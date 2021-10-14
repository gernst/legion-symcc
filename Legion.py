#!/usr/bin/python3

import argparse
import datetime
import functools
import itertools
import os
import random
import subprocess as sp
import sys
import z3

from math import sqrt, log, ceil, inf

RHO = 1
INPUTS = set()
VERSION = "testcomp2022"
BITS = 64


def constraint_from_string(ast, decls):
    try:
        (constraint,) = z3.parse_smt2_string(ast, decls=decls)
        return constraint
    except:
        write_smt2_trace(ast, decls, "log", "error")
        raise ValueError("Z3 parser error", ast)


def trace_from_file(trace):
    with open(trace, "rt") as stream:
        nbytes = 0
        target = []
        decls = {}

        polarity = None
        site = None
        pending = []

        result = []

        ok = None
        last = None

        def flush():
            if pending:
                ast = "(assert " + " ".join(pending) + ")"
                assert ast

                # parse_smt2_* returns a list
                constraint = constraint_from_string(ast, decls)
                event = (site, target, polarity, constraint)
                result.append(event)

                pending.clear()

        for line in stream.readlines():
            line = line.strip()

            if not line:
                continue

            last = line
            assert ok is None

            if line.startswith("in  "):
                flush()

                k = int(line[4:])
                n = "stdin" + str(k)
                x = z3.BitVec(n, 8)
                assert k == nbytes
                nbytes = nbytes + 1

                decls[n] = x
                target.append(x)

            elif line.startswith("yes "):
                flush()
                polarity = True
                site = int(line[4:])

            elif line.startswith("no "):
                flush()
                polarity = False
                site = int(line[4:])

            elif line.startswith("exit"):
                flush()
                last = line
                ok = True

            elif line.startswith("abort"):
                flush()
                last = line
                ok = False

            elif line.startswith("timeout"):
                flush()
                last = line
                ok = False

            else:
                pending.append(line)

        flush()
        # assert ok is not None
        return (ok, last, result)


# higher is better
def uct(w, n, N):
    if not n:
        return inf
    else:
        exploit = w / n
        explore = RHO * sqrt(2 * log(N) / n)
        return exploit + explore


def naive(solver, target):
    assert target
    assert type(target) == list

    if len(target) == 1:
        target = target[0]
    else:
        target = z3.Concat(list(reversed(target)))

    n = target.size()

    delta = z3.BitVec("delta", n)
    result = z3.BitVec("result", n)
    solver.add(result == target)

    solver.minimize(delta)

    while True:
        # print('---------------------------')
        guess = z3.BitVecVal(random.getrandbits(n), n)

        solver.push()
        solver.add(result ^ delta == guess)

        for known in INPUTS:
            solver.add(result != known)

        if solver.check() != z3.sat:
            break

        model = solver.model()
        value = model[result].as_long()

        solver.pop()

        INPUTS.add(value)
        yield value


class Arm:
    def __init__(self, node):
        self.node = node

        self.reward = 0
        self.selected = 0

    def score(self, N):
        if self.node.is_explored:
            return -inf
        else:
            return uct(self.reward, self.selected, N)

    def descr(self, N):
        return "uct(%d, %d, %d)" % (self.reward, self.selected, N)


class Node:
    def __init__(self, target, path, constraints, parent=None):
        self.site = None

        self.target = target
        self.nbytes = len(target)

        self.path = path
        self.constraints = constraints
        self.depth = len(constraints)

        self.parent = parent
        self.yes = None
        self.no = None

        self.sampler = None

        self.is_phantom = True
        self.is_leaf = False

        # do not sample at this particular node
        self.is_exhausted = False
        # do not sample anywhere in the subtree
        self.is_explored = False

        # statistics collected for sampling in this node and subtree, respectively
        self.here = Arm(self)
        self.tree = Arm(self)

    def check_invariants(self):
        try:
            if self.parent:
                assert self.target

            if self.is_phantom:
                assert not self.site
                assert not self.is_leaf
                assert not self.yes
                assert not self.no
                # assert not self.is_exhausted
                # assert not self.is_explored
            elif self.is_leaf:
                assert not self.yes
                assert not self.no
                assert self.is_exhausted
                assert self.is_explored
            else:
                assert self.site
                assert self.yes
                assert self.no

                if self.is_explored:
                    # assert self.is_exhausted
                    assert self.yes.is_explored
                    assert self.no.is_explored

                self.yes.check_invariants()
                self.no.check_invariants()
        except AssertionError as e:
            print("!", self.path)
            raise e

    def propagate(self, reward, selected, here=True):
        if here:  # to this node
            self.here.reward += reward
            self.here.selected += selected

        self.tree.reward += reward
        self.tree.selected += selected

        if self.parent:
            self.parent.propagate(reward, selected, here=False)

    def exhaust(self, here=True):
        if here:
            self.is_exhausted = True

        if self.is_leaf:
            assert here
            self.is_explored = True
        elif self.is_phantom:
            assert here
            # self.is_explored = self.is_exhausted
        else:
            self.is_explored = self.yes.is_explored and self.no.is_explored

        if self.parent:
            self.parent.exhaust(here=False)  # don't know yet

    def insert(self, trace, is_complete, path="", constraints=[], index=0):
        was_phantom = self.is_phantom

        if index < len(trace):
            assert not self.is_leaf

            site, target, polarity, phi = trace[index]

            yes = phi
            no = z3.Not(phi)
            bit = "1" if polarity else "0"
            phi = yes if polarity else no

            if was_phantom:
                self.is_phantom = False
                self.site = site
                self.yes = Node(target, path + "1", constraints + [yes], parent=self)
                self.no = Node(target, path + "0", constraints + [no], parent=self)

            child = self.yes if polarity else self.no
            base, leaf = child.insert(
                trace, is_complete, path + bit, constraints + [phi], index + 1
            )
        elif not is_complete:
            # print("integrated partial trace")
            # base, leaf = None, self.parent
            return None, self
        else:
            self.is_leaf = True
            self.is_phantom = False
            # print("exhaust leaf at", self.path)
            self.exhaust()
            base, leaf = None, self

        if was_phantom:
            return self, leaf
        else:
            return base, leaf

    def sample(self):
        assert not self.is_exhausted

        if not self.target:
            # print("exhaust non-target at", self.path)
            self.exhaust()
            return b""  # no bytes to sample

        if self.sampler is None:
            solver = z3.Optimize()
            solver.add(self.constraints)
            # print("target     ", self.target, " with size", self.nbytes)
            # print("constraints", self.constraints)
            self.sampler = naive(solver, self.target)

        try:
            sample = next(self.sampler)
            inputs = int_to_bytes(sample, self.nbytes)
            return inputs

        except StopIteration:
            # print("exhaust via sampler", self.path)
            self.exhaust()
            return None

    def select(self):
        assert not self.is_leaf
        assert not self.is_explored

        if self.is_phantom:
            if self.is_exhausted:
                print("unexpected exhausted node in select")
                self.pp()
                print()
            # assert not self.is_exhausted
            return self
        else:
            options = []
            if not self.is_exhausted:
                options.append(self.here)
            if not self.yes.is_explored:
                options.append(self.yes.tree)
            if not self.no.is_explored:
                options.append(self.no.tree)

            N = self.tree.selected

            # print([arm.descr(N) for arm in options])
            # print([arm.score(N) for arm in options])

            candidates = []
            best = -inf

            for arm in options:
                cur = arm.score(N)

                if cur == best:
                    candidates.append(arm)
                    continue
                if cur > best:
                    best = cur
                    candidates = [arm]

            arm = random.choice(candidates)
            node = arm.node

            if node is self:
                assert not self.is_exhausted
                return node
            else:
                return node.select()

    def pp_legend(self):
        print("      local      subtree")
        print("   win  try     win  try    path")
        self.pp()

    def pp(self):
        if not self.parent:
            key = "*"
        elif self.is_leaf:
            key = "$"
        elif self.is_explored:
            key = "E"
        elif self.is_exhausted:
            key = "e"
        elif self.is_phantom:
            key = "?"
        else:
            key = "."

        if True or key != ".":
            a = "%4d %4d" % (self.here.reward, self.here.selected)
            b = "%4d %4d" % (self.tree.reward, self.tree.selected)
            print(key, a, "  ", b, "  ", self.path)

        if key != "E":
            if self.no:
                self.no.pp()
            if self.yes:
                self.yes.pp()


def int_to_bytes(value, nbytes):
    return value.to_bytes(nbytes, "little")


def random_bit():
    return random.getrandbits(1)


def random_bytes(nbytes):
    return int_to_bytes(random.getrandbits(nbytes * 8), nbytes)


def sha256sum(file):
    res = sp.run(["sha256sum", file], stdout=sp.PIPE)
    out = res.stdout.decode("utf-8")
    return out[:64]


def write_metadata(file, path):
    sp.run(["mkdir", "-p", path])

    path = path + "/metadata.xml"
    print(path)
    print()

    with open(path, "wt") as stream:
        stream.write('<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n')
        stream.write(
            '<!DOCTYPE test-metadata PUBLIC "+//IDN sosy-lab.org//DTD test-format test-metadata 1.1//EN" "https://sosy-lab.org/test-format/test-metadata-1.1.dtd">\n'
        )
        stream.write("<test-metadata>\n")
        stream.write("  <sourcecodelang>C</sourcecodelang>\n")
        stream.write("  <producer>Legion/SymCC</producer>\n")
        stream.write("  <specification>COVER EDGES(@DECISIONEDGE)</specification>\n")
        stream.write("  <programfile>{}</programfile>\n".format(file))
        stream.write("  <programhash>{}</programhash>\n".format(sha256sum(file)))
        stream.write("  <entryfunction>main</entryfunction>\n")
        stream.write("  <architecture>{}bit</architecture>\n".format(BITS))
        stream.write(
            "  <creationtime>{}</creationtime>\n".format(datetime.datetime.now())
        )
        stream.write("</test-metadata>\n")


def write_testcase(lines, path, identifier):
    sp.run(["mkdir", "-p", path])
    path = path + "/" + str(identifier) + ".xml"

    with open(path, "wt") as stream:
        stream.write('<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n')
        stream.write(
            '<!DOCTYPE testcase PUBLIC "+//IDN sosy-lab.org//DTD test-format testcase 1.1//EN" "https://sosy-lab.org/test-format/testcase-1.1.dtd">\n'
        )
        stream.write("<testcase>\n")
        for line in lines:
            stream.write(line.decode("utf-8"))
        stream.write("</testcase>\n")


def write_smt2_trace(ast, decls, path, identifier):
    decls = [x.decl().sexpr() for _, x in decls.items()]
    decls = sorted(decls)

    sp.run(["mkdir", "-p", path])
    path = path + "/" + str(identifier) + ".smt2"

    with open(path, "wt") as stream:
        for decl in decls:
            stream.write(decl)
            stream.write("\n")

        stream.write(ast)


def execute_with_input(binary, data, path, identifier, timeout=None, maxlen=None):
    sp.run(["mkdir", "-p", path])
    path = path + "/" + str(identifier) + ".txt"
    os.remove(path)

    env = {}
    env["SYMCC_LOG_FILE"] = path

    if timeout:
        env["SYMCC_TIMEOUT"] = str(timeout)
    if maxlen:
        env["SYMCC_MAX_TRACE_LENGTH"] = str(maxlen)

    process = sp.Popen(
        binary, stdin=sp.PIPE, stdout=sp.PIPE, stderr=sp.PIPE, close_fds=True, env=env
    )

    # write initial input
    process.stdin.write(data)

    # provide random input as further necessary
    while process.poll() is None:
        try:
            process.stdin.write(random_bytes(64))
        except BrokenPipeError:
            break

    process.wait()

    # force reading entire output
    code = process.returncode
    outs = list(process.stdout.readlines())
    errs = list(process.stderr.readlines())

    return code, outs, errs, path


def run(*args):
    print(*args)
    sp.run(args, stderr=sp.STDOUT)
     
def compile_symcc(libs, source, binary):
    cmd = ["clang"]

    cmd.extend([
        "-Xclang", "-load", "-Xclang", libs + "/libSymbolize.so"
    ])

    if BITS == 32:
        rpath = libs + "32"
        cmd.append("-m32")
    elif BITS == 64:
        rpath = libs
        cmd.append("-m64")
    else:
        rpath = libs

    cmd.extend([
        source, "__VERIFIER.c", "-o", binary
    ])

    cmd.append("-lstdc++")
    cmd.append("-lSymRuntime")
    cmd.append("-L" + rpath)
    cmd.append("-Wl,-rpath," + rpath)
    
    run(*cmd)
    print()


def zip_files(file, paths):
    run("zip", "-r", file, *paths)
    print()

if __name__ == "__main__":
    if len(sys.argv) == 2 and (sys.argv[1] == "-v" or sys.argv[1] == "--version"):
        print(VERSION)
        sys.exit(0)

    parser = argparse.ArgumentParser(description="Legion")
    # parser.add_argument("-c", "--compile",
    #                     action='store_true',
    #                     help='compile binary (requires modified symcc on path, otherwise assume it has been compiled before)')
    parser.add_argument("file", help="C source file")
    parser.add_argument("-s", "--seed", type=int, default=0, help="random seed")
    parser.add_argument("-q", "--quiet", action="store_true", help="less output")
    parser.add_argument("-V", "--verbose", action="store_true", help="more output")
    parser.add_argument("-z", "--zip", action="store_true", help="zip test suite")
    parser.add_argument(
        "-64",
        dest="m64",
        action="store_true",
        help="compile with -m64 (override platform default)",
    )
    parser.add_argument(
        "-32",
        dest="m32",
        action="store_true",
        help="compile with -m32 (override platform default)",
    )
    parser.add_argument(
        "-i",
        "--iterations",
        type=int,
        default=10,
        help="number of iterations (samples to generate)",
    )
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        default=1,
        help="binary execution timeout (default 1)",
    )
    parser.add_argument(
        "-m",
        "--maxlen",
        type=int,
        default=100,
        help="maximum trace length (default: 100)",
    )
    parser.add_argument(
        "-L",
        dest="library",
        default="lib",
        help="location of SymCC compiler and runtime libraries",
    )
    parser.add_argument(
        "-T",
        "--testcov",
        action="store_true",
        help="run testcov (implies -z)",
    )
    args = parser.parse_args()

    random.seed(args.seed)

    source = args.file
    is_c = source[-2:] == ".c" or source[-2:] == ".i"

    if args.m32:
        BITS = 32
    elif args.m64:
        BITS = 64

    if is_c:
        binary = source[:-2]
        compile_symcc(args.library, source, binary)
    else:
        binary = source
        source = binary + ".c"

    # z3_check_sparse_models()

    stem = os.path.basename(binary)
    root = Node([], "", [])

    write_metadata(source, "tests/" + stem)

    # try:
    for i in range(1, args.iterations + 1):
        try:
            # root.pp()
            root.check_invariants()

            if root.is_explored:
                print("explored")
                break

            node = root.select()
            # node.selected += 1

            if node.is_exhausted:
                print("e", node.path.ljust(32))
                continue

            prefix = node.sample()

            if prefix is None:
                node.propagate(0, 1)
                print("e", node.path.ljust(32))
                continue
            else:
                print("?", node.path.ljust(32), "input: " + prefix.hex())
                if args.verbose:
                    print("  target     ",  node.target)
                    print("  constraints", node.constraints)

            code, outs, errs, path = execute_with_input(
                binary, prefix, "traces", "trace", args.timeout, args.maxlen
            )

            if errs:
                print("stderr:")
                for line in errs:
                    print(line.decode("utf-8"))
            if code != 0:
                print("code: ", code)

            try:
                ok, last, trace = trace_from_file(path)
            except Exception as e:
                node.propagate(0, 1)
                print("invalid trace", e)
                continue

            if not ok:
                # node.propagate(0, 1)
                print("partial trace: ", last)
                # continue

            if not trace:
                # testcov wants an empty test case
                write_testcase(b"", "tests/" + stem, i)
                print("deterministic")
                break

            bits = ["1" if bit else "0" for (_, _, bit, _) in trace]
            print("<", "".join(bits))

            added, leaf = root.insert(trace, ok)
            _, _, path, _ = zip(*trace)

            if added:
                node.propagate(1, 1)
            else:
                node.propagate(0, 1)

            if added:
                write_testcase(outs, "tests/" + stem, i)
                print("+", leaf.path)
            elif not leaf.path.startswith(node.path):
                print("!", leaf.path)  # missed a prefix
                # for a precise sampler, this means that we have a bogus node here
                # that should be regarded as an unreachable leaf
                node.is_leaf = True
                node.is_phantom = False
                node.exhaust()
                # raise Exception("failed to preserve prefix (naive sampler is precise)")
        except Exception as e:
            print()
            if not args.quiet:
                print("current tree")
                root.pp_legend()
            raise e

    print("done")
    print()
    # except:
    #     print("error")

    if not args.quiet:
        print("final tree")
        root.pp_legend()
        print()

    if args.testcov or args.zip:
        suite = "tests/" + stem + ".zip"
        zip_files(suite, ["tests/" + stem])
        print()

        cmd = ["testcov"]

        if args.m32:
            cmd.append("-32")
        else:
            cmd.append("-64")

        cmd.extend(
            [
                "--no-isolation",
                "--no-plots",
                "--timelimit-per-run", "3",
                "--test-suite",
                suite,
                source,
            ]
        )

        if args.testcov:
            run(*cmd)
        else:
            print(*cmd)
