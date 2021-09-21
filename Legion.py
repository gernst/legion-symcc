#!/usr/bin/python3

import sys
import z3
import argparse
import functools
import itertools
import random
import bvsampler
import subprocess as sp


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

            else:
                pending.append(line)

        flush()
        return result


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
        self.is_exhausted = False  # do not sample at this particular node
        self.is_explored = False  # do not sample anywhere in the subtree
        self.selected = 0

    def insert(self, trace, path="", constraints=[], index=0):
        if index < len(trace):
            site, target, polarity, phi = trace[index]

            yes = phi
            no = z3.Not(phi)
            bit = "1" if polarity else "0"
            phi = yes if polarity else no

            if self.site:
                assert self.site == site
            else:
                self.site = site

            if self.is_phantom:
                self.yes = Node(target, path + "1", constraints + [yes], parent=self)
                self.no = Node(target, path + "0", constraints + [no], parent=self)

            child = self.yes if polarity else self.no
            base, leaf = child.insert(trace, path + bit, constraints + [phi], index + 1)
        else:
            self.is_leaf = True
            self.is_exhausted = True
            self.is_explored = True
            self.check_explored()
            base, leaf = None, self

        if self.is_phantom:
            self.is_phantom = False
            return self, leaf
        else:
            return base, leaf

    def sample(self):
        if not self.target:
            self.is_exhausted = True
            return b""  # no bytes to sample

        if self.sampler is None:
            solver = z3.Optimize()
            solver.add(self.constraints)
            # print("target     ", self.target, " with size", self.nbytes)
            # print("constraints", self.constraints)
            self.sampler = bvsampler.naive(solver, self.target)

        try:
            sample = next(self.sampler)
            inputs = int_to_bytes(sample, self.nbytes)
            return inputs
        except StopIteration:
            self.is_exhausted = True
            self.check_explored()
            return None

    def check_explored(self):
        self.is_explored = True
        if self.yes and not self.yes.is_explored:
            self.is_explored = False
        if self.no and not self.no.is_explored:
            self.is_explored = False

        if self.parent:
            self.parent.check_explored()

    def select(self):
        assert not self.is_explored

        options = []

        if not self.is_exhausted:
            options.append(self)
        if self.yes and not self.yes.is_explored:
            options.append(self.yes)
        if self.no and not self.no.is_explored:
            options.append(self.no)

        assert options

        node = random.choice(options)

        if node is self:
            return node
        else:
            return node.select()

    def print(self):
        if not self.parent:
            key = "*"
        elif self.is_leaf:
            key = "$"
        elif self.is_explored:
            key = "e"
        elif self.is_phantom:
            key = "?"
        else:
            key = "."

        selected = "%4d" % self.selected
        print(key, selected, self.path)

        if self.no:
            self.no.print()
        if self.yes:
            self.yes.print()


def int_to_bytes(value, nbytes):
    return value.to_bytes(nbytes, "little")


def random_bit():
    return random.getrandbits(1)


def random_bytes(nbytes):
    return int_to_bytes(random.getrandbits(nbytes * 8), nbytes)


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


def execute_with_input(binary, data, path, identifier):
    sp.run(["mkdir", "-p", path])
    path = path + "/" + str(identifier) + ".txt"

    env = {"SYMCC_LOG_FILE": path, "SYMCC_TIMEOUT": "1"}

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

    # force reading entire output
    code = process.returncode
    outs = list(process.stdout.readlines())
    errs = list(process.stderr.readlines())

    return code, outs, errs, path


def compile_c(source_c, binary):
    sp.run(["symcc", source_c, "__VERIFIER.c", "-o", binary])


def z3_check_sparse_models():
    solver = z3.Optimize()
    x = z3.BitVec("x", 8)
    y = z3.BitVec("y", 8)
    solver.add(x > 0)
    solver.add(y == y)
    assert solver.check() == z3.sat
    model = solver.model()
    names = [v.name() for v in model]
    assert "x" in names
    assert "y" not in names
    assert names == ["x"]
    del solver


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Legion")
    # parser.add_argument("-c", "--compile",
    #                     action='store_true',
    #                     help='compile binary (requires modified symcc on path, otherwise assume it has been compiled before)')
    parser.add_argument(
        "-i",
        "--iterations",
        type=int,
        default=10,
        help="number of iterations (samples to generate)",
    )
    parser.add_argument("-s", "--seed", type=int, default=0, help="random seed")
    parser.add_argument("file", help="C source file")
    args = parser.parse_args()

    random.seed(args.seed)

    if args.file[-2:] == ".c":
        binary = args.file[:-2]
        compile_c(args.file, binary)
    else:
        binary = args.file

    z3_check_sparse_models()

    root = Node([], "*", [], False)

    try:
        for i in range(1, args.iterations + 1):
            if root.is_explored:
                print("explored")
                break

            node = root.select()
            node.selected += 1

            prefix = node.sample()
            if prefix is None:
                continue

            print("?", node.path.ljust(32), prefix.hex())

            code, outs, errs, path = execute_with_input(
                binary, prefix, "traces", "trace"
            )

            trace = trace_from_file(path)
            added, leaf = root.insert(trace)
            _, _, path, _ = zip(*trace)

            if added:
                write_testcase(outs, "tests", i)
                print("+", leaf.path)
            elif not leaf.path.startswith(node.path):
                print("!", leaf.path)  # missed a prefix
                raise Exception("failed to preserve prefix (naive sampler is precise)")

        print("done")
        print()
    except:
        pass

    root.print()
