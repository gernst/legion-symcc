#!/usr/bin/python3

import z3
import re
import argparse
import functools
import itertools
import random
import bvsampler
import subprocess as sp

MAX_LEVEL   = 1
DECLARE_FUN = re.compile('\(declare-fun (stdin[0-9]+) \(\) \(_ BitVec ([0-9]+)\)\)')


def target_from_file(trace):
    with open(trace, "rt") as stream:
        consts = []
        for line in stream.readlines():
            match = DECLARE_FUN.match(line)
            if match:
                name = str(match[1])
                bits = int(match[2])
                var  = z3.BitVec(name, bits)
                consts.append(var)

    if consts:
        # assemble input vector
        # z3.Concat is n-ary but requires at least two arguments m(
        return functools.reduce(lambda a, b: z3.Concat(a, b), consts)
    else:
        # the program is deterministic, we are done
        return None


def constraints_from_file(trace):
    solver = z3.Solver()
    solver.from_file(trace)
    return solver.assertions()


def trace_from_file(trace):
    with open(trace, "rt") as stream:
        nbytes   = 0
        target   = None
        decls    = {}

        polarity = None
        pending  = []

        result   = []

        def flush():
            if polarity is not None:
                ast = "(assert " + " ".join(pending) + ")"
                assert(ast)

                constraint, = z3.parse_smt2_string(ast, decls = decls)
                if polarity is False:
                    constraint = z3.Not(constraint)

                event = (target, constraint)
                result.append(event)

                pending.clear()

        for line in stream.readlines():
            line = line.strip()

            if line.startswith('in  '):
                flush()

                k = int(line[4:])
                n = "stdin" + str(k)
                x = z3.BitVec(n, 8)
                assert(k == nbytes)
                nbytes = nbytes + 1

                decls[n] = x

                if target is None:
                    target = x
                else:
                    target = z3.Concat(target, x)

            elif line.startswith('yes '):
                flush()
                polarity = True
                pending.append(line[4:])

            elif line.startswith('no '):
                flush()
                polarity = False
                pending.append(line[4:])

            else:
                pending.append(line)

        flush()
        return result


class Node:
    def __init__(self, trace):
        self.children    = {}
        self.constraints = []
        self.target      = None
        self.sampler     = None

        for _, constraint in trace:
            self.constraints.append(constraint)

    def insert(self, index, trace):
        if index == len(trace):
            return None # leaf node, no new subtree
        else:
            phi = trace[index]
            if phi in self.children:
                child = self.children[phi]
                return child.insert(index + 1, trace)
            else:
                child = Node(trace[:index])
                self.children[phi] = child
                child.insert(index + 1, trace)
                return child # return root of new subtree

    def sample(self):
        if not self.target:
            return b'' # no bytes to sample

        if not self.sampler:
            solver = z3.Optimize()
            self.sampler = bvsampler.bvsampler(solver, target)

        sample = self.sampler.next()
        return int_to_bytes(sample)

    def select(self):
        if not self.children():
            return self
        elif random_bit():
            return self
        else:
            child = random.choice(self.children)
            return child.select()


def insert(root, trace):
    child = root.insert(0, trace)
    print("found new path")
    return child


def int_to_bytes(value, nbytes):
    return value.to_bytes(nbytes, 'little')


def random_bit():
    return random.getrandbits(1)

def random_bytes(nbytes):
    return int_to_bytes(random.getrandbits(nbytes * 8), nbytes)


def write_testcase(lines, path, identifier):
    sp.run(['mkdir', '-p', path])
    test = path + '/' + str(identifier) + '.xml'

    with open(test, "wt") as stream:
        stream.write(
            '<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n')
        stream.write(
            '<!DOCTYPE testcase PUBLIC "+//IDN sosy-lab.org//DTD test-format testcase 1.1//EN" "https://sosy-lab.org/test-format/testcase-1.1.dtd">\n')
        stream.write('<testcase>\n')
        for line in lines:
            stream.write(line.decode('utf-8'))
        stream.write('</testcase>\n')


def execute_with_input(binary, data, path, identifier):
    sp.run(['mkdir', '-p', path])
    trace = path + '/' + str(identifier) + '.smt2'

    env = { 'SYMCC_LOG_FILE': trace }
    process = sp.Popen(binary, stdin=sp.PIPE, stdout=sp.PIPE, stderr=sp.PIPE, close_fds=True, env=env)

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

    return code, outs, errs, trace


def compile_c(source_c, binary):
	sp.run(['symcc', source_c, '__VERIFIER.c', '-o', binary])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Legion')
    parser.add_argument("file",
                        help='C source file')
    args     = parser.parse_args()

    source_c = args.file

    assert source_c[-2:] == '.c'
    binary   = "./" + source_c[:-2]

    compile_c(source_c, binary)

    code, outs, errs, log = execute_with_input(binary, bytes(), 'traces', 1)
    write_testcase(outs, 'tests', 1)

    trace = trace_from_file(log)
    for foo in trace:
        print(foo)

    root = Node([])
    insert(root, trace)

    # target = target_from_file(trace)
    # print(target)

    # constraints = constraints_from_file(trace)
    # print(constraints)

    # solver  = z3.Optimize()
    # solver.from_file(args.file)

    # target  = target_from_file(args.file)
    # bits    = target.size()
    # sampler = bvsampler.bvsampler(solver, target)

    # results = list(itertools.islice(sampler, 100))
    # for result in results:
    #     print(type(result))
    #     print(result)
