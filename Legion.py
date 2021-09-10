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


def target_from_file(trace_smt2):
    with open(trace_smt2, "rt") as stream:
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


def constraints_from_file(trace_smt2):
    solver = z3.Solver()
    solver.from_file(trace_smt2)
    return solver.assertions()


class Node:
    def __init__(self, constraint):
        pass


def int_to_bytes(value, nbytes):
    return value.to_bytes(nbytes, 'little')


def random_bytes(nbytes):
    return int_to_bytes(random.getrandbits(nbytes * 8), nbytes)


def write_testcase(lines, path, identifier):
    sp.run(['mkdir', '-p', path])
    test_xml = path + '/' + str(identifier) + '.xml'

    with open(test_xml, "wt") as stream:
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
    trace_smt2 = path + '/' + str(identifier) + '.smt2'

    env = { 'SYMCC_LOG_FILE': trace_smt2 }
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

    return code, outs, errs, trace_smt2


def compile_c(source_c, binary):
	sp.run(['symcc', source_c, '__VERIFIER.c', '-o', binary])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Legion')
    parser.add_argument("file",
                        help='C source file')
    args     = parser.parse_args()

    source_c = args.file
    trace_smt2 = 'trace.smt2'
    assert source_c[-2:] == '.c'
    binary   = "./" + source_c[:-2]

    compile_c(source_c, binary)

    code, outs, errs, trace = execute_with_input(binary, bytes(), 'traces', 1)
    write_testcase(outs, 'tests', 1)

    target = target_from_file(trace)
    print(target)

    constraints = constraints_from_file(trace)
    print(constraints)

    # solver  = z3.Optimize()
    # solver.from_file(args.file)

    # target  = target_from_file(args.file)
    # bits    = target.size()
    # sampler = bvsampler.bvsampler(solver, target)

    # results = list(itertools.islice(sampler, 100))
    # for result in results:
    #     print(type(result))
    #     print(result)
