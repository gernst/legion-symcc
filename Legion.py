#!/usr/bin/python3

import z3
import argparse
import functools
import itertools
import random
import bvsampler
import subprocess as sp

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
        site     = None
        pending  = []

        result   = []

        def flush():
            if pending:
                ast = "(assert " + " ".join(pending) + ")"
                assert(ast)

                # parse_smt2_* returns a list
                constraint, = z3.parse_smt2_string(ast, decls = decls)
                event       = (site, target, polarity, constraint)
                result.append(event)

                pending.clear()

        for line in stream.readlines():
            line = line.strip()
            if not line:
                continue

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
                    target = z3.Concat(x, target)

            elif line.startswith('yes '):
                flush()
                polarity = True
                site     = int(line[4:])

            elif line.startswith('no '):
                flush()
                polarity = False
                site     = int(line[4:])

            else:
                pending.append(line)

        flush()
        return result


class Node:
    def __init__(self, target, constraints, parent = None):
        self.site        = None
        self.target      = target
        self.nbytes      = target.size() // 8 if target is not None else 0
        self.constraints = constraints
        self.depth       = len(constraints)

        self.parent      = parent
        self.children    = {}
        
        self.sampler     = None

        self.phantom     = True
        self.exhausted   = False
        self.selected    = 0

    def insert(self, trace, constraints=[], index=0):
        if index < len(trace):
            site, target, polarity, phi = trace[index]

            yes = phi
            no  = z3.Not(phi)
            phi = yes if polarity else no

            if self.site:
                assert self.site == site
            else:
                self.site = site
            
            if not self.children:
                self.children[True]  = Node(target, constraints + [yes], parent=self)
                self.children[False] = Node(target, constraints + [no],  parent=self)
            
            child  = self.children[polarity]
            result = child.insert(trace, constraints + [phi], index + 1)
        else:
            result = None

        if self.phantom:
            self.phantom = False
            return self
        else:
            return result

    def sample(self):
        if self.target is None:
            return b'' # no bytes to sample

        if self.sampler is None:
            solver = z3.Optimize()
            solver.add(self.constraints)
            # print("constraints", self.constraints)
            # print("target     ", self.target, " with size", self.nbytes)
            self.sampler = bvsampler.bvsampler(solver, self.target)

        try:
            sample = next(self.sampler)
            inputs = int_to_bytes(sample, self.nbytes)
            print(inputs.hex())
            return inputs
        except StopIteration:
            self.exhausted = True
            return None

    def select(self):
        if not self.children:
            return self
        elif random_bit():
            return self
        else:
            child = random.choice(self.children)
            return child.select()


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
    parser.add_argument("-c", "--compile",
                        action='store_true',
                        help='force compile')
    parser.add_argument("file",
                        help='C source file')
    args     = parser.parse_args()

    source_c = args.file

    assert source_c[-2:] == '.c'
    binary   = "./" + source_c[:-2]

    if args.compile:
        compile_c(source_c, binary)

    root = Node(None, [])

    for i in range(1,11):
        # print("round", i)
        node   = root.select()
        node.selected += 1
        # print("depth", node.depth, " #selected ", node.selected, "select", node.site)
        
        prefix = node.sample()
        if prefix is None:
            continue
        
        code, outs, errs, log = execute_with_input(binary, prefix, 'traces', i)
        trace = trace_from_file(log)
        added = root.insert(trace)
        _, _, path, _ = zip(*trace)

        if added:
            write_testcase(outs, 'tests', i)
            print("new: ", path)
        else:
            print("old: ", path)
            pass

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
