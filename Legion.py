#!/usr/bin/python3

import z3
import argparse

class Sampler:
    def __init__(self, file):
        self.solver = z3.Optimize()
        self.solver.from_file(file)

        self.solver.check()
        model = self.solver.model()
        stdin = sorted(model, key=lambda x: x.name())
        print(stdin)

class Node:
    def __init__(self, constraint):
        pass

def execute(binary, stdin):
    process = sp.Popen(binary, stdin=sp.PIPE, stdout=sp.PIPE, close_fds=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Legion')
    parser.add_argument("file",
                        help='C source file')
    args    = parser.parse_args()
    sampler = Sampler(args.file)
