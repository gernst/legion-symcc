#!/usr/bin/python3

import os
import random
import sys
import signal

from math import sqrt, log, ceil, inf

from legion.helper import *
from legion.execution import *
from legion.tree import *

BFS = True
RHO = 1
VERSION = "testcomp2022"
BITS = 64


def zip_files(file, paths):
    run("zip", "-r", file, *paths)
    print()


def interrupt(number, frame):
    print("received SIGTERM")
    raise StopIteration()


if __name__ == "__main__":
    if len(sys.argv) == 2 and (sys.argv[1] == "-v" or sys.argv[1] == "--version"):
        print(VERSION)
        sys.exit(0)

    sys.setrecursionlimit(1000 * 1000)

    args = parseArguments()

    random.seed(args.seed)

    if args.rho:
        RHO = args.rho

    source = args.file
    is_c = source[-2:] == ".c" or source[-2:] == ".i"

    if args.m32:
        BITS = 32
    elif args.m64:
        BITS = 64

    if is_c:
        binary = source[:-2]
        compile_symcc(args.library, source, binary, BITS, args.coverage)
    else:
        binary = source
        source = binary + ".c"

    # z3_check_sparse_models()

    stem = os.path.basename(binary)
    root = Node([], "", [], [])

    write_metadata(source, "tests/" + stem, BITS)

    # try:
    i = 0

    empty_testcase_written = False
    ntestcases = 0

    signal.signal(signal.SIGTERM, interrupt)

    while True:
        i += 1

        if args.iterations and i >= args.iterations:
            print("max iterations")
            break

        try:
            # root.pp()

            if args.verbose:
                print("selecting")
            node = root.select(BFS, RHO)

            if args.verbose:
                print("sampling...")
            prefix = node.sample()

            if prefix is None:
                node.propagate(0, 1)
                if args.verbose:
                    print("e", node.path.ljust(32))
                continue
            else:
                print("?", node.path.ljust(32), "input: " + prefix.hex())

            if args.verbose:
                print("executing", binary)

            maxlen = None

            if args.maxlen:
                maxlen = args.maxlen

            if args.adaptive or not args.maxlen:
                if ntestcases < 100:
                    maxlen = 100
                elif ntestcases < 1000:
                    maxlen = 1000
                else:
                    maxlen = 10000

            if maxlen and args.maxlen and maxlen > args.maxlen:
                maxlen = args.maxlen

            code, outs, errs, symcc_log, verifier_out = execute_with_input(
                binary, prefix, "traces/" + stem, i, args.timeout, maxlen
            )

            if -31 <= code and code < 0:
                print("signal: ", signal.Signals(-code).name)
            elif code != 0:
                print("return code: ", code)
                #Hier soll reach_error() abgefangen werden
                if code == 1:
                    print("reach_error() detected.")
                    break

            if outs:
                if args.verbose:
                    print("stdout:")
                for line in outs:
                    print(line.decode("utf-8").strip())

            if errs:
                if args.verbose:
                    print("stderr:")
                for line in errs:
                    print(line.decode("utf-8").strip())

            try:
                if args.verbose:
                    print("parse trace", symcc_log)
                is_complete, last, trace = trace_from_file(symcc_log)
            except Exception as e:
                node.propagate(0, 1)
                if args.verbose:
                    print("invalid trace", e)
                continue

            if not is_complete:
                # node.propagate(0, 1)
                if args.verbose:
                    print("partial trace: ", last)
                # continue

            if not trace:
                if not empty_testcase_written:
                    # testcov wants an empty test case
                    if args.verbose:
                        print("write empty testcase")
                    write_testcase(None, "tests/" + stem, i)
                    empty_testcase_written = True
                if args.verbose:
                    print("deterministic")
                continue

            bits = ["1" if bit else "0" for (_, _, bit, _) in trace]
            if args.verbose:
                print("<", "".join(bits))

            added, leaf = root.insert(trace, is_complete)
            _, _, path, _ = zip(*trace)

            if added:
                node.propagate(1, 1)
            else:
                node.propagate(0, 1)

            if added:
                if not args.error or code == 1:
                    if args.verbose:
                        print("write testcase", verifier_out)
                    write_testcase(verifier_out, "tests/" + stem, i)
                    ntestcases += 1
                    if code == 1 and args.error:
                        print("+", leaf.path)
                        break
            elif not leaf.path.startswith(node.path):
                print("!", leaf.path)  # missed a prefix
                # raise Exception("failed to preserve prefix (naive sampler is precise)")
        except KeyboardInterrupt:
            print("keyboard interrupt")
            break
        except StopIteration:
            print("signal interrupt")
            break
        except Exception as e:
            if args.verbose:
                print()
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

    print("tests: " + str(ntestcases))
    print()

    if args.coverage:
        stem = os.path.basename(binary)
        gcda = stem + ".gcda"
        gcov(gcda)
        try_remove(gcda)
        try_remove("__VERIFIER.gcda")

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
                "--timelimit-per-run",
                "3",
                "--test-suite",
                suite,
                source,
            ]
        )

        if args.testcov:
            run(*cmd)
        else:
            print(*cmd)