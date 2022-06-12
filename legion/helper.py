import random
import argparse
import subprocess as sp
import datetime
import os

def random_bit():
    return random.getrandbits(1)

def int_to_bytes(value, nbytes):
    return value.to_bytes(nbytes, "little")

def sha256sum(file):
    res = sp.run(["sha256sum", file], stdout=sp.PIPE)
    out = res.stdout.decode("utf-8")
    return out[:64]


def write_metadata(file, path, BITS):
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


def write_testcase(source, path, identifier):
    sp.run(["mkdir", "-p", path])
    path = path + "/" + str(identifier) + ".xml"

    with open(path, "wt") as stream:
        stream.write('<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n')
        stream.write(
            '<!DOCTYPE testcase PUBLIC "+//IDN sosy-lab.org//DTD test-format testcase 1.1//EN" "https://sosy-lab.org/test-format/testcase-1.1.dtd">\n'
        )
        stream.write("<testcase>\n")

        if source:
            with open(source, "rt") as dump:
                for line in dump.readlines():
                    stream.write(line)
        stream.write("</testcase>\n")

def gcov(gcda):
            cmd = ["llvm-cov", "gcov", "-b", "-n", gcda]
            proc = sp.Popen(cmd, stdout=sp.PIPE, stderr=sp.PIPE)
            for line in proc.stdout.readlines():
                line = line.decode("utf-8").rstrip()
                print(line)
                if line.startswith("Branches executed:"):
                    cov = float(line[18:21]) # two digits of accuracy
                    print("score: " + str(cov/100))


def try_remove(path):
            try:
                os.remove(path)
            except:
                pass

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

def parseArguments():
    parser = argparse.ArgumentParser(description="Legion")
    # parser.add_argument("-c", "--compile",
    #                     action='store_true',
    #                     help='compile binary (requires modified symcc on path, otherwise assume it has been compiled before)')
    parser.add_argument("file", help="C source file")
    parser.add_argument(
        "-c", "--coverage", action="store_true", help="generate coverage information"
    )
    parser.add_argument("-e", "--error", action="store_true", help="execute in cover-error mode")
    parser.add_argument("-r", "--rho", type=int, help="exploration factor (default: 1)")
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
        default=None,
        help="number of iterations (samples to generate)",
    )
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        default=3,
        help="binary execution timeout in seconds (default: 3)",
    )
    parser.add_argument(
        "-m",
        "--maxlen",
        type=int,
        default=None,
        help="maximum trace length (default: none)",
    )
    parser.add_argument(
        "-a",
        "--adaptive",
        type=bool,
        default=True,
        help="adaptively increase maximum trace length (default: true if -m is not given",
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
    return args