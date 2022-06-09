import random
import subprocess as sp
import datetime
import os
import z3

BITS = 64

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

def constraint_from_string(ast, decls):
    try:
        return z3.parse_smt2_string(ast, decls=decls)
    except:
        # write_smt2_trace(ast, decls, "log", "error")
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

        constraints = []

        is_complete = None
        last = None

        def flush():
            if pending:
                # constraint = constraint_from_string(ast, decls)
                event = (site, target, polarity, len(constraints))
                result.append(event)

                ast = "(assert " + " ".join(pending) + ")"
                constraints.append(ast)

                pending.clear()

        for line in stream.readlines():
            line = line.strip()

            if not line:
                continue

            last = line
            assert is_complete is None

            if line.startswith("in  "):
                flush()

                k = int(line[4:])
                while nbytes < k:
                    n = "stdin" + str(nbytes)
                    x = z3.BitVec(n, 8)
                    decls[n] = x
                    target.append(x)
                    nbytes = nbytes + 1

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
                is_complete = True

            elif line.startswith("abort"):
                flush()
                last = line
                is_complete = True  # used by benchmark tasks

            elif line.startswith("segfault"):
                flush()
                last = line
                is_complete = False

            elif line.startswith("unsupported"):
                flush()
                last = line
                is_complete = False

            elif line.startswith("timeout"):
                flush()
                last = line
                is_complete = False

            else:
                pending.append(line)

        flush()

        # parse all the stuff
        ast = "\n".join(constraints)
        constraints = constraint_from_string(ast, decls)

        for i in range(len(result)):
            (site, target, polarity, index) = result[i]
            result[i] = (site, target, polarity, constraints[index])

        return (is_complete, last, result)