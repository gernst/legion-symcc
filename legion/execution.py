import subprocess as sp
import threading
import z3
import random

from legion.helper import int_to_bytes

def run(*args):
    print(*args)
    return sp.run(args, stderr=sp.STDOUT)

def compile_symcc(libs, source, binary, bits, coverage=False):
    cmd = ["clang"]

    cmd.extend(["-Xclang", "-load", "-Xclang", libs + "/libSymbolize.so"])

    if bits == 32:
        rpath = libs + "32"
        cmd.append("-m32")
    elif bits == 64:
        rpath = libs
        cmd.append("-m64")
    else:
        rpath = libs

    if coverage:
        cmd.append("--coverage")
    cmd.append("-fbracket-depth=1024")

    cmd.extend([source, "Verifier.cpp", "-o", binary])

    cmd.append("-lstdc++")
    cmd.append("-lm")
    cmd.append("-lSymRuntime")
    cmd.append("-L" + rpath)
    cmd.append("-Wl,-rpath," + rpath)

    run(*cmd)
    print()

def random_bytes(nbytes):
    return int_to_bytes(random.getrandbits(nbytes * 8), nbytes)


def execute_with_input(binary, data, path, identifier, timeout=None, maxlen=None):
    sp.run(["mkdir", "-p", path])
    # os.remove(path)

    env = {}

    verifier_out = path + "/" + str(identifier) + ".out.txt"
    env["VERIFIER_STDOUT"] = verifier_out

    symcc_log = path + "/" + str(identifier) + ".txt"
    env["SYMCC_LOG_FILE"] = symcc_log

    if timeout:
        env["SYMCC_TIMEOUT"] = str(timeout)
        timeout += 1  # let the process have 1s of graceful shutdown
    if maxlen:
        env["SYMCC_MAX_TRACE_LENGTH"] = str(maxlen)

    process = sp.Popen(
        binary, stdin=sp.PIPE, stdout=sp.PIPE, stderr=sp.PIPE, close_fds=True, env=env
    )

    # write initial input
    process.stdin.write(data)

    def kill():
        print("killed")
        process.kill()

    timer = threading.Timer(timeout, kill)
    try:
        timer.start()
        # provide random input as further necessary
        while process.poll() is None:
            try:
                process.stdin.write(random_bytes(64))
            except BrokenPipeError:
                break
    finally:
        timer.cancel()

    process.wait()

    # force reading entire output
    code = process.returncode
    outs = list(process.stdout.readlines())
    errs = list(process.stderr.readlines())

    return code, outs, errs, symcc_log, verifier_out

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

            elif line.startswith("error"):
                flush()
                last = line
                is_complete = True  # used by benchmark tasks

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