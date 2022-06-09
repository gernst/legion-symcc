import subprocess as sp
import threading
from helper import random_bytes

BITS = 64

def run(*args):
    print(*args)
    return sp.run(args, stderr=sp.STDOUT)

def compile_symcc(libs, source, binary, coverage=False):
    cmd = ["clang"]

    cmd.extend(["-Xclang", "-load", "-Xclang", libs + "/libSymbolize.so"])

    if BITS == 32:
        rpath = libs + "32"
        cmd.append("-m32")
    elif BITS == 64:
        rpath = libs
        cmd.append("-m64")
    else:
        rpath = libs

    if coverage:
        cmd.append("--coverage")
    cmd.append("-fbracket-depth=1024")

    cmd.extend([source, "__VERIFIER.c", "-o", binary])

    cmd.append("-lstdc++")
    cmd.append("-lm")
    cmd.append("-lSymRuntime")
    cmd.append("-L" + rpath)
    cmd.append("-Wl,-rpath," + rpath)

    run(*cmd)
    print()


def zip_files(file, paths):
    run("zip", "-r", file, *paths)
    print()

def interrupt(number, frame):
    print("received SIGTERM")
    raise StopIteration()

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