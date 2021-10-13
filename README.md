# Legion/SymCC

Fresh implementation of the Legion algorithm on top of SyMCC.

## License

This repository contains a copy of SymCC source code in `runtime` and `compiler`, which is licensed under GPL (see `LICENSE.symcc`),
with the addition of a new simple backend in `runtime/Runtime.{cpp,h}` by the authors of Legion/SymCC.

`Legion.py` is licensed under MIT (see `LICENSE`). Please add your name if you contribute.

## Usage

Compile SymCC compiler pass and runtime libraries

    make

Get help (note: a bunch of paths are hardcoded)

    ./Legion.py -h

Simple example

    ./Legion.py examples/simple.c

## Dependencies & Installation

- Python Z3: https://pypi.org/project/z3-solver/

  This can be installed via your distribution,
  or simply use the version provided in `dist`:

    export PYTHONPATH="dist/z3_solver-4.8.12.0-py3.9-linux-x86_64.egg"

  (see also `legion.sh`)

- LLVM/Clang + C++ libraries.
  On Ubuntu:

    apt-get install -y llvm-dev clang build-essential

  and for 32Bit mode (`-32`):

    apt-get install -y gcc-multilib g++-multilib

- Compiling on Ubuntu2004 via Docker (cf. `Dockerfile`):
  builds the docker image, compiles SymCC compiler plugin + runtime
  from the current git checkout, and copies the resulting libraries
  to `ubuntu2004/`:

    make docker

  Run `Legion.py -L ubuntu2004/lib` to make use of this build.