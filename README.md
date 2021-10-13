# Legion/SymCC

Fresh implementation of the Legion algorithm [1] on top of SyMCC.

1. Dongge Liu, Gidon Ernst, Toby Murray, Ben Rubinstein: Legion: Best-First Concolic Testing. ASE 2020,
   <https://doi.org/10.1145/3324884.3416629>

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

-   [Python Z3](https://pypi.org/project/z3-solver/)
    can be installed via your distribution,
    or simply use the version provided in `dist`:

        export PYTHONPATH="dist/z3_solver-4.8.12.0-py3.9-linux-x86_64.egg"

    (see also `legion.sh`)

- LLVM/Clang + C++ libraries.
    On Ubuntu:

        apt-get install -y llvm-dev clang build-essential

    and for 32 bit mode (`-32`):

        apt-get install -y gcc-multilib g++-multilib

- Compiling on Ubuntu 20.04 via Docker (cf. `Dockerfile`):
    builds the docker image, compiles SymCC compiler plugin + runtime
    from the current git checkout, and copies the resulting libraries
    to `ubuntu2004/`:

        make docker

    Run `Legion.py -L ubuntu2004/lib` to make use of this build (it will then use `ubuntu2004/lib32` for 32bit mode)

## Interpreting the Output

Here is an example output, split into two parts.

During exploration, each line represents one piece of information,
encoding choices of the algorithm, feedback from the execution,
and information about exploration.

Paths to nodes are encoded in terms of their branches (`0` means not taken, `1` means taken).

- `?`: sample at the path, the input prefix should be shown on the right
- `e`: sample at this path but no more choices locally (solver returned `unsat`), continue
- `<`: path returned by binary execution
- `+`: new path found and integrated into the tree
- `!`: path failed to preserve the prefix chosen (approximate sampler)

Example trace:

    ?                                  input:
    < 1
    + 1
    ? 0                                input: 00
    < 0
    + 0
    explored
    done

The final output will be a compressed tree, where each node is represented by one line:

- `*` means root node
- `$` means leaf node
- `e` means this node is exhausted (no further solutions for the path constraint up to here),
      but it is possible that some children can still be sampled
- `E` entire tree is fully explored
- `?` is a phantom node which has never been hit explicitly
      but we know it is there as the negation of another known node
- `.` regular internal node

The statistics show how often we have sampled at this node in particular ("local"),
and aggregated over the entire subtree.
The path of the node is shown on the right.

    final tree
        local      subtree
       win  try     win  try    path
    *    1    1       2    2
    $    1    1       1    1    0
    $    0    0       0    0    1
