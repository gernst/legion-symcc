# Legion/SymCC

Fresh implementation of the Legion algorithm on top of SyMCC.

## License

This repository contains a copy of SymCC source code in `runtime` and `compiler`, which is licensed under GPL,
with the addition of a new simple backend in `runtime/Runtime.{cpp,h}` by the authors of Legion/SymCC.

`Legion.py` is licensed under MIT.

## Usage

Compile SymCC compiler pass and runtime libraries

    make

Get help

    ./Legion.py -h

Simple example

    ./Legion.py examples/simple.c