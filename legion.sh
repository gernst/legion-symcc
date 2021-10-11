#!/bin/sh

export PYTHONPATH="dist/z3_solver-4.8.12.0-py3.9-linux-x86_64.egg"
exec python3 Legion.py $@