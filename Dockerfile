FROM ubuntu:20.04

RUN apt-get update  -y
RUN apt-get install -y llvm-dev clang
RUN apt-get install -y build-essential
RUN apt-get install -y gcc-multilib g++-multilib

WORKDIR /root

COPY . /root

RUN make -B