COMPILER_H   = $(wildcard compiler/*.h)
COMPILER_CPP = $(wildcard compiler/*.cpp)

RUNTIME_H    = $(wildcard runtime/*.h)
RUNTIME_CPP  = $(wildcard runtime/*.cpp)

.PHONY: all docker

all: lib/libSymbolize.so lib/libSymRuntime.so lib32/libSymRuntime.so

lib/libSymRuntime.so: $(RUNTIME_CPP) $(RUNTIME_H)
	clang -std=c++17 -Wall $(RUNTIME_CPP) -Iruntime -fPIC -shared -o $@

lib32/libSymRuntime.so: $(RUNTIME_CPP) $(RUNTIME_H)
	clang -std=c++17 -Wall $(RUNTIME_CPP) -Iruntime -fPIC -shared -o $@ -m32

lib/libSymbolize.so: $(COMPILER_CPP) $(COMPILER_H)
	clang -std=c++17 -Wall $(COMPILER_CPP) -Wall -fPIC -D_GNU_SOURCE -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -Wl,-z,nodelete -shared -o $@

lib:
	mkdir -p lib

lib32:
	mkdir -p lib32

README.html: README.md
	pandoc $< -s -o $@

docker: lib/libSymbolize.so lib/libSymRuntime.so lib32/libSymRuntime.so
	docker build . -t gidonernst/legion-symcc
	./docker-cp.sh

archive:
	cp -r legion.sh Legion.py __VERIFIER.c ubuntu2004 dist ../testcomp-archives-2022/2022/legion-symcc
	(cd ../testcomp-archives-2022/2022/; zip legion-symcc.zip legion-symcc/ -r)