COMPILER_H   = $(wildcard compiler/*.h)
COMPILER_CPP = $(wildcard compiler/*.cpp)

RUNTIME_H    = $(wildcard runtime/*.h)
RUNTIME_CPP  = $(wildcard runtime/*.cpp)

.PHONY: all

all: lib/libSymbolize.so lib/libSymRuntime.so lib32/libSymRuntime.so

lib/libSymRuntime.so: $(RUNTIME_CPP) $(RUNTIME_H)
	clang -std=c++17 -Wall $(RUNTIME_CPP) -Iruntime -fPIC -shared -o $@

lib32/libSymRuntime.so: $(RUNTIME_CPP) $(RUNTIME_H)
	clang -std=c++17 -Wall $(RUNTIME_CPP) -Iruntime -fPIC -shared -o $@ -m32

lib/libSymbolize.so: $(COMPILER_CPP) $(COMPILER_H)
	clang -std=c++17 -Wall $(COMPILER_CPP) -Wall -fPIC -D_GNU_SOURCE -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -Wl,-z,nodelete -shared -o $@
