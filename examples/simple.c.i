# 0 "examples/simple.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "examples/simple.c"
extern char __VERIFIER_nondet_char(void);

int main() {
    char x = __VERIFIER_nondet_char();

    if(x > 0) {
        return 0;
    } else {
        return 1;
    }
}
