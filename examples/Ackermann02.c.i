# 0 "examples/Ackermann02.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "examples/Ackermann02.c"
extern void abort(void);
void reach_error(){}
# 13 "examples/Ackermann02.c"
extern int __VERIFIER_nondet_int(void);

int ackermann(int m, int n) {
    if (m==0) {
        return n+1;
    }
    if (n==0) {
        return ackermann(m-1,1);
    }
    return ackermann(m-1,ackermann(m,n-1));
}


int main() {
    int m = __VERIFIER_nondet_int();
    if (m < 0 || m > 3) {


        return 0;
    }
    int n = __VERIFIER_nondet_int();
    if (n < 0 || n > 23) {



        return 0;
    }
    int result = ackermann(m,n);
    if (m < 2 || result >= 4) {
        return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}
