extern char __VERIFIER_nondet_char(void);
extern int  __VERIFIER_nondet_int(void);

int main() {
    int *a = malloc(10);
    int i = __VERIFIER_nondet_int();
    printf("i = %d\n", i);
    a[i] = 0;
    return 0;
}
