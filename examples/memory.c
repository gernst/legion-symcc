extern unsigned char __VERIFIER_nondet_uchar();

int main() {
    int n = __VERIFIER_nondet_uchar();
    int a[n%8];
    int i;

    for(i=0; i<n; i++) {
        a[i] = 0;
    }

    return 0;
}