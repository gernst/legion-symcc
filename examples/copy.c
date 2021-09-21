extern int __VERIFIER_nondet_char(void);

int main() {
    char x = __VERIFIER_nondet_char();
    char y = __VERIFIER_nondet_char();

    if(x > 0 && y > 0)
        while(x < y) x++;

    return 0;
}

