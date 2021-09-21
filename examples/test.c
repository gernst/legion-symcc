extern int __VERIFIER_nondet_char(void);

int main() {
    char x = __VERIFIER_nondet_char();
    char y = __VERIFIER_nondet_char();

    if(x > 0) {
        y = __VERIFIER_nondet_char();
        if(y > 64) {
            return 0;
        } else if(y > 92) {
            return 1;
        }
    } else {
        if(y > 64) {
            return 0;
        } else if(y > 92) {
            return 1;
        }
    }
}

