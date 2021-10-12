
_Bool __VERIFIER_nondet_bool() {
    char x = 0;
    read_symbolized(0, &x, sizeof(x));
    _Bool y = x >=0;
    printf("  <input type=\"bool\">%d</input>\n", y);
    return y;
}

int main() {
    _Bool x = __VERIFIER_nondet_bool();

    if(x) {
        return 0;
    } else {
        return 1;
    }
}

