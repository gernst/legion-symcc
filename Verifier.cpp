extern const char *status;

extern "C" {

    #include <stdio.h>
    #include <stdlib.h>
    #include <unistd.h>

    extern ssize_t read(int fd, void *buf, size_t count);

    void __assert_fail (const char *__assertion, const char *__file,
        unsigned int __line, const char *__function) {
        status = "error";
        exit(1);
    }

    static int initialized = 0;
    static FILE* output;

    static void __VERIFIER_initialize() {
        if(initialized) return;
        initialized = 1;

        const char *VERIFIER_STDOUT = getenv("VERIFIER_STDOUT");
        
        if(VERIFIER_STDOUT) {
            output = fopen(VERIFIER_STDOUT, "wt");
        } else {
            output = stdout;
        }
    }

    bool __VERIFIER_nondet_bool() {
        __VERIFIER_initialize();

        char x = 0;
        read(0, &x, sizeof(x));
        bool y = x >=0;
        fprintf(output, "  <input type=\"bool\">%d</input>\n", y);
        fflush(output);
        return y;
    }

    char __VERIFIER_nondet_char() {
        __VERIFIER_initialize();
        
        char x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"char\">%d</input>\n", x);
        fflush(output);
        return x;
    }

    char __VERIFIER_nondet_unsigned_char() {
        __VERIFIER_initialize();

        unsigned char x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"unsigned char\">%d</input>\n", x);
        fflush(output);
        return x;
    }

    unsigned char __VERIFIER_nondet_uchar() {
        __VERIFIER_initialize();
        
        unsigned char x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"unsigned char\">%u</input>\n", x);
        fflush(output);
        return x;
    }

    short __VERIFIER_nondet_short() {
        __VERIFIER_initialize();
        
        short x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"short\">%hi</input>\n", x);
        fflush(output);
        return x;
    }

    unsigned short __VERIFIER_nondet_ushort() {
        __VERIFIER_initialize();
        
        unsigned short x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"unsigned short\">%hu</input>\n", x);
        fflush(output);
        return x;
    }

    unsigned long __VERIFIER_nondet_unsigned_long() {
        __VERIFIER_initialize();
        
        unsigned long x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"unsigned long\">%lu</input>\n", x);
        fflush(output);
        return x;
    }

    long __VERIFIER_nondet_long() {
        __VERIFIER_initialize();
        
        long x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"long\">%li</input>\n", x);
        fflush(output);
        return x;
    }

    unsigned int __VERIFIER_nondet_uint() {
        __VERIFIER_initialize();
        
        unsigned int x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"unsigned int\">%u</input>\n", x);
        fflush(output);
        return x;
    }

    int __VERIFIER_nondet_int() {
        __VERIFIER_initialize();
        
        int x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"int\">%d</input>\n", x);
        fflush(output);
        return x;
    }

    unsigned __VERIFIER_nondet_unsigned() {
        __VERIFIER_initialize();
        
        unsigned x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"unsigned\">%d</input>\n", x);
        fflush(output);
        return x;
    }

    unsigned long __VERIFIER_nondet_ulong() {
        __VERIFIER_initialize();
        
        unsigned long x = 0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"unsigned long\">%lu</input>\n", x);
        fflush(output);
        return x;
    }

    float __VERIFIER_nondet_float() {
        __VERIFIER_initialize();
        
        float x = 0.0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"float\">%f</input>\n", x);
        fflush(output);
        return x;
    }

    double __VERIFIER_nondet_double() {
        __VERIFIER_initialize();
        
        double x = 0.0;
        read(0, &x, sizeof(x));
        fprintf(output, "  <input type=\"double\">%lf</input>\n", x);
        fflush(output);
        return x;
    }

}