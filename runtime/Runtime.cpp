// This file is part of Legion/SymCC.
//
// SymCC is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// SymCC is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// SymCC. If not, see <https://www.gnu.org/licenses/>.

#include <Runtime.h>

#include <cstdarg>
#include <vector>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <atomic>
#include <cassert>

#include <unistd.h>
#include <signal.h>

#include "Config.h"
#include "GarbageCollection.h"
#include "LibcWrappers.h"
#include "Shadow.h"

#define CONST(fun, bits)       new Expr(fun, bits, nullptr)

#define EXPR(fun, bits, ...)   new Expr(fun, bits, __VA_ARGS__, nullptr)

class Extract {
    public:
        size_t first_bit, last_bit;
        Extract(size_t _first_bit, size_t _last_bit)
            : first_bit(_first_bit), last_bit(_last_bit)
        {

        }
};

class Expr {
    public:
        std::string fun;
        uint8_t bits;
        std::vector<Expr*> args;
        Extract *extract;

        Expr(std::string _fun, size_t _bits, ...)
            : fun(_fun), bits(_bits), args(), extract(nullptr)
        {
            va_list ap;
            va_start(ap, _bits);

            Expr *arg;
            while((arg = va_arg(ap, Expr*))) {
                args.push_back(arg);
            }
            va_end(ap);
        }
};

std::ostream& operator<<(std::ostream& out, const Expr& e) {
    if(e.args.empty()) {
        out << e.fun;
    } else {
        out << "(" << e.fun;
        for(Expr *a: e.args) {
            out << " ";
            out << *a;
        }
        out << ")";
    }

    return out;
}

std::string decimal(uint64_t value) {
    return std::to_string(value);
}

std::string hexadecimal(uint64_t value, uint8_t bits) {
    assert(bits % 8 == 0);
    std::stringstream res;
    res << "#x" << std::setfill('0') << std::setw(bits / 4) << std::setbase(16) << value;
    return res.str();
}

std::string hexadecimal(uint64_t high, uint64_t low, uint8_t bits) {
    assert(bits % 8 == 0);
    std::stringstream res;
    res << "#x";
    res << std::setfill('0') << std::setw(bits / 4) << std::setbase(16) << high;
    res << std::setfill('0') << std::setw(bits / 4) << std::setbase(16) << low;
    return res.str();
}

std::string variable(std::string prefix, int index) {
    return prefix + std::to_string(index);
}

namespace {
    std::atomic_flag initialized = ATOMIC_FLAG_INIT;

    std::ostream *out;
    std::vector<SymExpr> input;

    Expr g_null_pointer(hexadecimal(0, 8 * sizeof(void *)), 8 * sizeof(void *), nullptr);
    Expr g_true("true", 0, nullptr);
    Expr g_false("false", 0, nullptr);
    Expr g_zero("0", 0, nullptr);
    Expr g_bit0("#b0", 1, nullptr);

    Expr g_rm("roundNearestTiesToEven", 0, nullptr);
    Expr g_rm_zero("roundTowardZero", 0, nullptr);

    const char *status = "exit";

    size_t traceLength;
}

void hard_shutdown() {
    fflush(stdout);
    close(0);
    close(1);
    close(2);
    // raise(SIGKILL);
    exit(0);
}

void _sym_finalize(void) {
    *out << std::endl; // clear any partial output
    *out << status << std::endl;
    // hard_shutdown();
}

void _sym_abort(int code) {
    status = "abort";
    exit(0);
}

void _sym_segfault(int code) {
    status = "segfault";
    exit(0);
}

void _sym_timeout(int) {
    status = "timeout";
    exit(0);
}

void _sym_unsupported() {
    status = "unsupported";
    exit(0);
}

void _sym_initialize(void) {
    if (initialized.test_and_set())
        return;

    loadConfig();
    initLibcWrappers();

    if (!g_config.logFile.empty()) {
        out = new std::ofstream(g_config.logFile);
    } else {
        out = &std::cout;
    }

    if(g_config.executionTimeout > 0) {
        signal(SIGALRM, _sym_timeout);
        alarm(g_config.executionTimeout);
    }

    signal(SIGABRT, _sym_abort);
    signal(SIGSEGV, _sym_segfault);
    signal(SIGBUS, _sym_segfault);

    atexit(_sym_finalize);
}

Expr * _sym_build_integer(uint64_t value, uint8_t bits) {
    auto name = hexadecimal(value, bits);
    return CONST(name, bits);
}

Expr * _sym_build_integer128(uint64_t high, uint64_t low) {
    auto name = hexadecimal(high, low, 128);
    return CONST(name, 128);
}

Expr * _sym_build_float(double value, int is_double) {
    // // std::cerr << "_sym_build_float(" << value << ", " << is_double << ")" << std::endl;
    if(is_double) {
        double d = (double) value;
        Expr *a = _sym_build_integer(*(reinterpret_cast<uint64_t*>(&d)), 64);
        return _sym_build_bits_to_float(a, 1);
    } else {
        float f = (float) value;
        Expr *a  =_sym_build_integer(*(reinterpret_cast<uint32_t*>(&f)), 32);
        return _sym_build_bits_to_float(a, 0);
    }
}

Expr * _sym_get_input_byte(size_t offset) {
    auto n = input.size();

    if (offset < n)
        return input[offset];

    auto name = variable("stdin", n);

    auto expr = CONST(name, 8);
    input.push_back(expr);

    return expr;
}

Expr * _sym_build_null_pointer(void) { return &g_null_pointer; }
Expr * _sym_build_true(void)         { return &g_true; }
Expr * _sym_build_false(void)        { return &g_false; }
Expr * _sym_build_bool(bool value)   { return value ? &g_true : &g_false; }

#define ZERO1(fun, x) 0
#define ZERO2(fun, x, y) 0

#define SAME1(fun, x)   ((x)->bits)

uint8_t SAME2(const char *fun, Expr *a, Expr *b) {
    if(a->bits != b->bits) {
        std::cerr << "cannot construct:" << std::endl;
        std::cerr << "(" << fun << " " << *a << " " << *b << ")" << std::endl;
        std::cerr << "with bits " << (int)a->bits << " and " << (int)b->bits << std::endl;
    }
    assert(a->bits == b->bits);
    return a->bits;
}

#define UNARY(name, fun, f) \
SymExpr _sym_build_##name(SymExpr a) \
{ return EXPR(fun, f(fun, a), a); }

#define BINARY(name, fun, f) \
SymExpr _sym_build_##name(SymExpr a, SymExpr b) \
{ return  EXPR(fun, f(fun, a, b), a, b); }

#define BINARY_RM(name, fun, f) \
SymExpr _sym_build_##name(SymExpr a, SymExpr b) \
{ return  EXPR(fun, f(fun, a, b), &g_rm, a, b); }

BINARY(equal, "=", ZERO2)

UNARY(bool_not, "not", ZERO1)
BINARY(bool_and, "and", ZERO2)
BINARY(bool_or, "or", ZERO2)
BINARY(bool_xor, "xor", ZERO2)

UNARY(neg, "bvneg", SAME1)
UNARY(not, "bvnot", SAME1)

BINARY(add, "bvadd", SAME2)
BINARY(sub, "bvsub", SAME2)
BINARY(mul, "bvmul", SAME2)

BINARY(and, "bvand", SAME2)
BINARY(or, "bvor", SAME2)
BINARY(xor, "bvxor", SAME2)

BINARY(unsigned_div, "bvudiv", SAME2)
BINARY(signed_div, "bvsdiv", SAME2)
BINARY(unsigned_rem, "bvurem", SAME2)
BINARY(signed_rem, "bvsrem", SAME2)
BINARY(shift_left, "bvshl", SAME2)
BINARY(logical_shift_right, "bvlshr", SAME2)
BINARY(arithmetic_shift_right, "bvashr", SAME2)

BINARY(signed_less_than, "bvslt", ZERO2)
BINARY(signed_less_equal, "bvsle", ZERO2)
BINARY(signed_greater_than, "bvsgt", ZERO2)
BINARY(signed_greater_equal, "bvsge", ZERO2)
BINARY(unsigned_less_than, "bvult", ZERO2)
BINARY(unsigned_less_equal, "bvule", ZERO2)
BINARY(unsigned_greater_than, "bvugt", ZERO2)
BINARY(unsigned_greater_equal, "bvuge", ZERO2)

BINARY(float_ordered_greater_than, "fp.gt", ZERO2)
BINARY(float_ordered_greater_equal, "fp.geq", ZERO2)
BINARY(float_ordered_less_than, "fp.lt", ZERO2)
BINARY(float_ordered_less_equal, "fp.leq", ZERO2)
BINARY(float_ordered_equal, "fp.eq", ZERO2)

UNARY(fp_abs,   "fp.abs",   SAME1)
UNARY(fp_isNaN, "fp.isNaN", ZERO1)

BINARY_RM(fp_add, "fp.add", SAME2)
BINARY_RM(fp_sub, "fp.sub", SAME2)
BINARY_RM(fp_mul, "fp.mul", SAME2)
BINARY_RM(fp_div, "fp.div", SAME2)
BINARY   (fp_rem, "fp.rem", SAME2)


Expr * _sym_build_float_ordered_not_equal(Expr * a, Expr * b) {
    return _sym_build_bool_not(_sym_build_float_ordered_equal(a, b));
}

Expr * _sym_build_float_ordered(Expr * a, Expr * b) {
    return _sym_build_bool_not(_sym_build_float_unordered(a, b));
}

Expr * _sym_build_not_equal(Expr * a, Expr * b) {
    return _sym_build_bool_not(_sym_build_equal(a, b));
}

Expr * _sym_build_float_unordered(Expr * a, Expr * b) {
    return _sym_build_bool_or(_sym_build_fp_isNaN(a), _sym_build_fp_isNaN(b));
}

#define UNORDERED(name) \
SymExpr _sym_build_float_unordered_##name(SymExpr a, SymExpr b) \
{ return _sym_build_bool_or(_sym_build_float_unordered(a, b), _sym_build_float_ordered_##name(a, b)); }

UNORDERED(greater_than)
UNORDERED(greater_equal)
UNORDERED(less_than)
UNORDERED(less_equal)
UNORDERED(equal)
UNORDERED(not_equal)

const char *to_fp(int is_double, int is_signed) {
    if(is_signed) {
        if(!is_double)
            return "(_ to_fp  8 24)";
        else
            return "(_ to_fp 11 53)";
    } else {
        if(!is_double)
            return "(_ to_fp_unsigned  8 24)";
        else
            return "(_ to_fp_unsigned 11 53)";
    }
}

Expr * _sym_build_int_to_float(Expr * value, int is_double, int is_signed) {
    // std::cerr << "_sym_build_int_to_float(" << *value << ", " << is_double << "," << is_signed << ")" << std::endl;
    auto *fun = to_fp(is_double, is_signed);
    return EXPR(fun, is_double ? 64 : 32, &g_rm, value);    
}


Expr * _sym_build_float_to_float(Expr * expr, int to_double) {
    // std::cerr << "_sym_build_float_to_float(" << *expr << ", " << to_double << ")" << std::endl;
    auto *fun = to_fp(to_double, 0);
    return EXPR(fun, to_double ? 64 : 32, &g_rm, expr);    
}

Expr * _sym_build_bits_to_float(Expr * expr, int to_double) {
    if (expr == nullptr)
        return nullptr;
    // std::cerr << "_sym_build_bits_to_float(" << *expr << ", " << to_double << ")" << std::endl;
    auto *fun = to_fp(to_double, 0);
    return EXPR(fun, to_double ? 64 : 32, &g_rm, expr);
}

Expr * _sym_build_float_to_bits(Expr * expr) {
    if (expr == nullptr)
        return nullptr;

    // std::cerr << "_sym_build_float_to_bits(" << expr << " = " << *expr << ")" << std::endl;
    return EXPR("fp.to_ieee_bv", expr->bits, expr);
}

Expr * _sym_build_float_to_signed_integer(Expr * expr, uint8_t bits) {
    // std::cerr << "_sym_build_float_to_signed_integer(" << *expr << ", " << bits << ")" << std::endl;
    std::string fun = "(_ to_sbv " + decimal(bits) + ")";
    return EXPR(fun, bits, &g_rm_zero, expr);
}

Expr * _sym_build_float_to_unsigned_integer(Expr * expr, uint8_t bits) {
    // std::cerr << "_sym_build_float_to_unsigned_integer(" << *expr << ", " << bits << ")" << std::endl;
    std::string fun = "(_ to_ubv " + decimal(bits) + ")";
    return EXPR(fun, bits, &g_rm_zero, expr);
}

Expr * _sym_build_bool_to_bits(Expr * expr, uint8_t bits) {
    Expr * one = _sym_build_integer(1, bits);
    Expr * zero = _sym_build_integer(0, bits);
    switch(expr->bits) {
        case 0:
            return EXPR("ite", bits, expr, one, zero);
        case 1:
            return EXPR("ite", bits, _sym_build_equal(expr, &g_bit0), zero, one);
        default:
            assert(expr->bits == 0 || expr->bits == 1);
            return nullptr;
    }
}

Expr * _sym_build_sext(Expr * expr, uint8_t bits) {
    if(0 == bits) {
        return expr;
    } else {
        std::string fun = "(_ sign_extend " + decimal(bits) + ")";
        return EXPR(fun, bits + expr->bits, expr);
    }
}

Expr * _sym_build_zext(Expr * expr, uint8_t bits) {
    if(0 == bits) {
        return expr;
    } else {
        std::string fun = "(_ zero_extend " + decimal(bits) + ")";
        return EXPR(fun, bits + expr->bits, expr);
    }
}

Expr * _sym_build_trunc(Expr * expr, uint8_t bits) {
    return _sym_extract_helper(expr, bits - 1, 0);
}

void _sym_push_path_constraint(Expr * constraint, int taken,
                               uintptr_t site_id) {
    if (constraint == nullptr)
        return;

    static size_t last_input_size = 0;

    auto n = input.size();
    if(n > last_input_size) {
        last_input_size = n;
        *out << "in  " << n << std::endl;
    }

    traceLength++;
    if(g_config.maximumTraceLength > 0 && traceLength > g_config.maximumTraceLength) {
        raise(SIGALRM);
    }

    if(constraint->bits == 1)
        constraint = _sym_build_bool(constraint);

    *out << (taken ? "yes " : "no  ") << site_id << std::endl;
    *out << *constraint << std::endl;
}

Expr * _sym_concat_helper(Expr * a, Expr * b) {
    if(a->extract && b->extract) {
        if(a->extract->last_bit == b->extract->first_bit + 1) {
            assert(a->args.size() == 1);
            assert(b->args.size() == 1);
            Expr * a0 = a->args[0];
            Expr * b0 = b->args[0];
            if(a0 == b0)
                return _sym_extract_helper(a0, a->extract->first_bit, b->extract->last_bit);
        }
    }

    return EXPR("concat", a->bits + b->bits, a, b);
}

Expr * _sym_extract_helper(Expr * expr, size_t first_bit, size_t last_bit) {
    size_t bits = first_bit - last_bit + 1;
    if(expr->bits == bits) {
        return expr;
    }
    
    if(expr->fun == "concat") {
        assert(expr->args.size() == 2);

        Expr * e0 = expr->args[0];
        Expr * e1 = expr->args[1];

        if(last_bit >= e1->bits)
            return _sym_extract_helper(e0, first_bit - e1->bits, last_bit - e1->bits);

        if(first_bit < e1->bits)
            return _sym_extract_helper(e1, first_bit, last_bit);
    }

    std::string fun = "(_ extract " + decimal(first_bit) + " " + decimal(last_bit) + ")";
    auto res = EXPR(fun, bits, expr);
    res->extract = new Extract(first_bit, last_bit);

    return res;
}

size_t _sym_bits_helper(Expr * expr) {
  return expr->bits;
}

bool _sym_feasible(Expr *  expr) {
    return true;
}

void _sym_notify_call(uintptr_t) {}
void _sym_notify_ret(uintptr_t) {}
void _sym_notify_basic_block(uintptr_t) {}
void _sym_collect_garbage() {}