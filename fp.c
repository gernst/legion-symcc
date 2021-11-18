#include <stdlib.h>

#include <z3.h>

int main() {
    
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");
    Z3_set_param_value(cfg, "timeout", "10000"); // milliseconds
    Z3_context context = Z3_mk_context_rc(cfg);
    Z3_del_config(cfg);
    
    Z3_ast rm = Z3_mk_fpa_round_nearest_ties_to_even(context);
    Z3_inc_ref(context, (Z3_ast)rm);

    // Z3_solver solver = Z3_mk_solver(context);
    Z3_sort sort = Z3_mk_fpa_sort_single(context);
    Z3_inc_ref(context, (Z3_ast)sort);

    Z3_ast a = Z3_mk_fpa_numeral_double(context, 0, sort);
    Z3_inc_ref(context, a);

    Z3_ast b = Z3_mk_fpa_numeral_double(context, 1, sort);
    Z3_inc_ref(context, b);

    Z3_ast c = Z3_mk_fpa_numeral_double(context, -1, sort);
    Z3_inc_ref(context, c);

    Z3_ast d = Z3_mk_fpa_numeral_double(context, -2342.323453245, sort);
    Z3_inc_ref(context, d);

    Z3_ast x = Z3_mk_const(context, Z3_mk_string_symbol(context, "x"), sort);
    Z3_inc_ref(context, x);

    Z3_ast y = Z3_mk_const(context, Z3_mk_string_symbol(context, "y"), sort);
    Z3_inc_ref(context, y);

    Z3_ast B = Z3_mk_fpa_to_ieee_bv(context, a);
    Z3_inc_ref(context, B);
    Z3_ast I = Z3_mk_fpa_to_sbv(context, Z3_mk_fpa_round_toward_zero(context), x, 32);
    Z3_inc_ref(context, I);
    Z3_ast U = Z3_mk_fpa_to_ubv(context, Z3_mk_fpa_round_toward_zero(context), x, 32);
    Z3_inc_ref(context, U);
    
    printf("float:  %s\n", Z3_sort_to_string(context, Z3_mk_fpa_sort_single(context)));
    printf("double: %s\n", Z3_sort_to_string(context, Z3_mk_fpa_sort_double(context)));
    printf("\n");

    printf("a: %s\n", Z3_ast_to_string(context, a));
    printf("b: %s\n", Z3_ast_to_string(context, b));
    printf("c: %s\n", Z3_ast_to_string(context, c));
    printf("d: %s\n", Z3_ast_to_string(context, d));
    printf("B: %s\n", Z3_ast_to_string(context, B));
    printf("I: %s\n", Z3_ast_to_string(context, I));
    printf("U: %s\n", Z3_ast_to_string(context, U));
    printf("\n");
    
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_to_fp_bv(context, U, sort)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_to_fp_signed(context, rm, U, sort)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_to_fp_unsigned(context, rm, U, sort)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_to_fp_float(context, rm, x, sort)));
    printf("\n");

    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_gt(context, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_lt(context, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_geq(context, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_leq(context, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_eq(context, x, y)));
    printf("\n");

    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_abs(context, x)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_add(context, rm, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_sub(context, rm, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_mul(context, rm, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_div(context, rm, x, y)));
    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_rem(context, x, y)));
    printf("\n");

    printf("%s\n", Z3_ast_to_string(context, Z3_mk_fpa_is_nan(context, x)));
    printf("\n");

    return 0;
}