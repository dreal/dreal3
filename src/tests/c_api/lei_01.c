#include <stdio.h>

#include "opensmt/api/opensmt_c.h"

// Related Issue: https://github.com/dreal/dreal3/issues/149

int main() {
/* (assert(= x_0 0)) */
/* (assert(= x_18 (sin x_1))) */
/* (assert(= x_21 (cos x_2))) */
/* (assert(= x_22 (+ x_21 x_18))) */
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_set_verbosity(ctx, 10);

    opensmt_expr x_0  = opensmt_mk_unbounded_real_var(ctx, "x_0");
    opensmt_expr x_1  = opensmt_mk_unbounded_real_var(ctx, "x_1");
    opensmt_expr x_18 = opensmt_mk_unbounded_real_var(ctx, "x_18");
    opensmt_expr x_21 = opensmt_mk_unbounded_real_var(ctx, "x_21");
    opensmt_expr x_22 = opensmt_mk_unbounded_real_var(ctx, "x_22");
    opensmt_expr zero = opensmt_mk_num(ctx, 0.0);
    opensmt_expr assert_1 = opensmt_mk_eq(ctx,  x_0, zero);
    opensmt_expr assert_2 = opensmt_mk_eq(ctx, x_18, opensmt_mk_sin(ctx, x_1));
    opensmt_expr assert_3 = opensmt_mk_eq(ctx, x_21, opensmt_mk_cos(ctx, x_1));
    opensmt_expr assert_4 = opensmt_mk_eq(ctx, x_22, opensmt_mk_plus_2(ctx, x_21, x_18));
    opensmt_assert(ctx, assert_1);
    opensmt_assert(ctx, assert_2);
    opensmt_assert(ctx, assert_3);
    opensmt_assert(ctx, assert_4);
    opensmt_result res = opensmt_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );
    opensmt_del_context(ctx);
    return 0;
}
