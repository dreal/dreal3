#include <math.h>
#include <stdio.h>

#include "opensmt/api/opensmt_c.h"

// Test Memory Leaks
int main() {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x", -INFINITY, INFINITY);
    opensmt_expr zero = opensmt_mk_num(ctx, 0.0);
    opensmt_expr leq = opensmt_mk_leq(ctx, zero, x);
    opensmt_assert(ctx, leq);
    opensmt_result res = opensmt_check( ctx );
    if (res == l_true) {
        double const x_lb = opensmt_get_lb(ctx, x);
        double const x_ub = opensmt_get_ub(ctx, x);
        printf("sat: x = [%f, %f]\n", x_lb, x_ub);
    } else {
        printf("unsat\n");
    }
    opensmt_del_context(ctx);
    return 0;
}
