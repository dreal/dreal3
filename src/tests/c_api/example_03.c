#include "opensmt/api/opensmt_c.h"
#include <stdio.h>

int main( int argc, char * argv[] ) {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context( qf_nra );
    opensmt_set_precision (ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var( ctx, "x" , -3.141592, 3.141592);
    opensmt_expr y = opensmt_mk_real_var( ctx, "y" , -3.141592, 3.141592);

    opensmt_expr eq1 = opensmt_mk_eq( ctx, opensmt_mk_sin(ctx, x), opensmt_mk_cos(ctx, y));
    opensmt_push( ctx );
    opensmt_assert( ctx, eq1 );
    opensmt_result res = opensmt_check( ctx );
    printf( "%s\n", res == l_false ? "unsat" : "sat" );
    if (res == l_true) {
        double const x_lb = opensmt_get_lb(ctx, x);
        double const x_ub = opensmt_get_ub(ctx, x);
        printf("x = [%f, %f]\n", x_lb, x_ub);
        double const y_lb = opensmt_get_lb(ctx, y);
        double const y_ub = opensmt_get_ub(ctx, y);
        printf("y = [%f, %f]\n", y_lb, y_ub);
    }

    opensmt_expr eq2 = opensmt_mk_eq( ctx, opensmt_mk_cos(ctx, x), opensmt_mk_tan(ctx, y));
    opensmt_push( ctx );
    opensmt_assert( ctx, eq2 );
    res = opensmt_check( ctx );
    printf( "\n%s\n", res == l_false ? "unsat" : "sat" );
    if (res == l_true) {
        double const x_lb = opensmt_get_lb(ctx, x);
        double const x_ub = opensmt_get_ub(ctx, x);
        printf("x = [%f, %f]\n", x_lb, x_ub);
        double const y_lb = opensmt_get_lb(ctx, y);
        double const y_ub = opensmt_get_ub(ctx, y);
        printf("y = [%f, %f]\n", y_lb, y_ub);
    }

    opensmt_expr eq3 = opensmt_mk_eq( ctx, opensmt_mk_cos(ctx, x), opensmt_mk_cos(ctx, y));
    opensmt_push( ctx );
    opensmt_assert( ctx, eq3 );
    res = opensmt_check( ctx );
    printf( "\n%s\n", res == l_false ? "unsat" : "sat" );
    if (res == l_true) {
        double const x_lb = opensmt_get_lb(ctx, x);
        double const x_ub = opensmt_get_ub(ctx, x);
        printf("x = [%f, %f]\n", x_lb, x_ub);
        double const y_lb = opensmt_get_lb(ctx, y);
        double const y_ub = opensmt_get_ub(ctx, y);
        printf("y = [%f, %f]\n", y_lb, y_ub);
    }

    opensmt_pop( ctx );
    res = opensmt_check( ctx );
    printf( "\n%s:\n", res == l_false ? "unsat" : "sat" );
    if (res == l_true) {
        double const x_lb = opensmt_get_lb(ctx, x);
        double const x_ub = opensmt_get_ub(ctx, x);
        printf("x = [%f, %f]\n", x_lb, x_ub);
        double const y_lb = opensmt_get_lb(ctx, y);
        double const y_ub = opensmt_get_ub(ctx, y);
        printf("y = [%f, %f]\n", y_lb, y_ub);
    }
    opensmt_del_context( ctx );
    return 0;
}
