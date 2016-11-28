#include <stdio.h>

#include "opensmt/api/opensmt_c.h"

// Test Memory Leaks
int main(int argc, char * argv[]) {
    int i = 0;
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_set_precision (ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var(ctx, "a" , 0.0, 1.0);
    opensmt_push(ctx);

    // opensmt_expr point1 = opensmt_mk_num(ctx, 0.1);
    opensmt_expr point1 = opensmt_mk_num_from_string(ctx, "0.1");
    //opensmt_expr point9 = opensmt_mk_num(ctx, 0.9);
    opensmt_expr point9 = opensmt_mk_num_from_string(ctx, "0.8");
    opensmt_expr leq = opensmt_mk_leq(ctx, x, point1);
    opensmt_expr geq = opensmt_mk_leq(ctx, x, point9);

    opensmt_expr list[] = {geq, leq};
    opensmt_expr orr = opensmt_mk_or(ctx, list, 2);
    opensmt_assert(ctx, orr);
    opensmt_result res = opensmt_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );
    fprintf( stderr, "1\n");
    opensmt_pop(ctx);
    fprintf( stderr, "2\n");
    opensmt_push(ctx);
    fprintf( stderr, "3\n");

    opensmt_expr b3 = opensmt_mk_not(ctx, orr);
    fprintf( stderr, "4\n");
    opensmt_assert(ctx, b3);
    fprintf( stderr, "5\n");
    opensmt_result res2 = opensmt_check( ctx );
    fprintf( stderr, "6\n");
    printf( "%s\n\n", res2 == l_false ? "unsat" : "sat" );
    fprintf( stderr, "7\n");
    opensmt_pop(ctx);
    fprintf( stderr, "8\n");
    opensmt_del_context(ctx);
    return 0;
}
