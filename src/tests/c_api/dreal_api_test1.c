#include <stdio.h>

#include "api/dreal_c.h"

// Related Issue: https://github.com/dreal/dreal3/issues/143

int main(int argc, char * argv[]) {
/* julia> X = Var(Float64) # unbounded */
/* Ex{Float64}(Ptr{Void} @0x000000000704be00,Set{ASCIIString}({"x0"})) */
/* julia> add!(sin(X) > 0.0) */
/* Set{ASCIIString}({"x0"}) */
/* julia> is_satisfiable() */
/* false */
/* — */
    dreal_init();
    dreal_context ctx = dreal_mk_context(qf_nra);
    dreal_expr x = dreal_mk_unbounded_real_var(ctx, "x");
    dreal_expr zero = dreal_mk_num(ctx, 0.0);
    dreal_expr gt = dreal_mk_gt(ctx, dreal_mk_sin(ctx, x), zero);
    dreal_push(ctx);
    dreal_assert(ctx, gt);
    dreal_result res = dreal_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );
    dreal_del_context(ctx);
    return 0;
}
