#include <stdio.h>

#include "opensmt/api/opensmt_c.h"

// Related Issue: https://github.com/dreal/dreal3/issues/143

int main(int argc, char * argv[]) {
/* julia> X = Var(Float64) # unbounded */
/* Ex{Float64}(Ptr{Void} @0x000000000704be00,Set{ASCIIString}({"x0"})) */
/* julia> add!(sin(X) > 0.0) */
/* Set{ASCIIString}({"x0"}) */
/* julia> is_satisfiable() */
/* false */
/* — */
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_expr x = opensmt_mk_unbounded_real_var(ctx, "x");
    opensmt_expr zero = opensmt_mk_num(ctx, 0.0);
    opensmt_expr gt = opensmt_mk_gt(ctx, opensmt_mk_sin(ctx, x), zero);
    opensmt_push(ctx);
    opensmt_assert(ctx, gt);
    opensmt_result res = opensmt_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );
    opensmt_del_context(ctx);
    return 0;
}
