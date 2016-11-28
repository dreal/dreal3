#include <assert.h>

#include "opensmt/api/opensmt_c.h"

// Related PR : https://github.com/dreal/DReal.jl/pull/23
int main(int argc, char * argv[]) {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);

    opensmt_expr a = opensmt_mk_bool_var( ctx, "a" );
    opensmt_expr b = opensmt_mk_bool_var( ctx, "b" );
    opensmt_expr c = opensmt_mk_bool_var( ctx, "c" );

     /*  # Creating integer variables */
    opensmt_expr x = opensmt_mk_int_var( ctx, "x" , -100, 100);
    opensmt_expr y = opensmt_mk_int_var( ctx, "y" , -100, 100);
    opensmt_expr z = opensmt_mk_int_var( ctx, "z" , -100, 100);
    /*  # Creating inequality */
    opensmt_expr minus = opensmt_mk_minus( ctx, x, y );
    opensmt_expr zero = opensmt_mk_num_from_string( ctx, "0" );
    opensmt_expr leq = opensmt_mk_leq( ctx, minus, zero );

    /*  # Creating inequality 2 */
    opensmt_expr minus2 = opensmt_mk_minus( ctx, y, z );
    opensmt_expr leq2 = opensmt_mk_leq( ctx, minus2, zero );

    /*  # Creating inequality 3 */
    opensmt_expr minus3 = opensmt_mk_minus( ctx, z, x );
    opensmt_expr mone = opensmt_mk_num_from_string( ctx, "-1" );
    opensmt_expr leq3 = opensmt_mk_leq( ctx, minus3, mone );

    /*  # Creating inequality 4 */
    opensmt_expr minus4 = opensmt_mk_minus( ctx, z, x );
    opensmt_expr leq4 = opensmt_mk_leq( ctx, minus4, zero );

    /*  # Asserting first inequality */
    opensmt_assert( ctx, leq );                 /* ASSERT (e1) */
    opensmt_push( ctx );                        /* PUSH */

    /* # Checking for consistency */
    opensmt_result res = opensmt_check( ctx );  /* CHECK */
    assert(res == l_true);

    // # Asserting second inequality
    opensmt_assert( ctx, leq2 );               /* ASSERT (e2) */
    opensmt_push( ctx );                       /* PUSH */

    // # Checking for consistency
    res = opensmt_check( ctx );                /* CHECK */
    assert(res == l_true);

    // # Asserting third inequality
    opensmt_push( ctx );                       /* PUSH */
    opensmt_assert( ctx, leq3 );               /* ASSERT (e3)*/

    // # Checking for consistency - it is UNSAT
    res = opensmt_check( ctx );                /* CHECK */
    assert(res == l_false);

    /*  # Backtracking one step - so the state is SAT again */
    opensmt_pop( ctx );                        /* POP */

    /* # Asserting fourth inequality */
    opensmt_assert( ctx, leq4 );               /* ASSERT (e4) */

    /*  # Checking for consistency */
    res = opensmt_check( ctx );                /* CHECK */
    assert(res == l_true);
    res = opensmt_check( ctx );                /* CHECK */
    assert(res == l_true);

    opensmt_del_context(ctx);
    return 0;
}
