#include "opensmt/api/opensmt_c.h"
#include <stdio.h>

int main( int argc, char * argv[] ) {
    // Creating context
    printf( "Creating context\n" );
    opensmt_context ctx = opensmt_mk_context( qf_nra );

    // Setting verbosity
    opensmt_set_verbosity( ctx, 4 );

    // Creating boolean variables
    printf( "Creating some boolean variables\n" );
    opensmt_expr a = opensmt_mk_bool_var( ctx, "a" );
    opensmt_expr b = opensmt_mk_bool_var( ctx, "b" );
    opensmt_expr c = opensmt_mk_bool_var( ctx, "c" );
    // Creating integer variables
    printf( "Creating some integer variables\n" );
    opensmt_expr x = opensmt_mk_int_var( ctx, "x" , -100, 100);
    opensmt_expr y = opensmt_mk_int_var( ctx, "y" , -100, 100);
    opensmt_expr z = opensmt_mk_int_var( ctx, "z" , -100, 100);
    // Creating inequality
    printf( "Creating x - y <= 0\n" );

    printf( "  Creating x - y\n" );
    opensmt_expr minus = opensmt_mk_minus( ctx, x, y );
    printf( "  Expression created: " );
    opensmt_print_expr( minus );
    printf( "\n" );

    printf( "  Creating 0\n" );
    opensmt_expr zero = opensmt_mk_num_from_string( ctx, "0" );
    printf( "  Expression created: " );
    opensmt_print_expr( zero );
    printf( "\n" );

    printf( "  Creating x - y <= 0\n" );
    opensmt_expr leq = opensmt_mk_leq( ctx, minus, zero );
    printf( "  Expression created: " );
    opensmt_print_expr( leq );
    printf( "\n" );

    // Creating inequality 2
    printf( "Creating y - z <= 0\n" );
    opensmt_expr minus2 = opensmt_mk_minus( ctx, y, z );
    opensmt_expr leq2 = opensmt_mk_leq( ctx, minus2, zero );
    printf( "  Expression created: " );
    opensmt_print_expr( leq2 );
    printf( "\n" );

    // Creating inequality 3
    printf( "Creating z - x <= -1\n" );
    opensmt_expr minus3 = opensmt_mk_minus( ctx, z, x );
    opensmt_expr mone = opensmt_mk_num_from_string( ctx, "-1" );
    opensmt_expr leq3 = opensmt_mk_leq( ctx, minus3, mone );
    printf( "  Expression created: " );
    opensmt_print_expr( leq3 );
    printf( "\n" );

    // Creating inequality 4
    printf( "Creating z - x <= 0\n" );
    opensmt_expr minus4 = opensmt_mk_minus( ctx, z, x );
    opensmt_expr leq4 = opensmt_mk_leq( ctx, minus4, zero );
    printf( "  Expression created: " );
    opensmt_print_expr( leq4 );
    printf( "\n" );

    // Asserting first inequality
    printf( "Asserting ");
    opensmt_print_expr( leq );
    printf( "\n" );
    opensmt_assert( ctx, leq );
    opensmt_push( ctx );

    // Checking for consistency
    printf( "\nChecking for consistency: " );
    opensmt_result res = opensmt_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );

    // Asserting second inequality
    printf( "Asserting ");
    opensmt_print_expr( leq2 );
    printf( "\n" );
    opensmt_assert( ctx, leq2 );
    opensmt_push( ctx );

    // Checking for consistency
    printf( "\nChecking for consistency: " );
    res = opensmt_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );

    // Asserting third inequality
    printf( "Asserting ");
    opensmt_print_expr( leq3 );
    printf( "\n" );
    opensmt_assert( ctx, leq3 );
    opensmt_push( ctx );

    // Checking for consistency - it is UNSAT
    printf( "\nChecking for consistency: " );
    res = opensmt_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );

    // Backtracking one step - so the state is SAT again
    opensmt_pop( ctx );
    printf( "Backtracking one step\n\n" );

    // Asserting fourth inequality
    printf( "Asserting ");
    opensmt_print_expr( leq4 );
    printf( "\n" );
    opensmt_assert( ctx, leq4 );

    // Checking for consistency
    printf( "\nChecking for consistency: " );
    res = opensmt_check( ctx );
    printf( "%s\n\n", res == l_false ? "unsat" : "sat" );

    // Resetting context
    printf( "Resetting context\n" );
    opensmt_reset( ctx );
    // Deleting context
    printf( "Deleting context\n" );
    opensmt_del_context( ctx );

    return 0;
}
