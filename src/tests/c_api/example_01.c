/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>


dReal -- Copyright (C) 2013 - 2016, the dReal Team

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include <stdio.h>
#include "opensmt/api/opensmt_c.h"

void print_sol(opensmt_context ctx, opensmt_expr x, opensmt_expr y, opensmt_expr z) {
    double const x_lb = opensmt_get_lb(ctx, x);
    double const x_ub = opensmt_get_ub(ctx, x);
    fprintf(stderr, "x = [%f, %f]\n", x_lb, x_ub);
    double const y_lb = opensmt_get_lb(ctx, y);
    double const y_ub = opensmt_get_ub(ctx, y);
    fprintf(stderr, "y = [%f, %f]\n", y_lb, y_ub);
    double const z_lb = opensmt_get_lb(ctx, z);
    double const z_ub = opensmt_get_ub(ctx, z);
    fprintf(stderr, "z = [%f, %f]\n", z_lb, z_ub);
    return;
}

int main(int argc, char * argv[]) {
    // Creating context
    fprintf(stderr, "Creating context\n");
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);

    // Setting verbosity
    opensmt_set_verbosity(ctx, 4);

    // Creating boolean variables
    fprintf(stderr, "Creating some boolean variables\n");
    opensmt_expr a = opensmt_mk_bool_var(ctx, "a");
    opensmt_expr b = opensmt_mk_bool_var(ctx, "b");
    opensmt_expr c = opensmt_mk_bool_var(ctx, "c");
    // Creating integer variables
    fprintf(stderr, "Creating some integer variables\n");
    opensmt_expr x = opensmt_mk_int_var(ctx, "x" , -10, 10);
    opensmt_expr y = opensmt_mk_int_var(ctx, "y" , -10, 10);
    opensmt_expr z = opensmt_mk_int_var(ctx, "z" , -10, 10);
    // Creating inequality
    fprintf(stderr, "Creating x - y <= 0\n");

    fprintf(stderr, "  Creating x - y\n");
    opensmt_expr minus = opensmt_mk_minus(ctx, x, y);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(minus);
    fprintf(stderr, "\n");

    fprintf(stderr, "  Creating 0\n");
    opensmt_expr zero = opensmt_mk_num_from_string(ctx, "0");
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(zero);
    fprintf(stderr, "\n");

    fprintf(stderr, "  Creating x - y <= 0\n");
    opensmt_expr leq = opensmt_mk_leq(ctx, minus, zero);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(leq);
    fprintf(stderr, "\n");

    // Creating inequality 2
    fprintf(stderr, "Creating y - z <= 0\n");
    opensmt_expr minus2 = opensmt_mk_minus(ctx, y, z);
    opensmt_expr leq2 = opensmt_mk_leq(ctx, minus2, zero);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(leq2);
    fprintf(stderr, "\n");

    // Creating inequality 3
    fprintf(stderr, "Creating z - x <= -1\n");
    opensmt_expr minus3 = opensmt_mk_minus(ctx, z, x);
    opensmt_expr mone = opensmt_mk_num_from_string(ctx, "-1");
    opensmt_expr leq3 = opensmt_mk_leq(ctx, minus3, mone);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(leq3);
    fprintf(stderr, "\n");

    // Creating inequality 4
    fprintf(stderr, "Creating z - x <= 0\n");
    opensmt_expr minus4 = opensmt_mk_minus(ctx, z, x);
    opensmt_expr leq4 = opensmt_mk_leq(ctx, minus4, zero);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(leq4);
    fprintf(stderr, "\n");

    // Asserting first inequality
    fprintf(stderr, "Asserting ");
    opensmt_print_expr(leq);
    fprintf(stderr, "\n");
    opensmt_assert(ctx, leq);
    opensmt_push(ctx);

    // Checking for consistency
    fprintf(stderr, "\nChecking for consistency: ");
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, x, y, z);
    }

    // Asserting second inequality
    fprintf(stderr, "Asserting ");
    opensmt_print_expr(leq2);
    fprintf(stderr, "\n");
    opensmt_assert(ctx, leq2);
    opensmt_push(ctx);

    // Checking for consistency
    fprintf(stderr, "\nChecking for consistency: ");
    res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, x, y, z);
    }

    // Asserting third inequality
    fprintf(stderr, "Asserting ");
    opensmt_print_expr(leq3);
    fprintf(stderr, "\n");
    opensmt_assert(ctx, leq3);
    opensmt_push(ctx);

    // Checking for consistency - it is UNSAT
    fprintf(stderr, "\nChecking for consistency: ");
    res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, x, y, z);
    }

    // Backtracking one step - so the state is SAT again
    opensmt_pop(ctx);
    fprintf(stderr, "Backtracking one step\n\n");

    // Asserting fourth inequality
    fprintf(stderr, "Asserting ");
    opensmt_print_expr(leq4);
    fprintf(stderr, "\n");
    opensmt_assert(ctx, leq4);

    // Checking for consistency
    fprintf(stderr, "\nChecking for consistency: ");
    res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, x, y, z);
    }

    // Resetting context
    fprintf(stderr, "Resetting context\n");
    opensmt_reset(ctx);
    // Deleting context
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);

    return 0;
}
