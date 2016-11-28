/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

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

void print_sol(opensmt_context ctx, opensmt_expr x, opensmt_expr y) {
    double const x_lb = opensmt_get_lb(ctx, x);
    double const x_ub = opensmt_get_ub(ctx, x);
    fprintf(stderr, "x = [%f, %f]\n", x_lb, x_ub);
    double const y_lb = opensmt_get_lb(ctx, y);
    double const y_ub = opensmt_get_ub(ctx, y);
    fprintf(stderr, "y = [%f, %f]\n", y_lb, y_ub);
    return;
}

int main(int argc, char * argv[]) {
    // Creating context
    fprintf(stderr, "Creating context\n");
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);

    // Setting verbosity
    opensmt_set_verbosity(ctx, 4);

    // Creating integer variables
    fprintf(stderr, "Creating some integer variables\n");
    opensmt_expr x = opensmt_mk_int_var(ctx, "x" , -10, 10);
    opensmt_expr y = opensmt_mk_int_var(ctx, "y" , -10, 10);

    // numbers -- 2, 7, 10
    opensmt_expr num2  = opensmt_mk_num_from_string(ctx, "2");
    opensmt_expr num7  = opensmt_mk_num_from_string(ctx, "7");
    opensmt_expr num10 = opensmt_mk_num_from_string(ctx, "10");

    // t1 = x > 2
    opensmt_expr t1 = opensmt_mk_gt(ctx, x, num2);

    // t2 = y < 10
    opensmt_expr t2 = opensmt_mk_lt(ctx, y, num10);


    // t3 = 2 * y
    opensmt_expr subarray1[2] = {num2, y};
    opensmt_expr t3 = opensmt_mk_times(ctx, subarray1, 2);

    // t4 = x + t3 == 7
    opensmt_expr subarray2[2] = {x, t3};
    opensmt_expr t4 = opensmt_mk_eq(ctx, opensmt_mk_plus(ctx, subarray2, 2), num7);

    // t5 = t1 /\ t2 /\ t4
    opensmt_expr subarray3[3] = {t1, t2, t4};
    opensmt_expr t5 = opensmt_mk_and(ctx, subarray3, 3);

    opensmt_assert(ctx, t5);

    // Checking for consistency
    fprintf(stderr, "\nChecking for consistency: ");
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, x, y);
    }

    // Resetting context
    fprintf(stderr, "Resetting context\n");
    opensmt_reset(ctx);
    // Deleting context
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);

    return 0;
}
