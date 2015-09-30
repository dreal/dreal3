/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

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


//
//    argmin          x^2 + x + 2
// x in [-10, 10]
//
// It will find a point nearby x* = -0.5, f(x*) = 1.75
//


void print_sol(opensmt_context ctx, const char * name, opensmt_expr e) {
    double const lb = opensmt_get_lb(ctx, e);
    double const ub = opensmt_get_ub(ctx, e);
    fprintf(stderr, "%s = [%f, %f]\n", name, lb, ub);
}

int main() {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_set_precision (ctx, 0.001);

    // Creating Exist Real variables
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , -10, 10);
    // Creating Forall Real variables
    opensmt_expr y = opensmt_mk_forall_real_var(ctx, "y" , -10, 10);

    opensmt_expr cost = opensmt_mk_unbounded_real_var(ctx, "cost");

    // constants
    opensmt_expr two = opensmt_mk_num(ctx, 2.0);

    // value1 = x^2 + x + 2
    opensmt_expr value1 =
        opensmt_mk_plus_3(ctx,
                          opensmt_mk_pow(ctx, x, two),
                          x,
                          two);

    // value2 = y^2 + y + 2
    opensmt_expr value2 =
        opensmt_mk_plus_3(ctx,
                          opensmt_mk_pow(ctx, y, two),
                          y,
                          two);

    // cost = x^2 + x + 2
    opensmt_expr ctr1 = opensmt_mk_eq(ctx, cost, value1);

    // x^2 + x + 2 < y^2 + y + 2
    opensmt_expr ctr2 = opensmt_mk_lt(ctx, cost, value2);
    opensmt_expr forall_ctr2 = opensmt_mk_forall(ctx, &y, 1, ctr2);

    opensmt_assert(ctx, ctr1);
    opensmt_assert(ctx, forall_ctr2);
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, "x", x);
        print_sol(ctx, "cost", cost);
    }

    // Deleting context
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);

    return 0;
}
