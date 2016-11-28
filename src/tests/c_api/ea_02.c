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
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , 0, 8);
    // Creating Forall Real variables
    opensmt_expr y = opensmt_mk_forall_real_var(ctx, "y" , 0, 8.0);

    // constants
    opensmt_expr two = opensmt_mk_num(ctx, 2.0);
    opensmt_expr five = opensmt_mk_num(ctx, 5.0);
    opensmt_expr nine = opensmt_mk_num(ctx, 9.0);

    // circle1 := (x-2)^2 + (y-2)^2 <= 9
    opensmt_expr circle1 =
        opensmt_mk_leq(ctx,
                       opensmt_mk_plus_2(ctx,
                                         opensmt_mk_pow(ctx, opensmt_mk_minus(ctx, x, two), two),
                                         opensmt_mk_pow(ctx, opensmt_mk_minus(ctx, y, two), two)),
                       nine);
    // circle2 := (x-5)^2 + (y-5)^2 <= 9
    opensmt_expr circle2 =
        opensmt_mk_leq(ctx,
                       opensmt_mk_plus_2(ctx,
                                         opensmt_mk_pow(ctx, opensmt_mk_minus(ctx, x, five), two),
                                         opensmt_mk_pow(ctx, opensmt_mk_minus(ctx, y, five), two)),
                       nine);

    opensmt_expr vars[] = {y};
    opensmt_expr formula = opensmt_mk_forall(ctx, vars, 1,
                                             opensmt_mk_or_2(ctx, circle1, circle2));

    opensmt_assert(ctx, formula);
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, "x", x);
    }

    // Deleting context
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);

    return 0;
}
