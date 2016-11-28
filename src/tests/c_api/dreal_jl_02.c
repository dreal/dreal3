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
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , 0.0, 1.0);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y" , 0.0, 1.0);
    opensmt_expr ite = opensmt_mk_ite(ctx, opensmt_mk_gt(ctx, x, opensmt_mk_num(ctx, 0.4)),
                                      opensmt_mk_num(ctx, 0.3),
                                      opensmt_mk_num(ctx, 0.4));
    opensmt_expr eq = opensmt_mk_eq(ctx, y, ite);
    opensmt_assert( ctx, eq);
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, x, y);
    }
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);
    return 0;
}
