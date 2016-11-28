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

int main(int argc, char * argv[]) {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_set_precision (ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , -3, 3);
    opensmt_expr exp1 = opensmt_mk_abs(ctx, x);
    opensmt_expr exp2 = opensmt_mk_cos(ctx, x);
    opensmt_expr exp3 = opensmt_mk_div(ctx, exp1, exp2);
    opensmt_expr exp4 = opensmt_mk_sin(ctx, x);
    opensmt_expr eq   = opensmt_mk_eq(ctx, exp4, exp3);
    opensmt_push(ctx);
    opensmt_assert(ctx, eq);
    opensmt_result res = opensmt_check(ctx);
    printf("%s\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        double const x_lb = opensmt_get_lb(ctx, x);
        double const x_ub = opensmt_get_ub(ctx, x);
        printf("x = [%f, %f]\n", x_lb, x_ub);
    }
    opensmt_del_context(ctx);
    return 0;
}
