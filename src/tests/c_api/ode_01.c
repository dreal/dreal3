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

void print_sol(opensmt_context ctx, const char * name, opensmt_expr e) {
    double const lb = opensmt_get_lb(ctx, e);
    double const ub = opensmt_get_ub(ctx, e);
    fprintf(stderr, "%s = [%f, %f]\n", name, lb, ub);
}

int main() {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra_ode);
    opensmt_set_precision (ctx, 0.001);
    opensmt_set_verbosity(ctx, 10);

    // Creating Real variables
    opensmt_expr x = opensmt_mk_unbounded_real_var(ctx, "x");
    opensmt_expr P = opensmt_mk_unbounded_real_var(ctx, "P");
    opensmt_expr x_0 = opensmt_mk_real_var(ctx, "x_0", -100, 100);
    opensmt_expr P_0 = opensmt_mk_real_var(ctx, "P_0", 0.0, 1.0);
    opensmt_expr x_t = opensmt_mk_real_var(ctx, "x_t", -100, 100);
    opensmt_expr P_t = opensmt_mk_real_var(ctx, "P_t", 0.0, 1.0);
    opensmt_expr time_0 = opensmt_mk_real_var(ctx, "time_0", 0.0, 40.0);

    // =======================================================================
    // Define ODE (flow)
    // d/dt[x] = 1.0
    // d/dt[P] = 1.0 / ((2.0 * 3.14159265359) ^ 0.5) * exp (- (x ^ 2) / 2.0)
    opensmt_expr zero = opensmt_mk_num(ctx, 0.0);
    opensmt_expr half  = opensmt_mk_num(ctx, 0.5);
    opensmt_expr one = opensmt_mk_num(ctx, 1.0);
    opensmt_expr ten = opensmt_mk_num(ctx, 10.0);
    opensmt_expr neg_ten = opensmt_mk_num(ctx, -10.0);
    opensmt_expr two = opensmt_mk_num(ctx, 2.0);
    opensmt_expr pi  = opensmt_mk_num(ctx, 3.14159265359);
    opensmt_expr two_pi = opensmt_mk_times_2(ctx, two, pi);
    opensmt_expr p_rhs = opensmt_mk_times_2(ctx,
                                            // 1.0 / sqrt(2 * pi)
                                            opensmt_mk_div(ctx, one, opensmt_mk_sqrt(ctx, two_pi)),
                                            // exp (- x^2 / 2.0)
                                            opensmt_mk_exp(ctx, opensmt_mk_uminus(ctx,
                                                                                  opensmt_mk_div(ctx, opensmt_mk_pow(ctx, x, two), two))));

    opensmt_expr vars[2] = {x, P};
    opensmt_expr rhses[2] = {one, p_rhs};
    opensmt_define_ode(ctx, "flow_1", vars, rhses, 2);
    // =======================================================================

    opensmt_assert(ctx, opensmt_mk_eq(ctx, x_0, neg_ten));  // x_0 = -10.0
    opensmt_assert(ctx, opensmt_mk_eq(ctx, P_0, zero));     // P_0 = 0.0
    opensmt_assert(ctx, opensmt_mk_eq(ctx, x_t, ten));      // x_t = 10.0


    // =======================================================================
    // Add integral constraint
    // [x_t P_t] = integral_0^{time_0} [x_0 P_0] | flow_1

    opensmt_expr vars_t[2] = {x_t, P_t};
    opensmt_expr vars_0[2] = {x_0, P_0};
    opensmt_expr integral = opensmt_mk_integral(ctx, vars_t, zero, time_0, vars_0, 2, "flow_1");
    opensmt_assert(ctx, integral);
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        print_sol(ctx, "P_t", P_t);
    }
    // Deleting context
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);

    return 0;
}
