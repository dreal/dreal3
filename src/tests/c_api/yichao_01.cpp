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
#include <vector>
#include <string>
#include "opensmt/api/opensmt_c.h"

using std::string;
using std::vector;

string int2string(int num) {
    char chr[256];
    snprintf(chr, sizeof(chr), "%i", num);
    return string(chr);
}

int main() {
    // Creating context
    fprintf(stderr, "Creating context\n");
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_set_verbosity(ctx, 99);

    // Creating variables
    fprintf(stderr, "Creating some real variables\n");

    vector<opensmt_expr> x;
    for (unsigned i = 0; i <= 75; i++) {
        x.push_back(opensmt_mk_unbounded_real_var(ctx, ("x_"+int2string(i)).c_str()));
    }
    // Creating constraints

    opensmt_expr e1 = opensmt_mk_eq(ctx, x[0], opensmt_mk_num_from_string(ctx, "0"));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e1);
    opensmt_assert(ctx, e1);
    fprintf(stderr, "\n");

    opensmt_expr e2 = opensmt_mk_eq(ctx, x[8], opensmt_mk_plus_2(ctx, x[1], x[2]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e2);
    opensmt_assert(ctx, e2);
    fprintf(stderr, "\n");

    opensmt_expr e3 = opensmt_mk_eq(ctx, x[11], opensmt_mk_div(ctx, x[3], x[4]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e3);
    opensmt_assert(ctx, e3);
    fprintf(stderr, "\n");

    opensmt_expr e4 = opensmt_mk_gt(ctx, x[8], x[11]);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e4);
    opensmt_assert(ctx, e4);
    fprintf(stderr, "\n");

    opensmt_expr e5 = opensmt_mk_eq(ctx, x[14],  opensmt_mk_pow(ctx, x[1], opensmt_mk_num(ctx, 0.5)));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e5);
    opensmt_assert(ctx, e5);
    fprintf(stderr, "\n");

    opensmt_expr e6 = opensmt_mk_eq(ctx, x[17],  opensmt_mk_div(ctx, x[3], x[2]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e6);
    opensmt_assert(ctx, e6);
    fprintf(stderr, "\n");

    opensmt_expr e7 = opensmt_mk_gt(ctx, x[14], x[17]);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e7);
    opensmt_assert(ctx, e7);
    fprintf(stderr, "\n");

    opensmt_expr e8 = opensmt_mk_eq(ctx, x[21],  opensmt_mk_times_2(ctx, x[1], x[2]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e8);
    opensmt_assert(ctx, e8);
    fprintf(stderr, "\n");

    opensmt_expr e9 = opensmt_mk_eq(ctx, x[22],  opensmt_mk_log(ctx, x[21]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e9);
    opensmt_assert(ctx, e9);
    fprintf(stderr, "\n");

    opensmt_expr e10 = opensmt_mk_eq(ctx, x[25],  opensmt_mk_plus_2(ctx, x[4], x[5]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e10);
    opensmt_assert(ctx, e10);
    fprintf(stderr, "\n");

    opensmt_expr e11 = opensmt_mk_eq(ctx, x[27],  opensmt_mk_plus_2(ctx, x[3], x[25]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e11);
    opensmt_assert(ctx, e11);
    fprintf(stderr, "\n");

    opensmt_expr e12 = opensmt_mk_eq(ctx, x[28],  opensmt_mk_log(ctx, x[27]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e12);
    opensmt_assert(ctx, e12);
    fprintf(stderr, "\n");

    opensmt_expr e13 = opensmt_mk_gt(ctx, x[22], x[28]);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e13);
    opensmt_assert(ctx, e13);
    fprintf(stderr, "\n");

    opensmt_expr e14 = opensmt_mk_eq(ctx, x[31],  opensmt_mk_times_2(ctx, x[3], opensmt_mk_num(ctx, 2)));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e14);
    opensmt_assert(ctx, e14);
    fprintf(stderr, "\n");

    opensmt_expr e15 = opensmt_mk_eq(ctx, x[33],  opensmt_mk_times_2(ctx, x[4], opensmt_mk_num(ctx, 3)));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e15);
    opensmt_assert(ctx, e15);
    fprintf(stderr, "\n");

    opensmt_expr e16 = opensmt_mk_eq(ctx, x[34],  opensmt_mk_plus_2(ctx, x[31], x[33]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e16);
    opensmt_assert(ctx, e16);
    fprintf(stderr, "\n");

    opensmt_expr e17 = opensmt_mk_eq(ctx, x[36],  opensmt_mk_times_2(ctx, x[1], opensmt_mk_num(ctx, 7)));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e17);
    opensmt_assert(ctx, e17);
    fprintf(stderr, "\n");

    opensmt_expr e18 = opensmt_mk_eq(ctx, x[37],  opensmt_mk_plus_2(ctx, x[36], x[34]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e18);
    opensmt_assert(ctx, e18);
    fprintf(stderr, "\n");

    opensmt_expr e19 = opensmt_mk_eq(ctx, x[39],  opensmt_mk_pow(ctx, x[2], opensmt_mk_num(ctx, 6)));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e19);
    opensmt_assert(ctx, e19);
    fprintf(stderr, "\n");

    opensmt_expr e20 = opensmt_mk_gt(ctx, x[39], x[37]);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e20);
    opensmt_assert(ctx, e20);
    fprintf(stderr, "\n");

    opensmt_expr e21 = opensmt_mk_eq(ctx, x[43],  opensmt_mk_plus_2(ctx, x[3], x[4]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e21);
    opensmt_assert(ctx, e21);
    fprintf(stderr, "\n");

    opensmt_expr e22 = opensmt_mk_eq(ctx, x[46],  opensmt_mk_plus_2(ctx, x[1], x[2]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e22);
    opensmt_assert(ctx, e22);
    fprintf(stderr, "\n");

    opensmt_expr e23 = opensmt_mk_gt(ctx, x[43], x[46]);
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e23);
    opensmt_assert(ctx, e23);
    fprintf(stderr, "\n");

    opensmt_expr e24 = opensmt_mk_eq(ctx, x[51],  opensmt_mk_div(ctx, x[1], x[2]));
    fprintf(stderr, "  Expression created: ");
    opensmt_print_expr(e24);
    opensmt_assert(ctx, e24);
    fprintf(stderr, "\n");


    // Checking for consistency
    fprintf(stderr, "\nChecking for consistency: ");
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "dreal_result is %s\n\n", res == l_false ? "unsat" : "sat");

    // Deleting context
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);

    return 0;
}
