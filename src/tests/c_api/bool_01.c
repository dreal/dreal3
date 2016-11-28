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

#undef NDEBUG

int main() {
    // Creating context
    fprintf(stderr, "Creating context\n");
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);

    // Setting verbosity
    opensmt_set_verbosity(ctx, 4);

    // Creating boolean variables
    fprintf(stderr, "Creating some boolean variables\n");
    opensmt_expr x = opensmt_mk_bool_var(ctx, "x");
    opensmt_expr not_x = opensmt_mk_not(ctx, x);
    opensmt_expr y = opensmt_mk_bool_var(ctx, "y");
    opensmt_expr not_y = opensmt_mk_not(ctx, y);

    opensmt_expr arr[2] = {not_x, not_y};

    // (Not x || Not y)
    opensmt_expr t = opensmt_mk_or(ctx, arr, 2);

    opensmt_assert(ctx, t);

    // Checking for consistency
    fprintf(stderr, "\nChecking for consistency: ");
    opensmt_result res = opensmt_check(ctx);
    fprintf(stderr, "%s\n\n", res == l_false ? "unsat" : "sat");
    if (res == l_true) {
        opensmt_result result_x = opensmt_get_bool(ctx, x);
        opensmt_result result_y = opensmt_get_bool(ctx, y);
        printf("x = %d, y = %d\n", result_x, result_y);
        if (result_x == 0) {
            return 1;
        }
        if (result_y == 0) {
            return 1;
        }
        if (result_x == 1 && result_y == 1) {
            return 1;
        }
    }
    // Deleting context
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);

    return 0;
}
