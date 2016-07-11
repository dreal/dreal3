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

// Related Issue: https://github.com/dreal/dreal3/issues/210

void print_r(opensmt_result r){
    if(r==l_true)
        printf("sat\n");
    else if(r==l_false)
        printf("unsat\n");
    else
        printf("unknown\n");
}

int main() {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_set_verbosity(ctx, 1000);
    opensmt_expr a = opensmt_mk_bool_var(ctx, "a");
    opensmt_expr not_a = opensmt_mk_not(ctx, a);
    opensmt_expr b = opensmt_mk_bool_var(ctx, "b");
    opensmt_expr i1 = opensmt_mk_bool_var(ctx, "i1");
    opensmt_expr i2 = opensmt_mk_bool_var(ctx, "i2");
    opensmt_expr i3 = opensmt_mk_bool_var(ctx, "i3");

    opensmt_assert(ctx, opensmt_mk_imply(ctx, i1, a));//i1 -> a
    opensmt_assert(ctx, opensmt_mk_imply(ctx, i2, not_a));//i2 -> not a
    opensmt_assert(ctx, opensmt_mk_imply(ctx, i3, b)); //i3 -> b

    opensmt_push(ctx);
    opensmt_assert(ctx, i1);
    opensmt_assert(ctx, i2);
    opensmt_assert(ctx, i3);
    print_r(opensmt_check(ctx)); //a /\ not a /\ b   is unsat, result is okay
    opensmt_pop(ctx);
    opensmt_push(ctx);
    opensmt_assert(ctx, i1);
    opensmt_assert(ctx, i3);
    opensmt_assert(ctx, opensmt_mk_not(ctx,i2));
    print_r(opensmt_check(ctx));//a /\ b is sat, result is okay.
    opensmt_pop(ctx);
    opensmt_push(ctx);
    opensmt_assert(ctx, i1);
    opensmt_assert(ctx, i2);
    opensmt_assert(ctx, opensmt_mk_not(ctx,i3));
    print_r(opensmt_check(ctx));// a /\ not a  is unsat while the result is sat.
    opensmt_pop(ctx);
    opensmt_del_context(ctx);
    return 0;
}
