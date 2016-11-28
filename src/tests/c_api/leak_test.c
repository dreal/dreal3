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
#include <stdlib.h>
#include <time.h>
#include "opensmt/api/opensmt_c.h"

// Test Memory Leaks
int main(int argc, char * argv[]) {
    srand(time(NULL));
    int i = 0;
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    opensmt_set_precision (ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , 0.0, 1.0);
    for (i=0;i<100;++i) {
        opensmt_push(ctx);
        double v1 = (double)rand()/RAND_MAX;
        double v2 = (double)rand()/RAND_MAX;
        opensmt_expr lb = opensmt_mk_num(ctx, v1);
        opensmt_expr ub = opensmt_mk_num(ctx, v2);
        opensmt_expr geq = opensmt_mk_geq(ctx, x, lb);
        opensmt_expr leq = opensmt_mk_leq(ctx, x, ub);
        opensmt_assert(ctx, geq);
        opensmt_assert(ctx, leq);
        printf("%g < x < %g --- ", v1, v2);
        opensmt_result res = opensmt_check( ctx );
        printf( "%s\n", res == l_false ? "unsat" : "sat" );
        opensmt_pop(ctx);
    }
    opensmt_del_context(ctx);
    return 0;
}
