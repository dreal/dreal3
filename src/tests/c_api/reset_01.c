/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, the dReal Team

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

// related issure: https://github.com/dreal/dreal3/issues/208

#include <assert.h>
#include <stdio.h>
#include "opensmt/api/opensmt_c.h"

int main() {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra_ode);
    opensmt_set_verbosity(ctx, 10);
    opensmt_expr a = opensmt_mk_bool_var(ctx, "a");
    opensmt_expr not_a = opensmt_mk_not(ctx, a);
    opensmt_assert(ctx, a);
    opensmt_assert(ctx, not_a);
    assert(opensmt_check(ctx) == l_false);
    opensmt_reset(ctx);
    a = opensmt_mk_bool_var(ctx, "a");
    opensmt_assert(ctx, a);
    opensmt_result res = opensmt_check(ctx);
    assert(res == l_true);
    fprintf(stderr, "Deleting context\n");
    opensmt_del_context(ctx);
return 0;
}
