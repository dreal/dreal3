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
#include <iostream>
#include "opensmt/api/opensmt_c.h"
#include "opensmt/api/OpenSMTContext.h"
#include "util/box.h"
#include "util/constraint.h"
#include "contractor/contractor.h"
#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using std::cerr;
using std::endl;

namespace dreal {
TEST_CASE("ibex_fwdbwd_01") {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_set_precision(ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , -3, 3);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y" , -3, 3);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z" , -3, 3);
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    opensmt_expr exp1 = opensmt_mk_abs(ctx, x);
    opensmt_expr exp2 = opensmt_mk_cos(ctx, x);
    opensmt_expr exp3 = opensmt_mk_div(ctx, exp1, exp2);
    opensmt_expr exp4 = opensmt_mk_sin(ctx, x);
    opensmt_expr eq   = opensmt_mk_eq(ctx, exp4, exp3);
    Enode * node_eq   = static_cast<Enode *>(eq);

    nonlinear_constraint nc(node_eq, true);
    box b({var_x, var_y, var_z});
    contractor c = mk_contractor_ibex_fwdbwd(b, &nc);
    cerr << nc << endl;
    cerr << b << endl;
    auto input1 = c.input();
    auto output1 = c.input();
    cerr << "Input  (BEFORE) : ";  input1.display(cerr) << endl;
    cerr << "Output (BEFORE) : "; output1.display(cerr) << endl;
    b = c.prune(b, opensmt_ctx->getConfig());
    cerr << b << endl;
    auto input2 = c.input();
    auto output2 = c.output();
    cerr << "Input  (AFTER)  : ";  input2.display(cerr) << endl;
    cerr << "Output (AFTER)  : "; output2.display(cerr) << endl;
    opensmt_del_context(ctx);
}

TEST_CASE("ibex_fwdbwd_02") {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_set_precision(ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , -3, 3);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y" , -3, 3);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z" , -3, 3);
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    opensmt_expr exp1 = opensmt_mk_abs(ctx, x);           // abs(x)
    opensmt_expr exp2 = opensmt_mk_cos(ctx, y);           // cos(y)
    opensmt_expr exp3 = opensmt_mk_div(ctx, exp1, exp2);  // abs(x) / cos(y)
    opensmt_expr exp4 = opensmt_mk_sin(ctx, x);           // sin(x)
    opensmt_expr eq   = opensmt_mk_eq(ctx, exp4, exp3);   // sin(x) == abs(x) / cos(y)
    Enode * node_eq   = static_cast<Enode *>(eq);

    nonlinear_constraint nc(node_eq, true);
    box b({var_x, var_y, var_z});
    contractor c = mk_contractor_ibex_fwdbwd(b, &nc);
    cerr << nc << endl;
    cerr << b << endl;
    auto input1 = c.input();
    auto output1 = c.input();
    cerr << "Input  (BEFORE) : "; input1.display(cerr)  << endl;
    cerr << "Output (BEFORE) : "; output1.display(cerr) << endl;
    b = c.prune(b, opensmt_ctx->getConfig());
    cerr << b << endl;
    auto input2 = c.input();
    auto output2 = c.output();
    cerr << "Input  (AFTER)  : "; input2.display(cerr)  << endl;
    cerr << "Output (AFTER)  : "; output2.display(cerr) << endl;
    opensmt_del_context(ctx);
}

TEST_CASE("ibex_polytope") {
    opensmt_init();
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_set_precision(ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , -3, 3);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y" , -3, 3);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z" , -3, 3);
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    opensmt_expr exp1 = opensmt_mk_abs(ctx, x);
    opensmt_expr exp2 = opensmt_mk_cos(ctx, x);
    opensmt_expr exp3 = opensmt_mk_div(ctx, exp1, exp2);
    opensmt_expr exp4 = opensmt_mk_sin(ctx, x);
    opensmt_expr eq   = opensmt_mk_eq(ctx, exp4, exp3);
    Enode * node_eq   = static_cast<Enode *>(eq);
    node_eq->setPolarity(l_True);

    nonlinear_constraint nc(node_eq, true);
    box b({var_x, var_y, var_z});
    contractor c = mk_contractor_ibex_polytope(0.001, {var_x, var_y, var_z}, {&nc});
    cerr << nc << endl;
    cerr << b << endl;
    auto input1 = c.input();
    auto output1 = c.input();
    cerr << "IBEX_polytope Input  (BEFORE) : ";  input1.display(cerr) << endl;
    cerr << "IBEX_polytope Output (BEFORE) : "; output1.display(cerr) << endl;
    b = c.prune(b, opensmt_ctx->getConfig());
    cerr << b << endl;
    auto input2 = c.input();
    auto output2 = c.output();
    cerr << "IBEX_polytope Input  (AFTER)  : ";  input2.display(cerr) << endl;
    cerr << "IBEX_polytope Output (AFTER)  : "; output2.display(cerr) << endl;
    opensmt_del_context(ctx);
}
}  // namespace dreal
