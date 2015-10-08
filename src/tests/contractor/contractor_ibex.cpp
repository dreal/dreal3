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
#include <memory>
#include <unordered_set>
#include "opensmt/api/opensmt_c.h"
#include "opensmt/api/OpenSMTContext.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using std::cerr;
using std::endl;
using std::unordered_set;
using std::shared_ptr;
using std::make_shared;

namespace dreal {

TEST_CASE("ibex_fwdbwd_01") {
    cerr << "===================================================\n";
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

    box b({var_x, var_y, var_z});
    unordered_set<Enode*> var_set({var_x, var_y, var_z});
    auto nc = make_shared<nonlinear_constraint>(node_eq, var_set, true);
    contractor c = mk_contractor_ibex_fwdbwd(nc);
    cerr << *nc << endl;
    cerr << b << endl;
    auto input_before = c.input();
    auto output_before = c.output();
    cerr << "Input  (BEFORE) : ";  input_before.display(cerr) << endl;
    cerr << "Output (BEFORE) : "; output_before.display(cerr) << endl;
    c.prune(b, opensmt_ctx->getConfig());
    cerr << b << endl;
    auto input_after = c.input();
    auto output_after = c.output();
    cerr << "Input  (AFTER)  : ";  input_after.display(cerr) << endl;
    cerr << "Output (AFTER)  : "; output_after.display(cerr) << endl;
    for (auto ctc : c.used_constraints()) {
        cerr << "Used constraint : " << *ctc << endl;
    }
    REQUIRE((input_after[0]  && !input_after[1]  && !input_after[2]));
    REQUIRE((output_after[0] && !output_after[1] && !output_after[2]));
    auto used_ctcs = c.used_constraints();
    REQUIRE(used_ctcs.size() == 1);
    REQUIRE(used_ctcs.find(nc) != used_ctcs.end());
    opensmt_del_context(ctx);
}

TEST_CASE("ibex_fwdbwd_02") {
    cerr << "===================================================\n";
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

    box b({var_x, var_y, var_z});
    unordered_set<Enode*> var_set({var_x, var_y, var_z});
    auto nc = make_shared<nonlinear_constraint>(node_eq, var_set, true);
    contractor c = mk_contractor_ibex_fwdbwd(nc);
    cerr << *nc << endl;
    cerr << b << endl;
    auto input_before = c.input();
    auto output_before = c.output();
    cerr << "Input  (BEFORE) : "; input_before.display(cerr)  << endl;
    cerr << "Output (BEFORE) : "; output_before.display(cerr) << endl;
    c.prune(b, opensmt_ctx->getConfig());
    cerr << b << endl;
    auto input_after = c.input();
    auto output_after = c.output();
    cerr << "Input  (AFTER)  : "; input_after.display(cerr)  << endl;
    cerr << "Output (AFTER)  : "; output_after.display(cerr) << endl;
    for (auto ctc : c.used_constraints()) {
        cerr << "Used constraint : " << *ctc << endl;
    }
    REQUIRE((input_after[0]  && input_after[1]  && !input_after[2]));
    REQUIRE((output_after[0] && output_after[1] && !output_after[2]));
    auto used_ctcs = c.used_constraints();
    REQUIRE(used_ctcs.size() == 1);
    REQUIRE(used_ctcs.find(nc) != used_ctcs.end());
    opensmt_del_context(ctx);
}

TEST_CASE("ibex_polytope") {
    cerr << "===================================================\n";
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_set_precision(ctx, 0.0000001);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x" , -3, 3);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y" , -3, 3);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z" , -3, 3);
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);

    // y = cos(x);
    opensmt_expr eq1 = opensmt_mk_eq(ctx, y,
                                     opensmt_mk_cos(ctx, x));
    // x = sin(y);
    opensmt_expr eq2 = opensmt_mk_eq(ctx, x,
                                     opensmt_mk_sin(ctx, y));
    Enode * node_eq1 = static_cast<Enode *>(eq1);
    Enode * node_eq2 = static_cast<Enode *>(eq2);
    node_eq1->setPolarity(l_True);
    node_eq2->setPolarity(l_True);

    box b({var_x, var_y, var_z});
    unordered_set<Enode*> var_set({var_x, var_y, var_z});
    auto nc1 = make_shared<nonlinear_constraint>(node_eq1, var_set, true);
    auto nc2 = make_shared<nonlinear_constraint>(node_eq2, var_set, true);
    contractor c = mk_contractor_ibex_polytope(0.001, {var_x, var_y, var_z}, {nc1, nc2});
    cerr << *nc1 << endl;
    cerr << *nc2 << endl;
    cerr << b << endl;
    auto input_before = c.input();
    auto output_before = c.output();
    cerr << "IBEX_polytope Input  (BEFORE) : ";  input_before.display(cerr) << endl;
    cerr << "IBEX_polytope Output (BEFORE) : "; output_before.display(cerr) << endl;
    c.prune(b, opensmt_ctx->getConfig());
    cerr << b << endl;
    auto input_after = c.input();
    auto output_after = c.output();
    cerr << "IBEX_polytope Input  (AFTER)  : ";  input_after.display(cerr) << endl;
    cerr << "IBEX_polytope Output (AFTER)  : "; output_after.display(cerr) << endl;

    REQUIRE((input_after[0]  && input_after[1]  && !input_after[2]));
    REQUIRE((output_after[0] && output_after[1] && !output_after[2]));

    auto used_ctcs = c.used_constraints();
    for (auto ctc : used_ctcs) {
        cerr << "Used constraint : " << *ctc << endl;
    }
    REQUIRE(used_ctcs.size() == 2);
    REQUIRE(used_ctcs.find(nc1) != used_ctcs.end());
    REQUIRE(used_ctcs.find(nc2) != used_ctcs.end());
    opensmt_del_context(ctx);
}
}  // namespace dreal
