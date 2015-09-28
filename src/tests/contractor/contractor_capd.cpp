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
#include <utility>
#include "opensmt/api/opensmt_c.h"
#include "opensmt/api/OpenSMTContext.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using std::cerr;
using std::endl;
using std::make_pair;

namespace dreal {

TEST_CASE("capd_fwd") {
    opensmt_init();
    cerr << "========CAPD_FWD========\n";
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_set_precision(ctx, 0.0000001);

    opensmt_expr x   = opensmt_mk_real_var(ctx, "x", -100, 100);
    opensmt_expr x_0 = opensmt_mk_real_var(ctx, "x_0_0", -100, 100);
    opensmt_expr x_t = opensmt_mk_real_var(ctx, "x_0_t", -100, 100);
    opensmt_expr p   = opensmt_mk_real_var(ctx, "p", 0.0, 1.0);
    opensmt_expr p_0 = opensmt_mk_real_var(ctx, "p_0_0", 0.0, 1.0);
    opensmt_expr p_t = opensmt_mk_real_var(ctx, "p_0_t", 0.0, 1.0);
    opensmt_expr time_0 = opensmt_mk_real_var(ctx, "time_0", 0.0, 40.0);

    box b({static_cast<Enode*>(x),
           static_cast<Enode*>(x_0),
           static_cast<Enode*>(x_t),
           static_cast<Enode*>(p),
           static_cast<Enode*>(p_0),
           static_cast<Enode*>(p_t),
           static_cast<Enode*>(time_0)});
    b[1] = -10.0;  // x_0 = -10;
    b[2] = 10.0;   // x_t = 10.0;
    b[4] = 0.0;    // p_0 = 0.0;

    opensmt_expr zero  = opensmt_mk_num(ctx, 0.0);
    opensmt_expr half  = opensmt_mk_num(ctx, 0.5);
    opensmt_expr one   = opensmt_mk_num(ctx, 1.0);
    opensmt_expr two   = opensmt_mk_num(ctx, 2.0);
    opensmt_expr pi    = opensmt_mk_num(ctx, 3.14159265359);
    opensmt_expr ten   = opensmt_mk_num(ctx, 10.0);
    opensmt_expr m_ten = opensmt_mk_num(ctx, -10.0);

    opensmt_expr rhs_x = one;
    opensmt_expr rhs_p = opensmt_mk_times_2(ctx,
                                            opensmt_mk_div(ctx, one,
                                                           opensmt_mk_pow(ctx,
                                                                          opensmt_mk_times_2(ctx, two, pi),
                                                                          half)),
                                            opensmt_mk_exp(ctx,
                                                           opensmt_mk_div(ctx,
                                                                          opensmt_mk_uminus(ctx,
                                                                                            opensmt_mk_pow(ctx, x, two)),
                                                                          two)));
    opensmt_expr vars[2] = {x, p};
    opensmt_expr rhses[2] = {rhs_x, rhs_p};
    opensmt_define_ode(ctx, "flow_1", vars, rhses, 2);
    opensmt_expr assert1 = opensmt_mk_eq(ctx, x_0, m_ten);
    opensmt_expr assert2 = opensmt_mk_eq(ctx, p_0, zero);
    opensmt_expr assert3 = opensmt_mk_eq(ctx, x_t, ten);
    opensmt_expr assert4 = opensmt_mk_geq(ctx, p_t, zero);

    opensmt_expr vars_t[2] = {x_t, p_t};
    opensmt_expr vars_0[2] = {x_0, p_0};

    opensmt_expr assert5 = opensmt_mk_integral(ctx, vars_t, zero, time_0, vars_0, 2, "flow_1");

    integral_constraint ic(static_cast<Enode*>(assert5), 1,
                           static_cast<Enode*>(zero),
                           static_cast<Enode*>(time_0),
                           {static_cast<Enode*>(x_0), static_cast<Enode*>(p_0)}, {},
                           {static_cast<Enode*>(x_t), static_cast<Enode*>(p_t)}, {},
                           {},
                           {make_pair("x", static_cast<Enode*>(rhs_x)),
                            make_pair("p", static_cast<Enode*>(rhs_p))});
    ode_constraint oc(ic, {});

    contractor c = mk_contractor_capd_fwd_full(b, &oc);

    cerr << oc << endl;
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

    REQUIRE(!input_after[0]);
    REQUIRE(input_after[1]);
    REQUIRE(input_after[2]);
    REQUIRE(!input_after[3]);
    REQUIRE(input_after[4]);
    REQUIRE(input_after[5]);
    REQUIRE(input_after[6]);

    REQUIRE(!output_after[0]);
    REQUIRE(!output_after[1]);
    REQUIRE(!output_after[2]);
    REQUIRE(!output_after[3]);
    REQUIRE(!output_after[4]);
    REQUIRE(output_after[5]);
    REQUIRE(output_after[6]);

    auto used_ctcs = c.used_constraints();
    REQUIRE(used_ctcs.size() == 1);
    REQUIRE(used_ctcs.find(&oc) != used_ctcs.end());

    opensmt_del_context(ctx);
}

TEST_CASE("capd_bwd") {
    opensmt_init();
    cerr << "========CAPD_BWD========\n";
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_set_precision(ctx, 0.0000001);

    opensmt_expr x   = opensmt_mk_real_var(ctx, "x", -100, 100);
    opensmt_expr x_0 = opensmt_mk_real_var(ctx, "x_0_0", -100, 100);
    opensmt_expr x_t = opensmt_mk_real_var(ctx, "x_0_t", -100, 100);
    opensmt_expr p   = opensmt_mk_real_var(ctx, "p", 0.0, 1.0);
    opensmt_expr p_0 = opensmt_mk_real_var(ctx, "p_0_0", 0.0, 1.0);
    opensmt_expr p_t = opensmt_mk_real_var(ctx, "p_0_t", 0.0, 1.0);
    opensmt_expr time_0 = opensmt_mk_real_var(ctx, "time_0", 0.0, 40.0);

    box b({static_cast<Enode*>(x),
           static_cast<Enode*>(x_0),
           static_cast<Enode*>(x_t),
           static_cast<Enode*>(p),
           static_cast<Enode*>(p_0),
           static_cast<Enode*>(p_t),
           static_cast<Enode*>(time_0)});
    b[1] = -10.0;  // x_0 = -10;
    b[2] = 10.0;   // x_t = 10.0;
    b[5] = 1.0;    // p_t = 1.0;

    opensmt_expr zero  = opensmt_mk_num(ctx, 0.0);
    opensmt_expr half  = opensmt_mk_num(ctx, 0.5);
    opensmt_expr one   = opensmt_mk_num(ctx, 1.0);
    opensmt_expr two   = opensmt_mk_num(ctx, 2.0);
    opensmt_expr pi    = opensmt_mk_num(ctx, 3.14159265359);
    opensmt_expr ten   = opensmt_mk_num(ctx, 10.0);
    opensmt_expr m_ten = opensmt_mk_num(ctx, -10.0);

    opensmt_expr rhs_x = one;
    opensmt_expr rhs_p = opensmt_mk_times_2(ctx,
                                            opensmt_mk_div(ctx, one,
                                                           opensmt_mk_pow(ctx,
                                                                          opensmt_mk_times_2(ctx, two, pi),
                                                                          half)),
                                            opensmt_mk_exp(ctx,
                                                           opensmt_mk_div(ctx,
                                                                          opensmt_mk_uminus(ctx,
                                                                                            opensmt_mk_pow(ctx, x, two)),
                                                                          two)));
    opensmt_expr vars[2] = {x, p};
    opensmt_expr rhses[2] = {rhs_x, rhs_p};
    opensmt_define_ode(ctx, "flow_1", vars, rhses, 2);
    opensmt_expr assert1 = opensmt_mk_eq(ctx, x_0, m_ten);
    opensmt_expr assert2 = opensmt_mk_eq(ctx, p_0, zero);
    opensmt_expr assert3 = opensmt_mk_eq(ctx, x_t, ten);
    opensmt_expr assert4 = opensmt_mk_geq(ctx, p_t, zero);

    opensmt_expr vars_t[2] = {x_t, p_t};
    opensmt_expr vars_0[2] = {x_0, p_0};

    opensmt_expr assert5 = opensmt_mk_integral(ctx, vars_t, zero, time_0, vars_0, 2, "flow_1");

    integral_constraint ic(static_cast<Enode*>(assert5), 1,
                           static_cast<Enode*>(zero),
                           static_cast<Enode*>(time_0),
                           {static_cast<Enode*>(x_0), static_cast<Enode*>(p_0)}, {},
                           {static_cast<Enode*>(x_t), static_cast<Enode*>(p_t)}, {},
                           {},
                           {make_pair("x", static_cast<Enode*>(rhs_x)),
                            make_pair("p", static_cast<Enode*>(rhs_p))});
    ode_constraint oc(ic, {});

    contractor c = mk_contractor_capd_bwd_full(b, &oc);

    cerr << oc << endl;
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

    REQUIRE(!input_after[0]);
    REQUIRE(input_after[1]);
    REQUIRE(input_after[2]);
    REQUIRE(!input_after[3]);
    REQUIRE(input_after[4]);
    REQUIRE(input_after[5]);
    REQUIRE(input_after[6]);

    REQUIRE(!output_after[0]);
    REQUIRE(!output_after[1]);
    REQUIRE(!output_after[2]);
    REQUIRE(!output_after[3]);
    REQUIRE(output_after[4]);
    REQUIRE(!output_after[5]);
    REQUIRE(output_after[6]);

    auto used_ctcs = c.used_constraints();
    REQUIRE(used_ctcs.size() == 1);
    REQUIRE(used_ctcs.find(&oc) != used_ctcs.end());

    opensmt_del_context(ctx);
}
}  // namespace dreal
