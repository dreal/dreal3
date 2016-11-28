/*********************************************************************
Author: Damien Zufferey <zufferey@csail.mit.edu>

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

#include <cassert>
#include <memory>
#include <unordered_set>

#include "ibex_Interval.h"
#include "opensmt/api/opensmt_c.h"
#include "util/box.h"
#include "util/glpk_wrapper.h"

#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

class Enode;
class OpenSMTContext;

using std::unordered_set;

namespace dreal {

// Example from the GLPK doc
// max 10x + 6y + 4z
// s.t.
//   x +  y + z  <= 100
// 10x + 4y + 5z <= 600
//  2x + 2y + 6z <= 300
// x,y,z ∈ [0,100]
// ---
// objective = 733.333
// x = 33.3333
// y = 66.6667
// z = 0

opensmt_expr make_linear(opensmt_context ctx, double cx, opensmt_expr x, double cy, opensmt_expr y,
                         double cz, opensmt_expr z) {
    opensmt_expr ex = opensmt_mk_times_2(ctx, opensmt_mk_num(ctx, cx), x);
    opensmt_expr ey = opensmt_mk_times_2(ctx, opensmt_mk_num(ctx, cy), y);
    opensmt_expr ez = opensmt_mk_times_2(ctx, opensmt_mk_num(ctx, cz), z);
    return opensmt_mk_plus_2(ctx, opensmt_mk_plus_2(ctx, ex, ey), ez);
}

TEST_CASE("glpk_sat") {
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x", 0, 100);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y", 0, 100);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z", 0, 100);
    opensmt_expr c1 =
        opensmt_mk_leq(ctx, make_linear(ctx, 1, x, 1, y, 1, z), opensmt_mk_num(ctx, 100));
    opensmt_expr c2 =
        opensmt_mk_leq(ctx, make_linear(ctx, 10, x, 4, y, 5, z), opensmt_mk_num(ctx, 600));
    opensmt_expr c3 =
        opensmt_mk_leq(ctx, make_linear(ctx, 2, x, 2, y, 6, z), opensmt_mk_num(ctx, 300));
    opensmt_expr cObj = make_linear(ctx, 10, x, 6, y, 4, z);
    Enode * e1 = static_cast<Enode *>(c1);
    Enode * e2 = static_cast<Enode *>(c2);
    Enode * e3 = static_cast<Enode *>(c3);
    Enode * eObj = static_cast<Enode *>(cObj);
    unordered_set<Enode *> es({e1, e2, e3});
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    box b({var_x, var_y, var_z});
    glpk_wrapper solver(b, es);
    solver.set_objective(eObj);
    solver.set_maximize();
    // solver.print_to_file("/dev/stdout");
    assert(solver.is_sat());
    solver.get_solution(b);
    // std::cerr << solver.get_objective() << std::endl;
    assert(solver.get_objective() >= -1e-3 + 733.333);
    assert(solver.get_objective() <= 1e-3 + 733.333);
    assert(b[var_x].lb() >= -1e-4 + 33.3333);
    assert(b[var_x].ub() <= 1e-4 + 33.3333);
    assert(b[var_y].lb() >= -1e-4 + 66.6667);
    assert(b[var_y].ub() <= 1e-4 + 66.6667);
    assert(b[var_z].lb() >= -1e-4 + 0);
    assert(b[var_z].ub() <= 1e-4 + 0);
    opensmt_del_context(ctx);
}

TEST_CASE("glpk_interior_sat") {
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x", 0, 100);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y", 0, 100);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z", 0, 100);
    opensmt_expr c1 =
        opensmt_mk_leq(ctx, make_linear(ctx, 1, x, 1, y, 1, z), opensmt_mk_num(ctx, 100));
    opensmt_expr c2 =
        opensmt_mk_leq(ctx, make_linear(ctx, 10, x, 4, y, 5, z), opensmt_mk_num(ctx, 600));
    opensmt_expr c3 =
        opensmt_mk_leq(ctx, make_linear(ctx, 2, x, 2, y, 6, z), opensmt_mk_num(ctx, 300));
    Enode * e1 = static_cast<Enode *>(c1);
    Enode * e2 = static_cast<Enode *>(c2);
    Enode * e3 = static_cast<Enode *>(c3);
    unordered_set<Enode *> es({e1, e2, e3});
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    box b({var_x, var_y, var_z});
    glpk_wrapper solver(b, es);
    solver.set_maximize();
    solver.use_interior_point();
    // solver.print_to_file("/dev/stdout");
    assert(solver.is_sat());
    opensmt_del_context(ctx);
}

TEST_CASE("glpk_no_obj") {
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x", 0, 100);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y", 0, 100);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z", 0, 100);
    opensmt_expr c1 =
        opensmt_mk_leq(ctx, make_linear(ctx, 1, x, 1, y, 1, z), opensmt_mk_num(ctx, 100));
    opensmt_expr c2 =
        opensmt_mk_leq(ctx, make_linear(ctx, 10, x, 4, y, 5, z), opensmt_mk_num(ctx, 600));
    opensmt_expr c3 =
        opensmt_mk_leq(ctx, make_linear(ctx, 2, x, 2, y, 6, z), opensmt_mk_num(ctx, 300));
    opensmt_expr cObj = make_linear(ctx, 10, x, 6, y, 4, z);
    Enode * e1 = static_cast<Enode *>(c1);
    Enode * e2 = static_cast<Enode *>(c2);
    Enode * e3 = static_cast<Enode *>(c3);
    Enode * eObj = static_cast<Enode *>(cObj);
    unordered_set<Enode *> es({e1, e2, e3});
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    box b({var_x, var_y, var_z});
    glpk_wrapper solver(b, es);
    // solver.print_to_file("/dev/stdout");
    assert(solver.is_sat());
    opensmt_del_context(ctx);
}

TEST_CASE("glpk_min") {
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x", 0, 100);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y", 0, 100);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z", 0, 100);
    opensmt_expr c1 =
        opensmt_mk_leq(ctx, make_linear(ctx, 1, x, 1, y, 1, z), opensmt_mk_num(ctx, 100));
    opensmt_expr c2 =
        opensmt_mk_leq(ctx, make_linear(ctx, 10, x, 4, y, 5, z), opensmt_mk_num(ctx, 600));
    opensmt_expr c3 =
        opensmt_mk_leq(ctx, make_linear(ctx, 2, x, 2, y, 6, z), opensmt_mk_num(ctx, 300));
    opensmt_expr cObj = make_linear(ctx, 10, x, 6, y, 4, z);
    Enode * e1 = static_cast<Enode *>(c1);
    Enode * e2 = static_cast<Enode *>(c2);
    Enode * e3 = static_cast<Enode *>(c3);
    Enode * eObj = static_cast<Enode *>(cObj);
    unordered_set<Enode *> es({e1, e2, e3});
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    box b({var_x, var_y, var_z});
    glpk_wrapper solver(b, es);
    solver.set_objective(eObj);
    solver.set_minimize();
    // solver.print_to_file("/dev/stdout");
    assert(solver.is_sat());
    solver.get_solution(b);
    // std::cerr << solver.get_objective() << std::endl;
    assert(solver.get_objective() >= -1e-3);
    assert(solver.get_objective() <= 1e-3);
    assert(b[var_x].lb() >= -1e-4);
    assert(b[var_x].ub() <= 1e-4);
    assert(b[var_y].lb() >= -1e-4);
    assert(b[var_y].ub() <= 1e-4);
    assert(b[var_z].lb() >= -1e-4);
    assert(b[var_z].ub() <= 1e-4);
    opensmt_del_context(ctx);
}

TEST_CASE("glpk_unsat") {
    opensmt_context ctx = opensmt_mk_context(qf_nra);
    OpenSMTContext * opensmt_ctx = static_cast<OpenSMTContext *>(ctx);
    opensmt_expr x = opensmt_mk_real_var(ctx, "x", 0, 100);
    opensmt_expr y = opensmt_mk_real_var(ctx, "y", 0, 100);
    opensmt_expr z = opensmt_mk_real_var(ctx, "z", 0, 100);
    opensmt_expr c1 =
        opensmt_mk_leq(ctx, make_linear(ctx, 1, x, 1, y, 0, z), opensmt_mk_num(ctx, -100));
    opensmt_expr c2 =
        opensmt_mk_leq(ctx, make_linear(ctx, 10, x, 4, y, 0, z), opensmt_mk_num(ctx, 600));
    Enode * e1 = static_cast<Enode *>(c1);
    Enode * e2 = static_cast<Enode *>(c2);
    unordered_set<Enode *> es({e1, e2});
    Enode * var_x = static_cast<Enode *>(x);
    Enode * var_y = static_cast<Enode *>(y);
    Enode * var_z = static_cast<Enode *>(z);
    box b({var_x, var_y, var_z});
    glpk_wrapper solver(b, es);
    // solver.print_to_file("/dev/stdout");
    assert(!solver.is_sat());
    solver.use_interior_point();
    assert(!solver.is_sat());
    opensmt_del_context(ctx);
}

}  // namespace dreal
