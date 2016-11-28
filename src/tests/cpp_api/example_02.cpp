/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>
        Soonho Kong <soonhok@cs.cmu.edu>

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
#include <vector>

#include "api/dreal.h"

using dreal::solver;
using dreal::expr;
using std::vector;

void test() {
    solver s;
    expr x1 = s.var("x1", -5, 5);
    expr p1 = s.var("p1", -5, 5);
    expr p2 = s.var("p2", -5, 5);
    expr p3 = s.var("p3", -5, 5);
    expr p4 = s.var("p4", -5, 5);
    expr p5 = s.var("p5", -5, 5);
    vector<expr> x = {x1};
    vector<expr> p = {p1, p2, p3, p4, p5};
    expr f1 = p1 * x1 + p2;
    vector<expr> f = {f1};
    expr V = p3 * (x1 ^ 2) + p4 * x1 + p5;

    double eps = 0.01;

    assert(x.size() == f.size());
    assert(eps > 0);

    expr ball = s.num("0");
    expr LV = s.num("0");

    for (unsigned i = 0; i < x.size(); i++) {
        ball = ball + (x[i] ^ 2);
        LV = LV + f[i] * der(V, x[i]);
    }

    expr search_condition = implies(ball > eps, V > 0) && implies(ball > eps, LV < 0);

    s.add(search_condition);

    s.print_problem();
    s.solve();

    return;
}

int main() {
    test();
    return 0;
}
