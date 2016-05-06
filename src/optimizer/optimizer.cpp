/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>

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

#include <cmath>
#include <unordered_set>
#include <vector>
#include <map>
#include "optimizer/optimizer.h"
#include "util/eval.h"

using std::vector;
using std::cerr;
using std::endl;
using std::unordered_set;
using std::map;

namespace dreal {

optimizer::optimizer(box & b, vector<Enode*> const & l, Egraph & e, SMTConfig & c)
    : domain(b), egraph(e), config(c) {
    // iterate through l and define error functions
    for (auto lit : l) {
    assert(lit->hasPolarity());
    assert(lit->getArity() == 2);
    bool pos = (lit->getPolarity() == l_True);
    Enode * left = lit -> get1st();
    Enode * right = lit -> get2nd();
    Enode * f = nullptr;
    Enode * f_plain = nullptr;  // simplified error function for ease of differentiation
    if (pos && lit->isEq()) {
        f = egraph.mkMinus(left, right);
        f_plain = f;
    } else if (!pos && lit->isEq()) {
        f = egraph.mkNum("0");
        f_plain = f;
    } else if ( (pos && lit->isLeq()) || (pos && lit->isLt())
            || (!pos && lit->isGeq()) || (!pos && lit->isGt()) ) {
        f_plain = egraph.mkMinus(left, right);
        f = egraph.mkPlus(f_plain, egraph.mkAbs(egraph.cons(f_plain)));
    } else if ( (pos && lit->isGeq()) || (pos && lit->isGt())
            || (!pos && lit->isLeq()) || (!pos && lit->isLt()) ) {
        f_plain = egraph.mkMinus(left, right);
        f = egraph.mkMinus(f_plain, egraph.mkAbs(egraph.cons(f_plain)));
    }
    error_funcs.push_back(f);
    plainf.emplace(f, f_plain);
    }
}

optimizer::~optimizer() {
    // will clean up the traces
}

bool optimizer::improve(box& p) {
    // will have multiple methods
    return improve_naive(p);
}

bool optimizer::improve_naive(box& p) {  //  note that p is a point not a nontrivial box
    Enode * target = nullptr;  // will pick one target error function
    double delta = config.nra_precision;
    double max_error = delta;
    for (auto f : error_funcs) {
    // evaluate f on p
    double c = std::fabs(eval_enode_term(f, p));
    cerr << "for f = " << f << ", the error evaluates to " << c << endl;
    if (c > max_error) {
        max_error = c;
        target = f;
    }
    }
    if (max_error <= delta) {
    cerr << "error already minimized" << endl;
    return false;
    }
    cerr << "max_error is: " << max_error << ", happening on function " << target << endl;
    // otherwise, move on each dimension based on the gradient of f
    Enode * ptarget = plainf[target];  // use the simplified form for computing gradients
    map<Enode*, double> new_values;
    unordered_set<Enode*> vars = ptarget->get_vars();
    for (auto v : vars) {
    Enode * gradient_v = egraph.mkDeriv(ptarget, v);
    double p_v = p.get_value(v).lb();
    double grad = eval_enode_term(gradient_v, p);
    // take a newton step on the dimention
    cerr << "exploring the domain:\n" << domain << endl;
    double length = domain.get_value(v).ub() - domain.get_value(v).lb();
    double step = ((p_v-domain.get_value(v).lb())/(length+delta))*(domain.get_value(v).ub()-p_v);
    cerr << "taking a step of size: " << step << endl;
    cerr << "at gradient " << grad << endl;
    double newv = p_v - step*grad;
    cerr << "making a move on " << v << " by " << newv << endl;
    new_values.emplace(v, newv);
    }
    // TODO(sean): collect the box that it has been through
    // if value interval has no zero, push to the learned boxes; the new point is the improved point
    // if value interval has zero, push that box to the top!
    for (auto v : vars) {
    // change the value in p using the new point
    p.set_value(v, new_values[v], new_values[v]);  // lower and upper bounds are the same
    }
    cerr << "the new point is:\n" << p << endl;
    return true;
}
}  // namespace dreal
