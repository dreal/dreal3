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

// Related issue: https://github.com/ibex-team/ibex-lib/issues/145

#include <iostream>

#include "ibex_CtcNewton.h"
#include "ibex_Expr.h"
#include "ibex_Function.h"
#include "ibex_IntervalVector.h"

namespace ibex {
class CtcFwdBwd;
class Interval;
class NumConstraint;
}  // namespace ibex

using ibex::Variable;
using ibex::Function;
using ibex::NumConstraint;
using ibex::CtcFwdBwd;
using ibex::IntervalVector;
using ibex::Interval;
using ibex::ExprSymbol;
using std::cout;
using std::endl;

int main() {
    Variable x1, x2;
    Function f(x1, x2, ibex::Return(x1 - 1, ibex::asin(x2) - x1));
    double init_box[][2] = {{1, 1}, {1.570796326794893, 1.570796326794901}};
    IntervalVector box(2, init_box);
    ibex::CtcNewton newton(f);
    cout << "Before: " << box << endl;
    newton.contract(box);
    cout << "After: " << box << endl;
    return 0;
}
