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

#include <iostream>
#include "ibex/ibex.h"

using ibex::Variable;
using ibex::Function;
using ibex::NumConstraint;
using ibex::CtcFwdBwd;
using ibex::IntervalVector;
using ibex::Interval;
using ibex::ExprSymbol;
using ibex::ExprCtr;
using ibex::ExprConstant;
using ibex::ExprNode;
using std::cout;
using std::endl;

int main() {
    NumConstraint c("x1", "x2", "cost", "cost = cos(x1^30 + x2^30)");
    IntervalVector box(3);
    box[0] = Interval(-100000, 100000);
    box[1] = Interval(-100000, 100000);

    cout << "box before=" << box << endl;
    CtcFwdBwd(c).contract(box);
    cout << "box after=" << box << endl;

    return 0;
}
