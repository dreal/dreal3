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

#include <iostream>

#include "ibex_CtcFwdBwd.h"
#include "ibex_Expr.h"
#include "ibex_Function.h"
#include "ibex_Interval.h"
#include "ibex_IntervalVector.h"
#include "ibex_NumConstraint.h"

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
    // z = atan2(y, x)
    const ExprSymbol & x = ExprSymbol::new_();
    const ExprSymbol & y = ExprSymbol::new_();
    const ExprSymbol & z = ExprSymbol::new_();
    Function f(y, x, z, z - atan2(y, x));
    NumConstraint c(f);
    CtcFwdBwd ctc(c);

    IntervalVector box(3);
    box[0] = Interval(1, 1);
    box[1] = Interval(0, 0);
    box[2] = Interval(-100, 100);

    cout << "Before contract: " << box << endl;
    ctc.contract(box);
    cout << "After contract: " << box << endl;
    return 0;
}
