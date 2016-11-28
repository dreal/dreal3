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
#include "ibex_ExprCtr.h"
#include "ibex_Interval.h"
#include "ibex_IntervalVector.h"
#include "ibex_NumConstraint.h"

namespace ibex {
class Function;
}  // namespace ibex

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
    // z = atan2(y, x)
    const ExprSymbol & x = ExprSymbol::new_();

    //  Function f(x, pow(3, x) - 1);
    //  NumConstraint c(x, pow(3, x) = 1);
    ExprNode const & n0 = ExprConstant::new_scalar(3.0);
    ExprNode const & n1 = ibex::pow(n0, x);
    ExprNode const & n2 = x;
    ExprCtr const & c1 = n1 > n2;
    NumConstraint c(x, c1);
    CtcFwdBwd ctc(c);

    IntervalVector box(1);
    box[0] = Interval(0, 10);

    cout << "Before contract: " << box << endl;
    ctc.contract(box);
    cout << "After contract: " << box << endl;
    return 0;
}
