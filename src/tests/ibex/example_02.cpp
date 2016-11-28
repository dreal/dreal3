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

#include <algorithm>
#include <iostream>
#include "ibex/ibex.h"

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
#ifdef USE_CLP
    Variable x1, x2, y;
    NumConstraint c1(x1, x2, y, y >= ibex::min(x1, x2));
    NumConstraint c2(x1, x2, y, y <= ibex::max(x1, x2));
    ibex::SystemFactory factory;
    factory.add_var(x1);
    factory.add_var(x2);
    factory.add_var(y);
    factory.add_ctr(c1);
    factory.add_ctr(c2);
    ibex::System sys(factory);
    ibex::CtcHC4 ctc_hc4(sys.ctrs, 0.001);
    ibex::LinearRelaxCombo lrc(sys, ibex::LinearRelaxCombo::XNEWTON);
    ibex::CtcPolytopeHull ctc_ph(lrc, ibex::CtcPolytopeHull::ALL_BOX);

    IntervalVector box(3);
    box[0] = Interval(-10, 10);
    box[1] = Interval(-10, 10);
    box[2] = Interval(-1, 1);

    cout << "Before contract: " << box << endl;
    cout << box << endl;
    ctc_ph.contract(box);

    cout << "After contract: " << box << endl;
    cout << box << endl;
#endif
    return 0;
}
