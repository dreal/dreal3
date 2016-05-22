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
    Variable x1, x2;
    NumConstraint c1(x1, x2, x2 = ibex::asin(x1));
    NumConstraint c2(x1, x2, x1 = 1);
    cout << "c1 = " << c1 << endl;
    cout << "c2 = " << c2 << endl;
    ibex::SystemFactory factory;
    factory.add_var(x1);
    factory.add_var(x2);
    factory.add_ctr(c1);
    factory.add_ctr(c2);
    ibex::System sys(factory);
    ibex::CtcHC4 ctc_hc4(sys.ctrs, 0.001);
    ibex::LinearRelaxCombo lrc(sys, ibex::LinearRelaxCombo::XNEWTON);
    ibex::CtcPolytopeHull ctc_ph(lrc, ibex::CtcPolytopeHull::ALL_BOX);
    ibex::CtcCompo ctc_combo(ctc_ph, ctc_hc4);
    ibex::CtcFixPoint ctc_fp(ctc_combo);

    IntervalVector box(2);
    box[0] = Interval(-10, 10);
    box[1] = Interval(-10, 10);

    for (int i = 0; i < 10; ++i) {
        cout << "Before contract: " << box << endl;
        ctc_fp.contract(box);
        cout << "After contract: " << box << endl << endl << endl;
    }
    return 0;
}
