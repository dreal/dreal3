/*********************************************************************
Author: Soonho Kong

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

#include "util/strengthen_enode.h"
#include <sstream>
#include <stdexcept>
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"
#include "util/logging.h"

using std::runtime_error;
using std::ostringstream;

namespace dreal {

/// strengthening a constraint (Enode) by eps (positive constant)
Enode * strengthen_enode(Egraph & eg, Enode * const e, double const eps, bool const polarity) {
    if (e->isNot()) {
        return strengthen_enode(eg, e->get1st(), eps, !polarity);
    }
    if (polarity && e->isEq()) {
        // e1 == e2  ==>  (a == 0)   (no change)
        return e;
    }
    Enode * const e1 = e->get1st();
    Enode * const e2 = e->get2nd();
    Enode * const eps_node = eg.mkNum(eps);
    if (!polarity && e->isEq()) {
        // |e1 - e2| >= eps
        return eg.mkGeq(eg.cons(eg.mkAbs(eg.cons(eg.mkMinus(e1, e2))), eg.cons(eps_node)));
    }
    if ((polarity && e->isLt()) || (!polarity && e->isGeq())) {
        // e1 <  e2  ==>  e1 < e2 - eps
        return eg.mkLt(eg.cons(e1, eg.cons(eg.mkMinus(e2, eps_node))));
    }
    if ((polarity && e->isLeq()) || (!polarity && e->isGt())) {
        // e1 <= e2  ==>  e1 <= e2 - eps
        return eg.mkLeq(eg.cons(e1, eg.cons(eg.mkMinus(e2, eps_node))));
    }
    if ((polarity && e->isGt()) || (!polarity && e->isLeq())) {
        // e1 >  e2  ==>  e1 > e2 + eps
        return eg.mkGt(eg.cons(e1, eg.cons(eg.mkPlus(e2, eps_node))));
    }
    if ((polarity && e->isGeq()) || (!polarity && e->isLt())) {
        // e1 >= e2  ==>  e1 >= e2 + eps
        return eg.mkGeq(eg.cons(e1, eg.cons(eg.mkPlus(e2, eps_node))));
    }
    // Something is wrong.
    ostringstream os;
    os << "strengthen_enode: should be unreachable (Enode = " << e << ")";
    throw runtime_error(os.str());
}
}  // namespace dreal
