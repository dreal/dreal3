/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

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

#include <functional>
#include <initializer_list>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "ibex/ibex.h"
#include "capd/capdlib.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/ibex_enode.h"
#include "util/constraint.h"
#include "util/contractor.h"

using std::function;
using std::initializer_list;
using std::vector;
using std::unordered_set;

namespace dreal {

contractor_capd_fwd::contractor_capd_fwd(box const & box, ode_constraint const * const ctr)
    : contractor_cell(contractor_kind::CAPD_FWD), m_ctr(ctr) {
}
box contractor_capd_fwd::prune(box b) const {
    // TODO(soonhok): implement this
    return b;
}

contractor_capd_bwd::contractor_capd_bwd(box const & box, ode_constraint const * const ctr)
    : contractor_cell(contractor_kind::CAPD_BWD), m_ctr(ctr) {
}
box contractor_capd_bwd::prune(box b) const {
    // TODO(soonhok): implement this
    return b;
}

contractor mk_contractor_capd_fwd(box const & box, ode_constraint const * const ctr) {
    return contractor(shared_ptr<contractor_cell>(new contractor_capd_fwd(box, ctr)));
}
contractor mk_contractor_capd_bwd(box const & box, ode_constraint const * const ctr) {
    return contractor(shared_ptr<contractor_cell>(new contractor_capd_bwd(box, ctr)));
}


}
