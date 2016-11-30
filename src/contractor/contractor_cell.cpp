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

#include "contractor/contractor_cell.h"

#include <initializer_list>

#include "ibex/ibex.h"

namespace dreal {
using std::initializer_list;
ibex::BitSet contractor_cell::join_bitsets(initializer_list<ibex::BitSet> const & inputs) {
    assert(inputs.size() > 0);
    auto it = inputs.begin();
    ibex::BitSet ret{*(it++)};
    while (it != inputs.end()) {
        ret.union_with(*(it++));
    }
    return ret;
}
}  // namespace dreal
