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

#include "contractor/extract_bitset.h"

#include <initializer_list>
#include <vector>

#include "contractor/contractor.h"
#include "ibex/ibex.h"

namespace dreal {

using std::vector;
using std::initializer_list;

ibex::BitSet extract_bitset(vector<contractor> const & ctcs) {
    assert(ctcs.size() > 0);
    auto it = ctcs.begin();
    ibex::BitSet ret{(it++)->get_input()};
    while (it != ctcs.end()) {
        ret.union_with((it++)->get_input());
    }
    return ret;
}
ibex::BitSet extract_bitset(initializer_list<contractor> const & ctcs) {
    assert(ctcs.size() > 0);
    auto it = ctcs.begin();
    ibex::BitSet ret{(it++)->get_input()};
    while (it != ctcs.end()) {
        ret.union_with((it++)->get_input());
    }
    return ret;
}

}  // namespace dreal
