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

#include <string>
#include <iostream>
#include <initializer_list>
#include <unordered_map>
#include <vector>
#include <utility>
#include "opensmt/egraph/Enode.h"
#include "ibex/ibex.h"
#include "util/flow.h"

namespace dreal {

using std::string;
using std::ostream;
using std::endl;

flow::flow() { }
flow::flow(Enode * const v, Enode * const e) {
    add(v, e);
}
void flow::add(Enode * const v, Enode * const e) {
    assert(m_vars.size() == m_odes.size());
    m_vars.push_back(v);
    m_odes.push_back(e);
}

ostream & operator<<(ostream & out, flow const & _flow) {
    for (unsigned i = 0; i < _flow.m_vars.size(); i++) {
        out << "d/dt[" << _flow.m_vars[i] << "] = "
            << _flow.m_odes[i] << endl;
    }
    return out;
}
}  // namespace dreal
