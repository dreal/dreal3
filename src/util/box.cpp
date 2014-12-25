/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <unordered_map>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/interval.h"
#include "util/var.h"
#include "util/logging.h"

using std::initializer_list;
using std::vector;
using std::string;
using std::ostream;

namespace dreal {
box::box() { }
box::box(initializer_list<var> const & var_list) : m_vec(var_list), m_name_map(m_vec.size()) {
    for (vector<var>::size_type i = 0; i < m_vec.size(); i++) {
        m_name_map.emplace(m_vec[i].getName(), i);
    }
}
void box::add(var const & v) {
    string const & name = v.getName();
    if (m_name_map.find(name) == m_name_map.end()) {
        m_name_map.emplace(name, m_vec.size());
        m_vec.push_back(v);
    }
}
void box::add(initializer_list<var> const & var_list) {
    for (auto const & v : var_list) {
        add(v);
    }
}

void box::intersect(box const & other) {
    assert(m_vec.size() == other.m_vec.size());
    for (vector<var>::size_type i = 0; i < m_vec.size(); i++) {
        m_vec[i].intersect(other.m_vec[i]);
    }
}

ostream& operator<<(ostream& out, box const & b) {
    DREAL_LOG_INFO << "box size = " << b.size();
    for (auto const & v : b.m_vec) {
        out << "\t" << v << endl;
    }
    return out;
}
}
