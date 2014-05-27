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

#include <iomanip>
#include <iostream>
#include <sstream>
#include "util/scoped_vec.h"

using std::endl;
using std::left;
using std::right;
using std::setfill;
using std::setw;
using std::stringstream;

namespace dreal {
scoped_vec::scoped_vec()  { }
scoped_vec::~scoped_vec() { }
void scoped_vec::push_back(value_type const & v) {
    m_vec.push_back(v);
}
void scoped_vec::push() {
    m_scopes.push_back(m_vec.size());
}
void scoped_vec::pop() {
    unsigned const prev_size = m_scopes.back();
    m_scopes.pop_back();
    unsigned cur_size = m_vec.size();
    while (cur_size-- > prev_size) { m_vec.pop_back(); }
}
scoped_vec::reference scoped_vec::operator[] (size_type n) {
    return m_vec[n];
}
scoped_vec::const_reference scoped_vec::operator[] (size_type n) const {
    return m_vec[n];
}
std::ostream & operator<<(std::ostream & out, scoped_vec const & s) {
    for (auto const & l : s) {
        stringstream ss;
        l->print(ss);
        out << right << setfill(' ') << setw(15) << "lit "
            << left  << setfill(' ') << setw(40) << ss.str() << " : " << l->getPolarity().toInt() << endl;
    }
    return out;
}
}
