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

#include "util/point.h"

using std::ostream;

namespace dreal {

ostream& operator<<(ostream& out, point const & p) {
    out << "(";
    std::streamsize ss = out.precision();
    out.precision(16);
    unsigned n = p.m_values.size();
    if (n >= 1) {
        out << p.m_values[0];
        for (unsigned i = 1; i < n; i++) {
            out << ", " << p.m_values[i];
        }
    }
    out << ")";
    out.precision(ss);
    return out;
}
}  // namespace dreal
