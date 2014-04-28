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

#include <iostream>
#include <string>
#include <limits>
#include "util/interval.h"
#include "util/hexfloat.h"

using std::ostream;
using std::string;
using std::numeric_limits;
using std::streamsize;

namespace dreal {
interval::interval() : lb(0), ub (0) { }

interval::interval(double const l, double const u)
    : lb(l), ub(u) {
}

interval::interval(rp_interval const rp_intv)
    : lb(rp_binf(rp_intv)), ub(rp_bsup(rp_intv)) {
}

ostream & interval::print(ostream & out, unsigned digits, bool exact) const {
    if (lb == -numeric_limits<double>::infinity()) {
        out << "(";
    } else {
        out << "[";
    }
    if (exact) {
        out << to_hexfloat(lb) << ", " << to_hexfloat(ub);
    } else {
        streamsize ss = out.precision();
        out.precision(digits);
        out << lb << ", " << ub;
        out.precision(ss);
    }
    if (ub == numeric_limits<double>::infinity()) {
        out << ")";
    } else {
        out << "]";
    }
    return out;
}

ostream & operator<<(ostream & out, interval const & i) {
    return i.print(out);
}
}
