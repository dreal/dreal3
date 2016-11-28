/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>


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

#include "util/hexfloat.h"

#include <stdio.h>

#include "util/logging.h"

using std::string;

namespace dreal {
string to_hexfloat(double x) {
    static int const BUF_SIZE = 100;
    char buf[BUF_SIZE];
    int len = snprintf(buf, sizeof(buf), "%a", x);
    if (len >= BUF_SIZE) {
        DREAL_LOG_WARNING << "to_hexfloat: printing " << x << " requires more than " << BUF_SIZE
                          << " bytes of buffer.";
    }
    return buf;
}
}  // namespace dreal
