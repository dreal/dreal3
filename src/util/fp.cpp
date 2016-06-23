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

#include <cfenv>
#include <cstdlib>
#include <string>
#include "util/fp.h"

namespace dreal {
using std::string;

// TODO(soonhok): we assume that 'strtod' function honors rounding
//                mode. However this is not always the case. See [1]
//                for the details. A possible solution for this
//                problem is to use a custom 'strtod' function. For
//                example, consider [2] (note that we need to enable
//                Honor_FLT_ROUNDS).
//
// [1]: http://www.exploringbinary.com/visual-c-plus-plus-and-glibc-strtod-ignore-rounding-mode
// [2]: http://www.ampl.com/netlib/fp/dtoa.c

double stod_downward(char const * str) {
    int const saved_rounding_mode = fegetround();
    if (saved_rounding_mode != FE_DOWNWARD) {
        fesetround(FE_DOWNWARD);
        double const lb = strtod(str, nullptr);
        fesetround(saved_rounding_mode);
        return lb;
    } else {
        double const lb = strtod(str, nullptr);
        return lb;
    }
}

double stod_downward(string const & str) {
    return stod_downward(str.c_str());
}

double stod_upward(char const * str) {
    int const saved_rounding_mode = fegetround();
    if (saved_rounding_mode != FE_UPWARD) {
        fesetround(FE_UPWARD);
        double const lb = strtod(str, nullptr);
        fesetround(saved_rounding_mode);
        return lb;
    } else {
        double const lb = strtod(str, nullptr);
        return lb;
    }
}

double stod_upward(string const & str) {
    return stod_upward(str.c_str());
}

double stod_tonearest(char const * str) {
    int const saved_rounding_mode = fegetround();
    if (saved_rounding_mode != FE_TONEAREST) {
        fesetround(FE_TONEAREST);
        double const lb = strtod(str, nullptr);
        fesetround(saved_rounding_mode);
        return lb;
    } else {
        double const lb = strtod(str, nullptr);
        return lb;
    }
}

double stod_tonearest(string const & str) {
    return stod_tonearest(str.c_str());
}
}  // namespace dreal
