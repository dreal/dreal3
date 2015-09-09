/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

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

#include "util/cxx11_check.h"
#include "util/box.h"
#include "util/static_warning.h"
#include "contractor/contractor.h"

namespace dreal {

void check_nothrow_move_constructible() {
    // TODO(soonhok): use static-warning
    // reference: http://stackoverflow.com/questions/8936063/does-there-exist-a-static-warning

    STATIC_WARNING(std::is_nothrow_move_constructible<ibex::IntervalVector>::value,
                   "class ibex::IntervalVector is not nothrow-move-constructible.");
    STATIC_WARNING(std::is_nothrow_move_constructible<ibex::Interval>::value,
                   "class ibex::Interval is not nothrow-move-constructible.");
    STATIC_WARNING(std::is_nothrow_move_constructible<box>::value,
                   "class dreal::box is not nothrow-move-constructible.");
    STATIC_WARNING(std::is_nothrow_move_constructible<contractor>::value,
                   "class dreal::contractor is not nothrow-move-constructible.");
    STATIC_WARNING(std::is_nothrow_move_constructible<capd::interval>::value,
                   "class capd::Interval is not nothrow-move-constructible.");
    STATIC_WARNING(std::is_nothrow_move_constructible<capd::IVector>::value,
                   "class dreal::contractor is not nothrow-move-constructible.");
}
}  // namespace dreal
