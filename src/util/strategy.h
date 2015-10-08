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

#pragma once

#include "opensmt/smtsolvers/SMTConfig.h"
#include "contractor/contractor.h"
#include "util/box.h"
#include "util/scoped_vec.h"

namespace dreal {
class strategy {
public:
    // Takes a stack of constraint and a box, return a contractor
    virtual contractor build_contractor(box const & box,
                                        scoped_vec<std::shared_ptr<constraint>> const &ctrs,
                                        bool const complete,
                                        SMTConfig const & config) const = 0;
};

class default_strategy : public strategy {
public:
    static bool term_cond(box const & old_box, box const & new_box);
    virtual contractor build_contractor(box const & box,
                                        scoped_vec<std::shared_ptr<constraint>> const &ctrs,
                                        bool const complete,
                                        SMTConfig const & config) const;
};
}  // namespace dreal
