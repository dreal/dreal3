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

#include "util/box.h"
#include "util/stat.h"
#include "contractor/contractor.h"
#include "opensmt/smtsolvers/SMTConfig.h"

namespace dreal {
void output_solution(box const & b, SMTConfig & config, unsigned i = 0);

class naive_icp {
public:
    static box solve(box b, contractor const & ctc, SMTConfig & config);
};

class ncbt_icp {
public:
    static box solve(box b, contractor const & ctc, SMTConfig & config);
};

class random_icp {
private:
    static bool random_bool();

public:
    static box solve(box b, contractor const & ctc, SMTConfig & config);
};

}  // namespace dreal
