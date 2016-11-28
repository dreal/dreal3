/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@mit.edu>

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

#pragma once

#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"

struct SMTConfig;

namespace dreal {
class box;
class contractor;
class contractor_status;

void output_solution(box const & b, SMTConfig & config, unsigned i);
void prune(contractor & ctc, contractor_status & s);
}  // namespace dreal
