/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, the dReal Team

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
#include <algorithm>
#include <cassert>
#include <initializer_list>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include "./dreal_config.h"
#include "constraint/constraint.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"

namespace dreal {
enum class contractor_kind {
    ID,
    SEQ,
    OR,
    ITE,
    FP,
    PARALLEL_ALL,
    PARALLEL_ANY,
    PSEQ,
    TIMEOUT,
    TRY,
    TRY_OR,
    JOIN,
    IBEX_FWDBWD,
    IBEX_NEWTON,
    IBEX_HC4,
#ifdef USE_CLP
    IBEX_POLYTOPE,
#endif
    INT,
    EVAL,
    CACHE,
    SAMPLE,
    AGGRESSIVE,
    FORALL,
    THROW,
    THROW_IF_EMPTY,
    EMPTY,
    DEBUG,
#ifdef SUPPORT_ODE
    CAPD_FULL,
    CAPD_SIMPLE,
    CAPD_POINT,
#endif
};

#ifdef SUPPORT_ODE
enum class ode_direction { FWD, BWD };

std::ostream & operator<<(std::ostream & out, ode_direction const & d);
#endif

class contractor_exception : public std::runtime_error {
public:
    explicit contractor_exception(const std::string & what_arg) : runtime_error(what_arg) {}
    explicit contractor_exception(const char * what_arg) : runtime_error(what_arg) {}
};

}  // namespace dreal
