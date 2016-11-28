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

#pragma once
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
}  // namespace dreal
