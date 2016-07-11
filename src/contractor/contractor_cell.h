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
#include <unordered_map>
#include <vector>
#include <cassert>
#include <initializer_list>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "./config.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "contractor/contractor_common.h"
#include "contractor/contractor_status.h"

namespace dreal {
// Base Cell
class contractor_cell {
protected:
    contractor_kind m_kind;
    // Static overapproximation of the input vector, which should be
    // computed in construction time.
    //
    // "m_input[i] == 1" means that the i-th varialbe is an input to
    // the contractor. It implies that any changes on i-th variable
    // should trigger another run of the contractor in the fixpoint
    // computation.
    ibex::BitSet m_input;

public:
    explicit contractor_cell(contractor_kind kind) : m_kind(kind) { }
    contractor_cell(contractor_kind kind, unsigned n)
        : m_kind(kind), m_input(ibex::BitSet::empty(n)) { }
    virtual ~contractor_cell() noexcept { }
    ibex::BitSet get_input() const { return m_input; }
    virtual void prune(contractor_status & cs) = 0;
    virtual std::ostream & display(std::ostream & out) const = 0;
};

std::ostream & operator<<(std::ostream & out, contractor_cell const & c);
}  // namespace dreal
