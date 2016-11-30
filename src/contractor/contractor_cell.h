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
#include "contractor/contractor_kind.h"
#include "contractor/contractor_status.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"

namespace dreal {
// Base Cell
class contractor_cell {
public:
    explicit contractor_cell(contractor_kind kind) : m_kind{kind} {}
    contractor_cell(contractor_kind kind, unsigned n)
        : m_kind{kind}, m_input{ibex::BitSet::empty(n)} {}
    contractor_cell(contractor_kind kind, ibex::BitSet const & input)
        : m_kind{kind}, m_input{input} {}
    contractor_cell(contractor_kind kind, std::initializer_list<ibex::BitSet> const & inputs)
        : m_kind{kind}, m_input{join_bitsets(inputs)} {}
    contractor_kind const & get_kind() const { return m_kind; }
    ibex::BitSet const & get_input() const { return m_input; }
    virtual void prune(contractor_status & cs) = 0;
    virtual std::ostream & display(std::ostream & out) const = 0;

private:
    contractor_kind const m_kind;
    // Static overapproximation of the input vector, which should be
    // computed in construction time.
    //
    // "m_input[i] == 1" means that the i-th varialbe is an input to
    // the contractor. It implies that any changes on i-th variable
    // should trigger another run of the contractor in fixed-point
    // computation.
    ibex::BitSet const m_input;
    static ibex::BitSet join_bitsets(std::initializer_list<ibex::BitSet> const & inputs);
};
std::ostream & operator<<(std::ostream & out, contractor_cell const & c);
}  // namespace dreal
