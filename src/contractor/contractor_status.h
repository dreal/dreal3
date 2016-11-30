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
#include <unordered_set>
#include <utility>
#include <vector>

#include "constraint/constraint.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"

namespace dreal {
/// contractor_status class is passed to a contractor::prune method as
/// a reference. A contractor updates a given contractor status during
/// a pruning step.
class contractor_status {
public:
    /// The current box to prune. Most of contractors are updating
    /// this member.
    box m_box;
    /// Some of contractors return a set of boxes in their pruning
    /// processes. The first one is saved in m_box, the rest will be
    /// saved in m_box_stack. When a contractor_status is returned to
    /// an ICP layer, its m_box_stack will be passed to the ICP stack.
    std::vector<box> m_box_stack;
    // "m_output[i] == 1" means that the value of the i-th variable is
    // changed after running the contractor.
    ibex::BitSet m_output;
    std::unordered_set<std::shared_ptr<constraint>> m_used_constraints;
    SMTConfig & m_config;
    Egraph & m_egraph;

public:
    contractor_status(box const & b, std::vector<box> const & box_stack,
                      ibex::BitSet const & output,
                      std::unordered_set<std::shared_ptr<constraint>> const & used_constraints,
                      SMTConfig & config, Egraph & eg)
        : m_box(b),
          m_box_stack(box_stack),
          m_output(output),
          m_used_constraints(used_constraints),
          m_config(config),
          m_egraph(eg) {}
    contractor_status(SMTConfig & config, Egraph & eg)
        : m_box({}), m_config(config), m_egraph(eg) {}
    contractor_status(contractor_status const & cs, box const & b)
        : m_box(b),
          m_output(ibex::BitSet::empty(b.size())),
          m_config(cs.m_config),
          m_egraph(cs.m_egraph) {}
    contractor_status(box const & b, SMTConfig & config, Egraph & eg)
        : m_box(b), m_output(ibex::BitSet::empty(b.size())), m_config(config), m_egraph(eg) {}

    // reset
    void reset(contractor_status & cs) {
        m_box = cs.m_box;
        m_box_stack = cs.m_box_stack;
        m_output = cs.m_output;
        m_used_constraints = cs.m_used_constraints;
    }
    void join(contractor_status const & cs) {
        m_box.hull(cs.m_box);
        m_box_stack.insert(std::end(m_box_stack), std::begin(cs.m_box_stack),
                           std::end(cs.m_box_stack));
        m_output.union_with(cs.m_output);
        std::unordered_set<std::shared_ptr<constraint>> const & used_ctrs = cs.m_used_constraints;
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
    }
};

/// contractor_status_guard provide a way to 'temporarily' clear out a
/// contractor_status' output and used_constraints members. It works as follows:
///
/// {
///     contractor_status_guard csg(cs);  // save cs' m_output and m_used_constraints;
///
///     assert(cs.m_output.empty());
///     assert(cs.m_used_constraints.empty());
///     ...
///     ctr.prune(cs);  // pruning update cs' m_output and m_used_constraints
///     ...
/// }
/// // csg is destroyed and its destruction joins old and new values of m_output and
/// // m_used_constraints
class contractor_status_guard {
private:
    contractor_status & m_cs_ref;
    ibex::BitSet m_old_output;
    std::unordered_set<std::shared_ptr<constraint>> m_old_used_constraints;

public:
    // Save output and used_constraints, and clear them
    explicit contractor_status_guard(contractor_status & cs)
        : m_cs_ref(cs), m_old_output(cs.m_output), m_old_used_constraints() {
        cs.m_output.clear();
        cs.m_used_constraints.swap(m_old_used_constraints);
    }
    ~contractor_status_guard() {
        // Add saved output and used_constraints back to the m_cs_ref
        m_cs_ref.m_output.swap(m_old_output);
        m_cs_ref.m_used_constraints.swap(m_old_used_constraints);
        if (!m_old_output.empty()) {
            m_cs_ref.m_output.union_with(m_old_output);
            m_cs_ref.m_used_constraints.insert(m_old_used_constraints.begin(),
                                               m_old_used_constraints.end());
        }
    }
};
}  // namespace dreal
