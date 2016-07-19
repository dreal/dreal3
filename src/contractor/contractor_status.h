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

#include <unordered_set>
#include "opensmt/smtsolvers/SMTConfig.h"
#include "constraint/constraint.h"
#include "util/box.h"

namespace dreal {
class contractor_status {
public:
    box m_box;
    // "m_output[i] == 1" means that the value of the i-th variable is
    // changed after running the contractor.
    ibex::BitSet m_output;
    std::unordered_set<std::shared_ptr<constraint>> m_used_constraints;
    SMTConfig & m_config;

public:
    explicit contractor_status(SMTConfig & config)
        : m_box({}), m_config(config) { }
    contractor_status(box const & b, SMTConfig & config)
        : m_box(b), m_output(ibex::BitSet::empty(b.size())), m_config(config) { }
    contractor_status(box const & b,
                      ibex::BitSet const & output,
                      std::unordered_set<std::shared_ptr<constraint>> const & used_constraints,
                      SMTConfig & config)
        : m_box(b), m_output(output), m_used_constraints(used_constraints), m_config(config) { }

    // reset
    void reset(contractor_status & cs) {
        m_box = cs.m_box;
        m_output = cs.m_output;
        m_used_constraints = cs.m_used_constraints;
    }
    void join(contractor_status const & cs) {
        m_output.union_with(cs.m_output);
        std::unordered_set<std::shared_ptr<constraint>> const & used_ctrs = cs.m_used_constraints;
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        m_box.hull(cs.m_box);
    }
};

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
            m_cs_ref.m_used_constraints.insert(m_old_used_constraints.begin(), m_old_used_constraints.end());
        }
    }
};

}  // namespace dreal
