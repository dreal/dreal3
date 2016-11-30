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
#include <functional>
#include <initializer_list>
#include <ostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "contractor/contractor.h"
#include "contractor/contractor_cell.h"

namespace dreal {
// contractor_fixpoint
// Repeatedly applying the contractor while the condition is met
class contractor_fixpoint : public contractor_cell {
public:
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        contractor const & c);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        std::initializer_list<contractor> const & clist);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec);
    // contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
    //                     std::initializer_list<std::vector<contractor>> const & cvec_list);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::function<bool(box const &, box const &)> m_term_cond;
    std::vector<contractor> m_clist;
    box m_old_box;
    std::unordered_map<int, std::unordered_set<int>>
        m_dep_map;  // m_dep_map[v] = set of contractors depending on v (input)

    void init();
    // Naive fixedpoint algorithm
    void naive_fixpoint_alg(contractor_status & cs);
    // Worklist fixedpoint algorithm
    void worklist_fixpoint_alg(contractor_status & cs);
    void build_deps_map();
};
}  // namespace dreal
