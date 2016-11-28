/*********************************************************************
Author: Daniel Bryce <dbryce@sift.net>

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

#include <memory>
#include <vector>

#include "contractor/contractor.h"
#include "icp/brancher.h"
#include "util/mcts_node.h"

namespace dreal {
class mcts_node;
class BranchHeuristic;
class constraint;
class contractor;
class contractor_status;
template <typename T>
class scoped_vec;

class mcts_expander {
public:
    virtual void expand(mcts_node * node) = 0;
    virtual double simulate(mcts_node * node) = 0;
};

class icp_mcts_expander : public mcts_expander {
public:
    icp_mcts_expander(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                      BranchHeuristic & brancher)
        : m_ctc(ctc), m_cs(cs), m_ctrs(ctrs), m_brancher(brancher) {}
    virtual void expand(mcts_node * node);
    virtual double simulate(mcts_node * node);

private:
    contractor & m_ctc;
    contractor_status & m_cs;
    scoped_vec<std::shared_ptr<constraint>> const & m_ctrs;
    BranchHeuristic & m_brancher;
};
}  // namespace dreal
