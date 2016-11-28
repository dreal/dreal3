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

#include <assert.h>
#include <math.h>
#include <limits>

#include "util/logging.h"
#include "util/mcts_expander.h"
#include "util/mcts_node.h"

using dreal::mcts_node;
using dreal::icp_mcts_node;
using std::numeric_limits;

mcts_node * mcts_node::select() {
    mcts_node * selected = NULL;
    double max_score = numeric_limits<double>::lowest();

    // UCT score
    for (auto child : m_children_list) {
        // DREAL_LOG_INFO << m_value << " " << m_visits << " " << child->visits() << " " <<
        // max_score;
        double score = m_value + UCT_COEFFICIENT * sqrt(log(m_visits) / child->visits());
        child->set_score(score);
        // DREAL_LOG_INFO << "mcts_node::select(" << m_id
        //             << ") set score(" << child->id() << ") = " << score;
        if (score > max_score) {
            selected = child;
            max_score = score;
        }
    }

    DREAL_LOG_INFO << "mcts_node::select(" << m_id << ") = " << selected->id();
    m_visits++;
    return selected;
}

mcts_node * icp_mcts_node::expand() {
    DREAL_LOG_INFO << "mcts_node::expand(" << m_id << ")";
    assert(m_children_list.empty());

    m_visits++;

    if (!m_terminal) {
        m_expander->expand(this);
        m_size = m_children_list.size();

        DREAL_LOG_INFO << "mcts_node::expand(" << m_id << ")"
                       << " Got num children: " << m_children_list.size();

        for (auto child : m_children_list) {
            // DREAL_LOG_INFO << "child: " << child->id();
            child->inc_visits();
        }

        if (m_children_list.empty()) {
            m_terminal = true;
        }
    }

    return (m_terminal ? NULL : m_children_list[0]);
}

double mcts_node::simulate() {
    DREAL_LOG_INFO << "mcts_node::simulate(" << m_id << ")";

    if (m_terminal) {
        m_value = (m_is_solution ? 1.0 : -1.0);
    } else {
        // TODO(dan)
        m_value = m_expander->simulate(this);
    }
    return m_value;
}

void mcts_node::backpropagate() {
    // DREAL_LOG_INFO << "mcts_node::backpropagate(" << m_id << ") size = " << m_size;

    if (!m_children_list.empty()) {
        m_size = 0;
        m_value = 0;
        for (auto child : m_children_list) {
            m_size += child->size() + 1;
            m_value += child->value();
        }
        m_value /= m_children_list.size();  // average value backprop
    }
    //  DREAL_LOG_INFO << "mcts_node::backpropagate(" << m_id << ") size = " << m_size;
}
