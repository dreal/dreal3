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

#include "util/mcts_expander.h"

#include <assert.h>
#include <stddef.h>
#include <iostream>
#include <tuple>
#include <vector>

#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "contractor/contractor_status.h"
#include "icp/brancher.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/mcts_node.h"
#include "util/stat.h"

using std::vector;
using std::tuple;
using std::get;
using std::endl;
using dreal::icp_mcts_expander;
using dreal::mcts_node;

void icp_mcts_expander::expand(mcts_node * node) {
    // DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node)";

    icp_mcts_node * icp_node = NULL;

    if ((icp_node = dynamic_cast<icp_mcts_node *>(node))) {
        vector<mcts_node *> * children = node->children();

        m_cs.m_box = icp_node->get_box();
        try {
            m_ctc.prune(m_cs);
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!m_cs.m_box.is_empty()) {
            vector<int> const sorted_dims =
                m_brancher.sort_branches(m_cs.m_box, m_ctrs, m_ctc.get_input(), m_cs.m_config, 1);
            if (sorted_dims.size() > 0) {
                int const i = sorted_dims[0];
                tuple<int, box, box> splits = m_cs.m_box.bisect_at(sorted_dims[0]);
                if (m_cs.m_config.nra_use_stat) {
                    m_cs.m_config.nra_stat.increase_branch();
                }
                box const & first = get<1>(splits);
                box const & second = get<2>(splits);
                assert(first.get_idx_last_branched() == i);
                assert(second.get_idx_last_branched() == i);

                children->push_back(new icp_mcts_node(second, node, this));
                children->push_back(new icp_mcts_node(first, node, this));

                //      DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) split";

                if (m_cs.m_config.nra_proof) {
                    m_cs.m_config.nra_proof_out << "[branched on " << m_cs.m_box.get_name(i) << "]"
                                                << endl;
                }
            } else {
                icp_node->set_solution(true);
            }
        }
    }
    DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) exit";
}

double icp_mcts_expander::simulate(mcts_node * node) {
    icp_mcts_node * icp_node = NULL;
    int simulation_steps = 0;

    if ((icp_node = dynamic_cast<icp_mcts_node *>(node))) {
        m_cs.m_box = icp_node->get_box();
        while (!m_cs.m_box.is_empty() && !m_cs.m_box.is_point()) {  // either not unsat or not sat
            vector<int> const sorted_dims =
                m_brancher.sort_branches(m_cs.m_box, m_ctrs, m_ctc.get_input(), m_cs.m_config, 1);
            DREAL_LOG_INFO << "icp_mcts_simulator::simulate() |sorted_dims| = "
                           << sorted_dims.size();
            if (sorted_dims.size() > 0) {
                int const i = sorted_dims.front();
                DREAL_LOG_INFO << "icp_mcts_simulator::simulate() sampling dimension = " << i;
                DREAL_LOG_INFO << "icp_mcts_simulator::simulate() before\n" << m_cs.m_box;
                m_cs.m_box = m_cs.m_box.sample_dimension(i);
                DREAL_LOG_INFO << "icp_mcts_simulator::simulate() after\n" << m_cs.m_box;

                try {
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() start pruning";
                    m_ctc.prune(m_cs);
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() done pruning";
                } catch (contractor_exception & e) {
                    // Do nothing
                }
            } else if (!m_cs.m_box.is_point()) {  // need to pick upper or lower bound
                vector<int> const dims = m_cs.m_box.non_point_dimensions();
                int const i = dims.front();
                box prev(m_cs.m_box);
                DREAL_LOG_INFO << "icp_mcts_simulator::simulate() found non-point ";
                DREAL_LOG_INFO << "icp_mcts_simulator::simulate() setting dimension lb = " << i;
                DREAL_LOG_INFO << "icp_mcts_simulator::simulate() before\n" << m_cs.m_box;
                m_cs.m_box = m_cs.m_box.set_dimension_lb(i);
                DREAL_LOG_INFO << "icp_mcts_simulator::simulate() after\n" << m_cs.m_box;

                try {
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() start pruning";
                    m_ctc.prune(m_cs);
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() done pruning";
                } catch (contractor_exception & e) {
                    // Do nothing
                }

                if (m_cs.m_box.is_empty()) {
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() setting dimension ub = " << i;
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() before\n" << prev;
                    m_cs.m_box = prev.set_dimension_ub(i);
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() after\n" << m_cs.m_box;

                    try {
                        DREAL_LOG_INFO << "icp_mcts_simulator::simulate() start pruning";
                        m_ctc.prune(m_cs);
                        DREAL_LOG_INFO << "icp_mcts_simulator::simulate() done pruning";
                    } catch (contractor_exception & e) {
                        // Do nothing
                    }
                }
            }
            simulation_steps++;
        }
        if (m_cs.m_box.is_point()) {
            std::cout << "found sat" << std::endl;
            DREAL_LOG_INFO << "icp_mcts_simulator::simulate() found sat";
            icp_mcts_node * icp_node = NULL;
            if ((icp_node = dynamic_cast<icp_mcts_node *>(node))) {
                icp_node->add_sat_simulation_box(m_cs.m_box);
            }
            node->set_solution(true);
        }
    }
    return (m_cs.m_box.is_empty() ? -1.0 / static_cast<double>(simulation_steps) : 1.0);
}
