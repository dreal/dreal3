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
#include <string>
#include <memory>
#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "contractor/contractor_status.h"
#include "icp/brancher.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"
#include <random>
#include <chrono>
#include <limits>
#include "util/logging.h"
#include "util/mcts_node.h"
#include "util/stat.h"
#include "constraint/constraint.h"

using std::vector;
using std::tuple;
using std::get;
using std::endl;
using std::numeric_limits;
using std::mt19937_64;
using std::chrono::system_clock;
using std::weak_ptr;

using dreal::icp_mcts_expander;
using dreal::mcts_node;

void icp_mcts_expander::expand(weak_ptr<mcts_node> node) {
    DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node)";

    icp_mcts_node * icp_node = NULL;
    shared_ptr<mcts_node> snode = shared_ptr<mcts_node>(node.lock());
    if ((icp_node = dynamic_cast<icp_mcts_node *>(&*snode))) {
        vector<shared_ptr<mcts_node>> * children = snode->children();

        m_cs.m_box = icp_node->get_box();

        // DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) pruning";
        // try {
        //     m_ctc.prune(m_cs);
        // } catch (contractor_exception & e) {
        //     // Do nothing
        // }

        DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) splitting";
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

                if (!second.is_empty()) {
		  DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) pruning split 2";
		  m_cs.m_box = second;
		  try {
		    m_ctc.prune(m_cs);
		  } catch (contractor_exception & e) {
		    // Do nothing
		  }
		  if(!second.is_empty()){
                    shared_ptr<mcts_node> child =
                        shared_ptr<mcts_node>(new icp_mcts_node(second, snode, this));
                    child->set_sp(child);
                    children->push_back(child);
		  }
                }
                if (!first.is_empty()) {
		  DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) pruning split 1";
		  m_cs.m_box = first;
		  try {
		    m_ctc.prune(m_cs);
		  } catch (contractor_exception & e) {
		    // Do nothing
		  }
		  if(!first.is_empty()){
                    shared_ptr<mcts_node> child =
		      shared_ptr<mcts_node>(new icp_mcts_node(first, snode, this));
                    child->set_sp(child);
                    children->push_back(child);
		  }
		}

                DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) split";

                if (m_cs.m_config.nra_proof) {
                    m_cs.m_config.nra_proof_out << "[branched on " << m_cs.m_box.get_name(i) << "]"
                                                << endl;
                }
            } else {
                std::cout << "mcts_expander::expand(mcts_node) found delta-sat";
                icp_node->set_solution(true);
            }
        }
    }
    DREAL_LOG_INFO << "icp_mcts_expander::expand(mcts_node) exit";
}
double icp_mcts_expander::simulate(weak_ptr<mcts_node> node) {
    return simulate_steps(node);

    // icp_mcts_node * icp_node = NULL;
    // int simulation_steps = 0;
    // box * last_non_empty_box = NULL;

    // double average_score = 0;
    // int num_simulations = 1;

    // for (int sim = 0; sim < num_simulations; sim++) {
    //     DREAL_LOG_INFO << "icp_mcts_expander::simulate() run = " << sim;
    //     if ((icp_node = dynamic_cast<icp_mcts_node *>(node))) {
    //         last_non_empty_box = new box(m_cs.m_box);
    //         m_cs.m_box = icp_node->get_box().sample_point();
    //         m_ctc.prune(m_cs);
    //         while (false && !m_cs.m_box.is_empty() &&
    //                !m_cs.m_box.is_point()) {  // either not unsat or not sat
    //                                           // vector<int> const sorted_dims =
    //             //     m_brancher.sort_branches(m_cs.m_box, m_ctrs, m_ctc.get_input(),
    //             //     m_cs.m_config, 1);
    //             // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() |sorted_dims| = "
    //             //                << sorted_dims.size();
    //             // if (sorted_dims.size() > 0) {
    //             //     int const i = sorted_dims.front();
    //             //     i;
    //             //     m_cs.m_box = m_cs.m_box.sample_dimension(i);
    //             //     delete last_non_empty_box;
    //             //     last_non_empty_box = new box(m_cs.m_box);
    //             //     try {
    //             //         // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() start pruning";
    //             //         m_ctc.prune(m_cs);
    //             //         // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() done pruning";
    //             //     } catch (contractor_exception & e) {
    //             //         // Do nothing
    //             //     }
    //             // } else
    //             if (!m_cs.m_box.is_point()) {  // need to pick upper or lower bound
    //                 vector<int> const dims = m_cs.m_box.non_point_dimensions();
    //                 static mt19937_64 rg(system_clock::now().time_since_epoch().count());

    //                 // find minimum width dimension
    //                 double min_width = numeric_limits<double>::max();
    //                 int i = -1;
    //                 for (auto dim : dims) {
    //                     ibex::Interval interval = m_cs.m_box[dim];
    //                     double width = interval.diam();
    //                     if (width < min_width  //|| rg() < rg.max()/2
    //                         ) {
    //                         min_width = width;
    //                         i = dim;
    //                     }
    //                 }
    //                 // if( rg() < rg.max()/2){

    //                 // box prev(m_cs.m_box);
    //                 // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() found non-point ";
    //                 // m_cs.m_box = m_cs.m_box.set_dimension_lb(i);

    //                 // try {
    //                 //     // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() start pruning";
    //                 //     m_ctc.prune(m_cs);
    //                 //     // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() done pruning";
    //                 // } catch (contractor_exception & e) {
    //                 //     // Do nothing
    //                 // }

    //                 // if (m_cs.m_box.is_empty()) {
    //                 //     " << i;
    //                 //     m_cs.m_box = prev.set_dimension_ub(i);
    //                 //     // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() after\n" <<
    //                 //     m_cs.m_box;
    //                 //     delete last_non_empty_box;
    //                 last_non_empty_box = new box(m_cs.m_box);
    //                 //     try {
    //                 //         m_ctc.prune(m_cs);
    //                 //     } catch (contractor_exception & e) {
    //                 //         // Do nothing
    //                 //     }
    //                 // }
    //                 // } else {
    //                 box prev(m_cs.m_box);
    //                 DREAL_LOG_INFO << "icp_mcts_simulator::simulate() found non-point ";
    //                 m_cs.m_box = m_cs.m_box =
    //                     m_cs.m_box.sample_dimension(i);  // m_cs.m_box.set_dimension_ub(i);
    //                 try {
    //                     DREAL_LOG_INFO << "icp_mcts_simulator::simulate() start pruning";
    //                     m_ctc.prune(m_cs);
    //                     DREAL_LOG_INFO << "icp_mcts_simulator::simulate() done pruning";
    //                 } catch (contractor_exception & e) {
    //                     // Do nothing
    //                 }

    //                 // if (m_cs.m_box.is_empty()) {
    //                 //     " << i;
    //                 //     m_cs.m_box = prev.set_dimension_lb(i);
    //                 //     m_cs.m_box;
    //                 //     delete last_non_empty_box;
    //                 //     last_non_empty_box = new box(m_cs.m_box);
    //                 //     try {
    //                 //         m_ctc.prune(m_cs);
    //                 //     } catch (contractor_exception & e) {
    //                 //         // Do nothing
    //                 //     }
    //                 // }
    //             }
    //         }
    //     }
    //     if (!m_cs.m_box.is_empty() && m_cs.m_box.is_point()) {
    //         std::cout << "found sat" << std::endl;
    //         // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() found sat";
    //         icp_mcts_node * icp_node = NULL;
    //         if ((icp_node = dynamic_cast<icp_mcts_node *>(node))) {
    //             icp_node->add_sat_simulation_box(m_cs.m_box);
    //         }
    //         node->set_solution(true);
    //     }
    //     average_score +=
    //         (m_cs.m_box.is_empty() ? -1.0 * constraint_error(*last_non_empty_box) : 1.0);
    // }
    // return average_score / num_simulations;
}

int get_step(std::string var, bool & at_start) {
    int first_underscore = var.find_first_of("_");
    int last_underscore = var.find_last_of("_");
    // DREAL_LOG_INFO << first_underscore << " " << last_underscore;
    int step = -1;
    if (first_underscore == last_underscore) {  // is a time_x variable
        step = std::stoi(var.substr(first_underscore + 1));
        at_start = false;
    } else {  // is a fun_x_t variable
        int second_last_underscore = var.substr(0, last_underscore - 1).rfind("_");
        //   DREAL_LOG_INFO << second_last_underscore << " " << var.substr(second_last_underscore+1,
        //   last_underscore-2) << " " << var.substr(last_underscore+1);
        step = std::stoi(var.substr(second_last_underscore + 1, last_underscore - 2));

        if (std::strcmp(var.substr(last_underscore + 1).c_str(), "t") == 0)
            at_start = false;
        else
            at_start = true;
    }
    return step;
}

double icp_mcts_expander::simulate_steps(weak_ptr<mcts_node> node) {
    icp_mcts_node * icp_node = NULL;
    // int simulation_steps = 0;
    box * last_non_empty_box = NULL;

    double average_score = 0;
    int num_simulations = 1;

    shared_ptr<mcts_node> snode = shared_ptr<mcts_node>(node.lock());

    for (int sim = 0; sim < num_simulations; sim++) {
        DREAL_LOG_INFO << "icp_mcts_expander::simulate() run = " << sim;
        if ((icp_node = dynamic_cast<icp_mcts_node *>(&*snode))) {
            m_cs.m_box = icp_node->get_box();
            while (!m_cs.m_box.is_empty() &&
                   !m_cs.m_box.is_point()) {   // either not unsat or not sat
                if (!m_cs.m_box.is_point()) {  // need to pick value for an interval dimension
                    vector<int> const dims = m_cs.m_box.non_point_dimensions();
                    static mt19937_64 rg(system_clock::now().time_since_epoch().count());

                    // find earliest interval
                    // double min_width = numeric_limits<double>::max();
                    int min_step = numeric_limits<int>::max();
                    // bool min_at_start = false;
                    int i = 0;
                    bool got_time = false;
                    for (auto dim : dims) {
                        ibex::Interval interval = m_cs.m_box[dim];
                        // double width = interval.diam();
                        std::string name = m_cs.m_box.get_name(dim);
                        bool at_start;
                        int step = get_step(name, at_start);
                        bool is_time =
                            m_cs.m_box.is_time_variable(dim) && name.find("_") == name.rfind("_");
                         DREAL_LOG_INFO << "i = " << i << " " << name << " step = " << step
					<< "at_start = " << at_start;// << " width = " << width;
                        if (step < min_step) {
                            min_step = step;
                            // min_at_start = at_start;
                            // min_width = width;
                            i = dim;
                        } else if (step <= min_step && is_time && !got_time) {
                            got_time = true;
                            min_step = step;
                            // min_at_start = at_start;
                            // min_width = width;
                            i = dim;
                        }
                    }
                    box prev(m_cs.m_box);
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() found non-point ";
                    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() setting dimension = "
                                   << m_cs.m_box.get_name(i);
                    // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() before\n" << m_cs.m_box;
                    m_cs.m_box = m_cs.m_box =
                        m_cs.m_box.sample_dimension(i);  // m_cs.m_box.set_dimension_ub(i);
                    // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() after\n" << m_cs.m_box;
                    last_non_empty_box = new box(m_cs.m_box);

                    try {
                        DREAL_LOG_INFO << "icp_mcts_simulator::simulate() start pruning";
                        m_ctc.prune(m_cs);
                        DREAL_LOG_INFO << "icp_mcts_simulator::simulate() done pruning";
                    } catch (contractor_exception & e) {
                        // Do nothing
                    }
                }
            }
        }
        average_score +=
            (m_cs.m_box.is_empty() ? -1.0 * log(constraint_error(*last_non_empty_box)) : 1.0);

        if (!m_cs.m_box.is_empty() && m_cs.m_box.is_point()) {
            // std::cout << "found sat" << std::endl;
            // DREAL_LOG_INFO << "icp_mcts_simulator::simulate() found sat";
            icp_mcts_node * icp_node = NULL;
            if ((icp_node = dynamic_cast<icp_mcts_node *>(&*snode))) {
                icp_node->add_sat_simulation_box(m_cs.m_box);
            }
            snode->set_solution(true);
            break;
        }
    }
    DREAL_LOG_INFO << "icp_mcts_simulator::simulate() exit, count = " << snode.use_count();
    return average_score / num_simulations;
}

double icp_mcts_expander::constraint_error(box b) const {
    DREAL_LOG_INFO << "icp_mcts_expander::constraint_error(box)";
    double error = 0.0;
    nonlinear_constraint * nc = NULL;
    for (auto ctr : m_ctrs) {
        if ((nc = dynamic_cast<nonlinear_constraint *>(ctr.get()))) {
            // DREAL_LOG_INFO << "icp_mcts_expander::constraint_error(box) ctr = " << *nc;
            error += nc->eval_error(b);
        }
    }

    DREAL_LOG_INFO << "icp_mcts_expander::constraint_error(box) error = " << error;
    return error;
}
