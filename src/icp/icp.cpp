/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@mit.edu>

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

#include "icp/icp.h"
#include <algorithm>
#include <atomic>
#include <functional>
#include <limits>
#include <memory>
#include <mutex>
#include <random>
#include <thread>
#include <tuple>
#include <unordered_set>
#include <vector>
#include "constraint/constraint.h"
#include "icp/brancher.h"
#include "util/logging.h"
#include "util/mcts_node.h"
#include "util/scoped_vec.h"
#include "util/stat.h"
#include "util/thread_local.h"

using std::atomic_bool;
using std::cerr;
using std::cout;
using std::endl;
using std::get;
using std::mutex;
using std::ofstream;
using std::reference_wrapper;
using std::shared_ptr;
using std::thread;
using std::tuple;
using std::unordered_set;
using std::vector;

namespace dreal {

void output_solution(box const & b, SMTConfig & config, unsigned i) {
    if (i > 0) {
        cout << i << "-th ";
    }
    cout << "Solution:" << endl;
    cout << b << endl;
    if (config.nra_model && !config.nra_model_out.is_open()) {
        config.nra_model_out.open(config.nra_model_out_name.c_str(),
                                  ofstream::out | ofstream::trunc);
        if (config.nra_model_out.fail()) {
            cout << "Cannot create a file: " << config.nra_model_out_name << endl;
            exit(1);
        }
    }
    display(config.nra_model_out, b, false, true);
}

void prune(contractor & ctc, contractor_status & s) {
    try {
        ctc.prune(s);
    } catch (contractor_exception & e) {
        // Do nothing
    }
}

stacker::stacker(std::vector<box> & boxes, scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                 double prec)
    : m_stack(boxes), m_ctrs(ctrs), m_prec(prec), m_sol(boxes[0]) {
    m_best_score = std::numeric_limits<double>::max();
}

bool stacker::playout() {
    // clear the score vector
    // run samples on each box, of numbers based on current scores
    // update the scores on each box and put them in the score set
    m_score_board.clear();
    for (unsigned i = 0; i < m_stack.size(); i++) {
        double score = std::numeric_limits<double>::max();
        for (unsigned j = 0; j < 5; j++) {
            box sample = m_stack[i].sample_point();
            // DREAL_LOG_INFO<<"testing sample: "<<sample;
            double total_err = 0;
            for (auto ctr : m_ctrs) {
                assert(ctr->get_type() == constraint_type::Nonlinear);
                double err = ctr->eval_error(sample);
                DREAL_LOG_INFO << "playout current err: " << err << " obtained on ctr " << *ctr;
                if (err >= m_prec) {
                    total_err += err;
                }
            }
            // DREAL_LOG_INFO<<"finished evaluation on box "<<m_stack[i];
            if (total_err <= m_prec) {  // solution found
                update_solution(sample);
                DREAL_LOG_INFO << "best score right now " << total_err << "\t";
                return true;
            } else if (score > total_err) {
                score = total_err;
            } else {
                DREAL_LOG_INFO << "skipped a useless sample -- current error " << total_err << ">"
                               << " best score on board " << score;
            }
        }
        assert(score > m_prec);
        score = m_stack[i].test_score(score);
        m_score_board.push_back(score);
    }
    return false;
}

void stacker::update_budgets() {
    // assuming score board has been sorted
    m_sample_budgets.clear();
    assert(m_stack.size() == m_score_board.size());  // pop operations shouldn't mess with this
    unsigned total = m_stack.size();                 // total num of boxes
    double range = m_score_board[total - 1] - m_score_board[0];
    unsigned total_budget = 5 * total;  // 10 votes from each box, to be reassigned;
    for (unsigned i = 0; i < total; i++) {
        m_sample_budgets.emplace(i, total_budget * std::ceil(range / m_score_board[i]));
    }
}

box stacker::pop_best() {
    sort(m_score_board.begin(), m_score_board.end());
    update_budgets();
    unsigned index_of_best = 0;
    for (unsigned i = 0; i < m_stack.size(); i++) {
        DREAL_LOG_INFO << "score board 0: " << m_score_board[0];
        DREAL_LOG_INFO << "current score of box " << i << ": " << m_stack[i].get_score();
        if (m_stack[i].get_score() <= m_score_board[0]) {
            index_of_best = i;
            break;
        }
    }
    box result = m_stack[index_of_best];
    m_stack.erase(m_stack.begin() + index_of_best);
    if (m_best_score > m_score_board[0]) {
        m_best_score = m_score_board[0];
    }
    DREAL_LOG_INFO << "m_best_score: " << m_score_board[0];
    return result;
}

void stacker::push(box const & b) { m_stack.push_back(b); }

SizeBrancher sb;
BranchHeuristic & naive_icp::defaultHeuristic = sb;

void naive_icp::solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<shared_ptr<constraint>> const & ctrs, BranchHeuristic & brancher) {
    DREAL_THREAD_LOCAL static vector<box> solns;
    DREAL_THREAD_LOCAL static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(cs.m_box);
    do {
        DREAL_LOG_INFO << "naive_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        double const prec = cs.m_config.nra_delta_test ? 0.0 : cs.m_config.nra_precision;
        cs.m_box = box_stack.back();
        box_stack.pop_back();
        prune(ctc, cs);
        if (!cs.m_box.is_empty()) {
            vector<int> const sorted_dims =
                brancher.sort_branches(cs.m_box, ctrs, ctc.get_input(), cs.m_config, 1);
            if (sorted_dims.size() > 0) {
                int const i = sorted_dims[0];
                tuple<int, box, box> splits = cs.m_box.bisect_at(sorted_dims[0]);
                if (cs.m_config.nra_use_stat) {
                    cs.m_config.nra_stat.increase_branch();
                }
                box const & first = get<1>(splits);
                box const & second = get<2>(splits);
                assert(first.get_idx_last_branched() == i);
                assert(second.get_idx_last_branched() == i);
                if (second.is_bisectable(prec)) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                }
                if (cs.m_config.nra_proof) {
                    cs.m_config.nra_proof_out << "[branched on " << cs.m_box.get_name(i) << "]"
                                              << endl;
                }
            } else {
                cs.m_config.nra_found_soln++;
                if (cs.m_config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
                }
                if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                    break;
                }
                solns.push_back(cs.m_box);
            }
        }
    } while (box_stack.size() > 0);
    if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        cs.m_box = solns.back();
        return;
    } else {
        assert(!cs.m_box.is_empty() || box_stack.size() == 0);
        return;
    }
}

void multiprune_icp::solve(contractor & ctc, contractor_status & cs,
                           scoped_vec<shared_ptr<constraint>> const & ctrs,
                           BranchHeuristic & brancher, unsigned num_try) {
    prune(ctc, cs);
    if (cs.m_box.is_empty()) {
        return;
    }
    DREAL_THREAD_LOCAL static vector<box> solns;
    DREAL_THREAD_LOCAL static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(cs.m_box);
    do {
        DREAL_LOG_INFO << "multiprune_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        cs.m_box = box_stack.back();
        box_stack.pop_back();
        assert(!cs.m_box.is_empty());
        vector<int> const sorted_dims =
            brancher.sort_branches(cs.m_box, ctrs, ctc.get_input(), cs.m_config, num_try);
        if (sorted_dims.size() > 0) {
            int bisectdim = -1;
            box first(cs.m_box);
            box second(cs.m_box);
            box original(cs.m_box);
            double score = -std::numeric_limits<double>::lowest();
            for (int const dim : sorted_dims) {
                original = hull(first, second);
                assert(!original.is_empty());
                if (!original.is_bisectable_at(dim, cs.m_config.nra_precision)) {
                    continue;
                }
                tuple<int, box, box> const splits = original.bisect_at(dim);
                assert(get<0>(splits) >= 0);
                // Prune Left Box
                cs.m_box = get<1>(splits);
                prune(ctc, cs);
                box a1 = cs.m_box;
                // Prune Right Box
                cs.m_box = get<2>(splits);
                prune(ctc, cs);
                box a2 = cs.m_box;
                double const cscore = -a1.volume() - a2.volume();  // TODO(dzufferey): not a good
                                                                   // way as some intervals are
                                                                   // points (volume = 0)
                if (cscore > score || bisectdim == -1) {
                    first = a1;
                    second = a2;
                    bisectdim = dim;
                    score = cscore;
                } else {
                    a1.hull(a2);
                    first.intersect(a1);
                    second.intersect(a1);
                }
                if (first.is_empty() && second.is_empty()) {
                    cs.m_box.set_empty();
                    break;
                }
            }
            assert(bisectdim != -1);
            assert(first.get_idx_last_branched() == bisectdim);
            assert(second.get_idx_last_branched() == bisectdim);
            if (cs.m_config.nra_use_stat && !first.is_empty() && !second.is_empty()) {
                cs.m_config.nra_stat.increase_branch();
            }
            if (!second.is_empty() && second.is_bisectable()) {
                box_stack.push_back(second);
                if (!first.is_empty()) {
                    box_stack.push_back(first);
                }
            } else {
                if (!first.is_empty()) {
                    box_stack.push_back(first);
                }
                if (!second.is_empty()) {
                    box_stack.push_back(second);
                }
            }
            if (cs.m_config.nra_proof) {
                cs.m_config.nra_proof_out << "[branched on " << cs.m_box.get_name(bisectdim) << "]"
                                          << endl;
            }
        } else {
            cs.m_config.nra_found_soln++;
            if (cs.m_config.nra_multiple_soln > 1) {
                // If --multiple_soln is used
                output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
            }
            if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                break;
            } else {
                solns.push_back(cs.m_box);
            }
        }
    } while (box_stack.size() > 0);
    if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        cs.m_box = solns.back();
    } else {
        assert(!cs.m_box.is_empty() || box_stack.size() == 0);
    }
}

void multiheuristic_icp::solve(contractor & /* ctc */, contractor_status & /* cs */,
                               scoped_vec<shared_ptr<constraint>> const & /* ctrs */,
                               vector<reference_wrapper<BranchHeuristic>> /* heuristics */) {
    //     // don't use yet, since contractor is not yet threadsafe
    //     static vector<box> solns;
    //     solns.clear();
    //     mutex mu;
    //     box hull = cs.m_box;
    //     // hull is a shared box, that's used by all dothreads,
    //     // contains the intersection of the unions of the possible regions for each heuristic.
    //     // Therefore, any solution must be in hull.
    //     atomic_bool solved;
    //     unordered_set<shared_ptr<constraint>> all_used_constraints;
    //     prune(hull, ctc, config, all_used_constraints);
    //     vector<thread> threads;

    //     auto dothread = [&](BranchHeuristic & heuristic) {
    // #define PRUNEBOX(x) prune((x), ctc, config, used_constraints)
    //         DREAL_THREAD_LOCAL static unordered_set<shared_ptr<constraint>> used_constraints;
    //         DREAL_THREAD_LOCAL static vector<box> box_stack;
    //         DREAL_THREAD_LOCAL static vector<box> hull_stack;  // nth box in hull_stack contains
    //         hull of first n boxes in box_stack
    //         box_stack.clear();
    //         hull_stack.clear();
    //         used_constraints.clear();

    //         auto pushbox = [&](box b) {
    //             box_stack.push_back(b);  // copies hull into vector
    //             if (hull_stack.size() > 0) { b.hull(hull_stack.back()); }  // maintain hull_stack
    //             invariant
    //             hull_stack.push_back(b);
    //         };

    //         auto popbox = [&] {
    //             box b = box_stack.back();
    //             box_stack.pop_back();
    //             hull_stack.pop_back();
    //             return b;
    //         };

    //         mu.lock();
    //         box b = hull;
    //         mu.unlock();
    //         pushbox(b);
    //         do {
    //             b = popbox();
    //             mu.lock();
    //             b.intersect(hull);
    //             // TODO(clhuang): is contractor threadsafe???
    //             PRUNEBOX(b);
    //             mu.unlock();
    //             if (!b.is_empty()) {
    //                 vector<int> sorted_dims = heuristic.sort_branches(b, config.nra_precision);
    //                 if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
    //                 if (sorted_dims.size() > 0) {
    //                     int bisectdim = sorted_dims[0];
    //                     auto splits = b.bisect_at(bisectdim);
    //                     box first = get<1>(splits);
    //                     box second = get<2>(splits);
    //                     assert(bisectdim != -1);
    //                     assert(first.get_idx_last_branched() == bisectdim);
    //                     assert(second.get_idx_last_branched() == bisectdim);
    //                     if (second.is_bisectable()) {
    //                         pushbox(second);
    //                         pushbox(first);
    //                     } else {
    //                         pushbox(first);
    //                         pushbox(second);
    //                     }
    //                     if (config.nra_proof) {
    //                         config.nra_proof_out << "[branched on "
    //                             << b.get_name(bisectdim)
    //                             << "]" << endl;
    //                     }
    //                 } else {
    //                     mu.lock();
    //                     config.nra_found_soln++;
    //                     solns.push_back(b);
    //                     if (config.nra_multiple_soln > 1) {
    //                         // If --multiple_soln is used
    //                         output_solution(b, config, config.nra_found_soln);
    //                     }
    //                     if (config.nra_found_soln >= config.nra_multiple_soln) {
    //                         solved = true;
    //                         mu.unlock();
    //                         break;
    //                     }
    //                     mu.unlock();
    //                 }
    //             }
    //             // hull_stack, hopefully shrunk
    //             if (!hull_stack.empty()) {
    //                 mu.lock();
    //                 hull.intersect(hull_stack.back());
    //                 mu.unlock();
    //             }
    //         } while (box_stack.size() > 0 && !solved);
    //         mu.lock();
    //         if (config.nra_found_soln == 0) {
    //             solved = true;  // needed if unsat
    //             solns.push_back(b);  // would be empty
    //         }
    //         // update all_used_constraints
    //         for (auto x : used_constraints) {
    //             all_used_constraints.insert(x);
    //         }
    //         mu.unlock();

    // #undef PRUNEBOX
    //     };
    //     for (auto& heuristic : heuristics) {
    //         threads.push_back(thread(dothread, heuristic));
    //     }

    //     for (auto& t : threads) {
    //         t.join();
    //     }
    //     ctc.set_used_constraints(all_used_constraints);

    //     return solns.back();
}

void ncbt_icp::solve(contractor & ctc, contractor_status & cs) {
    static unsigned prune_count = 0;
    DREAL_THREAD_LOCAL static vector<box> box_stack;
    box_stack.clear();
    box_stack.push_back(cs.m_box);
    do {
        // Loop Invariant
        DREAL_LOG_INFO << "ncbt_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        cs.m_box = box_stack.back();
        try {
            ctc.prune(cs);
        } catch (contractor_exception & e) {
            // Do nothing
        }
        prune_count++;
        box_stack.pop_back();
        if (!cs.m_box.is_empty()) {
            // SAT
            tuple<int, box, box> splits = cs.m_box.bisect(cs.m_config.nra_precision);
            int const index = get<0>(splits);
            if (index >= 0) {
                box const & first = get<1>(splits);
                box const & second = get<2>(splits);
                assert(first.get_idx_last_branched() == index);
                assert(second.get_idx_last_branched() == index);
                if (cs.m_config.nra_use_stat) {
                    cs.m_config.nra_stat.increase_branch();
                }
                if (second.is_bisectable()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                }
            } else {
                break;
            }
        } else {
            // UNSAT (b is emptified by pruning operators)
            // If this bisect_var is not used in all used
            // constraints, this box is safe to be popped.
            DREAL_THREAD_LOCAL static unordered_set<Enode *> used_vars;
            used_vars.clear();
            for (auto used_ctr : cs.m_used_constraints) {
                auto this_used_vars = used_ctr->get_occured_vars();
                used_vars.insert(this_used_vars.begin(), this_used_vars.end());
            }
            while (box_stack.size() > 0) {
                int const bisect_var = box_stack.back().get_idx_last_branched();
                assert(bisect_var >= 0);
                // If this bisect_var is not used in all used
                // constraints, this box is safe to be popped.
                if (used_vars.find(cs.m_box.get_vars()[bisect_var]) != used_vars.end()) {
                    break;
                }
                box_stack.pop_back();
            }
        }
    } while (box_stack.size() > 0);
    DREAL_LOG_DEBUG << "prune count = " << prune_count;
}

random_icp::random_icp(contractor & ctc, std::mt19937_64::result_type const random_seed)
    : m_ctc(ctc), m_rg(random_seed), m_dist(0, 1) {}

void random_icp::solve(contractor_status & cs, double const precision) {
    DREAL_THREAD_LOCAL static vector<box> solns;
    DREAL_THREAD_LOCAL static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(cs.m_box);
    do {
        DREAL_LOG_INFO << "random_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        cs.m_box = box_stack.back();
        box_stack.pop_back();
        try {
            m_ctc.prune(cs);
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!cs.m_box.is_empty()) {
            tuple<int, box, box> splits = cs.m_box.bisect(precision);
            int const i = get<0>(splits);
            if (i >= 0) {
                box const & first = get<1>(splits);
                box const & second = get<2>(splits);
                if (random_bool()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                }
                if (cs.m_config.nra_proof) {
                    cs.m_config.nra_proof_out << "[branched on " << cs.m_box.get_name(i) << "]"
                                              << endl;
                }
            } else {
                cs.m_config.nra_found_soln++;
                if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                    break;
                }
                if (cs.m_config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
                }
                solns.push_back(cs.m_box);
            }
        }
    } while (box_stack.size() > 0);
    if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        cs.m_box = solns.back();
    } else {
        assert(!cs.m_box.is_empty() || box_stack.size() == 0);
    }
}

BranchHeuristic & mcts_icp::defaultHeuristic = sb;

void mcts_icp::solve(contractor & ctc, contractor_status & cs,
                     scoped_vec<shared_ptr<constraint>> const & ctrs, BranchHeuristic & brancher) {
    thread_local static vector<box> solns;
    solns.clear();

    icp_mcts_expander expander(ctc, cs, ctrs, brancher);
    icp_mcts_node * root = new icp_mcts_node(cs.m_box, &expander);

    do {
        DREAL_LOG_INFO << "mcts_icp::solve - loop"
                       << "\t"
                       << "graph Size = " << root->size();

        mcts_node * current = root;
        mcts_node * last = current;

        // Get leaf node
        while (!current->children()->empty()) {  // the node is an interior node
            last = current;
            current = current->select();
            // DREAL_LOG_INFO << "mcts_icp::solve() selected node " << current->id();
        }

        // DREAL_LOG_INFO << "mcts_icp::solve() expand";

        // generate leaf nodes and pick one
        last = current->expand();

        if (last != NULL) {
            // DREAL_LOG_INFO << "mcts_icp::solve() simulate";
            // simulate to end: sat or unsat
            last->simulate();

            if (last->is_solution()) {
                cs.m_config.nra_found_soln++;
                DREAL_LOG_INFO << "mcts_icp::solve() found solution";
                if (cs.m_config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
                }
                if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                    break;
                }
                solns.push_back(cs.m_box);
            }
        } else {
            DREAL_LOG_INFO << "mcts_icp::solve() end state";
            last = current;
        }

        // DREAL_LOG_INFO << "mcts_icp::solve() backpropagate";

        // backpropagate value
        current = last;
        while (current != NULL) {  // the node is in the graph
            current->backpropagate();
            current = current->parent();
        }
    } while (true);

    delete root;
}

BranchHeuristic & mcss_icp::defaultHeuristic = sb;

void mcss_icp::solve(contractor & ctc, contractor_status & cs,
                     scoped_vec<shared_ptr<constraint>> const & ctrs, BranchHeuristic & brancher) {
    DREAL_THREAD_LOCAL static vector<box> solns;
    DREAL_THREAD_LOCAL static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(cs.m_box);
    double const prec = cs.m_config.nra_delta_test ? 0.0 : cs.m_config.nra_precision;
    stacker stack(box_stack, ctrs, prec);
    double tmp_score;
    DREAL_LOG_INFO << "----new mcss instance----";
    do {
        DREAL_LOG_INFO << "mcss_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        if (!stack.playout()) {
            cs.m_box = stack.pop_best();
            tmp_score = stack.get_best_score();
            DREAL_LOG_INFO << "best score right now: " << tmp_score << "\t";
        } else {
            cs.m_config.nra_found_soln++;
            if (cs.m_config.nra_multiple_soln > 1) {
                // If --multiple_soln is used
                output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
            }
            cs.m_box = stack.get_solution();
            DREAL_LOG_INFO << "mcss found solution\n" << cs.m_box;
            if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                break;
            }
            solns.push_back(cs.m_box);
        }
        prune(ctc, cs);
        if (!cs.m_box.is_empty()) {
            vector<int> const sorted_dims =
                brancher.sort_branches(cs.m_box, ctrs, ctc.get_input(), cs.m_config, 1);
            if (sorted_dims.size() > 0) {
                int const i = sorted_dims[0];
                tuple<int, box, box> splits = cs.m_box.bisect_at(sorted_dims[0]);
                if (cs.m_config.nra_use_stat) {
                    cs.m_config.nra_stat.increase_branch();
                }
                box & first = get<1>(splits);
                box & second = get<2>(splits);
                assert(first.get_idx_last_branched() == i);
                assert(second.get_idx_last_branched() == i);
                if (second.is_bisectable(prec)) {
                    second.test_score(tmp_score);
                    stack.push(second);
                    first.test_score(tmp_score);
                    stack.push(first);
                } else {
                    first.test_score(tmp_score);
                    stack.push(first);
                    second.test_score(tmp_score);
                    stack.push(second);
                }
                if (cs.m_config.nra_proof) {
                    cs.m_config.nra_proof_out << "[branched on " << cs.m_box.get_name(i) << "]"
                                              << endl;
                }
            } else {
                cs.m_config.nra_found_soln++;
                if (cs.m_config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
                }
                if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                    break;
                }
                solns.push_back(cs.m_box);
            }
        }
    } while (stack.get_size() > 0);
    if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        cs.m_box = solns.back();
        return;
    } else {
        assert(!cs.m_box.is_empty() || box_stack.size() == 0);
        return;
    }
}

}  // namespace dreal
