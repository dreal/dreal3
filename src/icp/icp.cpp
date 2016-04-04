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

#include <algorithm>
#include <random>
#include <tuple>
#include <mutex>
#include <unordered_set>
#include <vector>
#include <atomic>
#include "icp/icp.h"
#include "icp/brancher.h"
#include "util/logging.h"
#include "util/scoped_vec.h"
#include "util/stat.h"

using std::cerr;
using std::cout;
using std::endl;
using std::get;
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
        config.nra_model_out.open(config.nra_model_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
        if (config.nra_model_out.fail()) {
            cout << "Cannot create a file: " << config.nra_model_out_name << endl;
            exit(1);
        }
    }
    display(config.nra_model_out, b, false, true);
}

void prune(box & b, contractor & ctc, SMTConfig & config, std::unordered_set<std::shared_ptr<constraint>> & used_constraints) {
    try {
        ctc.prune(b, config);
        auto this_used_constraints = ctc.used_constraints();
        used_constraints.insert(this_used_constraints.begin(), this_used_constraints.end());
        if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
    } catch (contractor_exception & e) {
        // Do nothing
    }
}

box naive_icp::solve(box b, contractor & ctc, SMTConfig & config,
        BranchHeuristic& brancher) {
    thread_local static std::unordered_set<std::shared_ptr<constraint>> used_constraints;
    used_constraints.clear();
    thread_local static vector<box> solns;
    thread_local static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(b);
    do {
        DREAL_LOG_INFO << "naive_icp::solve - loop"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        box_stack.pop_back();
        prune(b, ctc, config, used_constraints);
        if (!b.is_empty()) {
            if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
            vector<int> sorted_dims = brancher.sort_branches(b, config.nra_precision);
            if (sorted_dims.size() > 0) {
                int const i = sorted_dims[0];
                tuple<int, box, box> splits = b.bisect_at(sorted_dims[0]);
                box const & first  = get<1>(splits);
                box const & second = get<2>(splits);
                assert(first.get_idx_last_branched() == i);
                assert(second.get_idx_last_branched() == i);
                if (second.is_bisectable()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                }
                if (config.nra_proof) {
                    config.nra_proof_out << "[branched on "
                                         << b.get_name(i)
                                         << "]" << endl;
                }
            } else {
                config.nra_found_soln++;
                if (config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(b, config, config.nra_found_soln);
                }
                if (config.nra_found_soln >= config.nra_multiple_soln) {
                    break;
                }
                solns.push_back(b);
            }
        }
    } while (box_stack.size() > 0);
    ctc.set_used_constraints(used_constraints);
    if (config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        assert(!b.is_empty() || box_stack.size() == 0);
        return b;
    }
}

box multiprune_icp::solve(box b, contractor & ctc, SMTConfig & config, BranchHeuristic& brancher, int num_try) {
#define PRUNEBOX(x) prune((x), ctc, config, used_constraints)
    thread_local static std::unordered_set<std::shared_ptr<constraint>> used_constraints;
    used_constraints.clear();
    thread_local static vector<box> solns;
    thread_local static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    PRUNEBOX(b);
    box_stack.push_back(b);
    do {
        DREAL_LOG_INFO << "multiprune_icp::solve - loop"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        box_stack.pop_back();
        if (!b.is_empty()) {
            vector<int> sorted_dims = brancher.sort_branches(b, config.nra_precision);
            if (sorted_dims.size() > num_try) {
                sorted_dims = vector<int>(sorted_dims.begin(), sorted_dims.begin()+num_try);
            }

            if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
            if (sorted_dims.size() > 0) {
                int bisectdim = -1;
                box first = b;
                box second = b;
                double score = -INFINITY;
                for (int dim : sorted_dims) {
                    tuple<int, box, box> splits = b.bisect_at(dim);
                    box a1 = get<1>(splits);
                    box a2 = get<2>(splits);
                    PRUNEBOX(a1);
                    PRUNEBOX(a2);
                    double cscore = -a1.volume() * a2.volume();
                    if (cscore > score || bisectdim == -1) {
                        first.hull(second);
                        a1.intersect(first);
                        a2.intersect(first);
                        first = a1;
                        second = a2;
                        bisectdim = dim;
                        score = cscore;
                    } else {
                        a1.hull(a2);
                        first.intersect(a1);
                        second.intersect(a1);
                    }
                }
                assert(bisectdim != -1);
                assert(first.get_idx_last_branched() == bisectdim);
                assert(second.get_idx_last_branched() == bisectdim);
                if (second.is_bisectable()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                }
                if (config.nra_proof) {
                    config.nra_proof_out << "[branched on "
                                         << b.get_name(bisectdim)
                                         << "]" << endl;
                }
            } else {
                config.nra_found_soln++;
                if (config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(b, config, config.nra_found_soln);
                }
                if (config.nra_found_soln >= config.nra_multiple_soln) {
                    break;
                }
                solns.push_back(b);
            }
        }
    } while (box_stack.size() > 0);
    ctc.set_used_constraints(used_constraints);
    if (config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        assert(!b.is_empty() || box_stack.size() == 0);
        return b;
    }
#undef PRUNEBOX
}

box multiheuristic_icp::solve(box bx, contractor & ctc, SMTConfig & config,
        vector<std::reference_wrapper<BranchHeuristic>> heuristics) {
    //don't use yet, since contractor is not yet threadsafe
    static vector<box> solns;
    solns.clear();
    std::mutex mu;
    box hull = bx;
    //hull is a shared box, that's used by all dothreads,
    //contains the intersection of the unions of the possible regions for each heuristic.
    //Therefore, any solution must be in hull.
    std::atomic_bool solved;
    std::unordered_set<std::shared_ptr<constraint>> all_used_constraints;
    prune(hull, ctc, config, all_used_constraints);
    vector<std::thread> threads;

    auto dothread = [&](BranchHeuristic & heuristic) {
#define PRUNEBOX(x) prune((x), ctc, config, used_constraints)
        thread_local static std::unordered_set<std::shared_ptr<constraint>> used_constraints;
        thread_local static vector<box> box_stack;
        thread_local static vector<box> hull_stack; //nth box in hull_stack contains hull of first n boxes in box_stack
        box_stack.clear();
        hull_stack.clear();
        used_constraints.clear();

        auto pushbox = [&](box b) {
            box_stack.push_back(b); //copies hull into vector
            if (hull_stack.size() > 0) b.hull(hull_stack.back()); //maintain hull_stack invariant
            hull_stack.push_back(b);
        };

        auto popbox = [&] {
            box b = box_stack.back();
            box_stack.pop_back();
            hull_stack.pop_back();
            return b;
        };

        mu.lock();
        box b = hull;
        mu.unlock();
        pushbox(b);

        do {
            b = popbox();
            mu.lock();
            b.intersect(hull);
            //TODO is contractor threadsafe???
            PRUNEBOX(b);
            mu.unlock();
            if (!b.is_empty()) {
                vector<int> sorted_dims = heuristic.sort_branches(b, config.nra_precision);
                if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
                if (sorted_dims.size() > 0) {
                    int bisectdim = sorted_dims[0];
                    auto splits = b.bisect_at(bisectdim);
                    box first = get<1>(splits);
                    box second = get<2>(splits);
                    assert(bisectdim != -1);
                    assert(first.get_idx_last_branched() == bisectdim);
                    assert(second.get_idx_last_branched() == bisectdim);
                    if (second.is_bisectable()) {
                        pushbox(second);
                        pushbox(first);
                    } else {
                        pushbox(first);
                        pushbox(second);
                    }
                    if (config.nra_proof) {
                        config.nra_proof_out << "[branched on "
                            << b.get_name(bisectdim)
                            << "]" << endl;
                    }
                } else {
                    mu.lock();
                    config.nra_found_soln++;
                    solns.push_back(b);
                    if (config.nra_multiple_soln > 1) {
                        // If --multiple_soln is used
                        output_solution(b, config, config.nra_found_soln);
                    }
                    if (config.nra_found_soln >= config.nra_multiple_soln) {
                        solved = true;
                        mu.unlock();
                        break;
                    }
                    mu.unlock();
                }
            }
            //hull_stack, hopefully shrunk
            if (!hull_stack.empty()) {
                mu.lock();
                hull.intersect(hull_stack.back());
                mu.unlock();
            }
        } while (box_stack.size() > 0 && !solved);

        mu.lock();
        if (config.nra_found_soln == 0) {
            solved = true; //needed if unsat
            solns.push_back(b); //would be empty
        }
        //update all_used_constraints
        for (auto x : used_constraints) {
            all_used_constraints.insert(x);
        }
        mu.unlock();

#undef PRUNEBOX
    };

    for (auto& heuristic : heuristics) {
        threads.push_back(std::thread(dothread, heuristic));
    }

    for (auto& t : threads) {
        t.join();
    }
    ctc.set_used_constraints(all_used_constraints);

    return solns.back();
}

box ncbt_icp::solve(box b, contractor & ctc, SMTConfig & config) {
    thread_local static std::unordered_set<std::shared_ptr<constraint>> used_constraints;
    used_constraints.clear();
    static unsigned prune_count = 0;
    thread_local static vector<box> box_stack;
    box_stack.clear();
    box_stack.push_back(b);
    do {
        // Loop Invariant
        DREAL_LOG_INFO << "ncbt_icp::solve - loop"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        try {
            ctc.prune(b, config);
            auto const this_used_constraints = ctc.used_constraints();
            used_constraints.insert(this_used_constraints.begin(), this_used_constraints.end());
            if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
        prune_count++;
        box_stack.pop_back();
        if (!b.is_empty()) {
            // SAT
            tuple<int, box, box> splits = b.bisect(config.nra_precision);
            if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
            int const index = get<0>(splits);
            if (index >= 0) {
                box const & first    = get<1>(splits);
                box const & second   = get<2>(splits);
                assert(first.get_idx_last_branched() == index);
                assert(second.get_idx_last_branched() == index);
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
            thread_local static unordered_set<Enode *> used_vars;
            used_vars.clear();
            for (auto used_ctr : used_constraints) {
                auto this_used_vars = used_ctr->get_vars();
                used_vars.insert(this_used_vars.begin(), this_used_vars.end());
            }
            while (box_stack.size() > 0) {
                int const bisect_var = box_stack.back().get_idx_last_branched();
                assert(bisect_var >= 0);
                // If this bisect_var is not used in all used
                // constraints, this box is safe to be popped.
                if (used_vars.find(b.get_vars()[bisect_var]) != used_vars.end()) {
                    // DREAL_LOG_FATAL << b.get_vars()[bisect_var] << " is used in "
                    //                 << *used_ctr << " and it's not safe to skip";
                    break;
                }
                // DREAL_LOG_FATAL << b.get_vars()[bisect_var] << " is not used and it's safe to skip this box"
                //                 << " (" << box_stack.size() << ")";
                box_stack.pop_back();
            }
        }
    } while (box_stack.size() > 0);
    DREAL_LOG_DEBUG << "prune count = " << prune_count;
    ctc.set_used_constraints(used_constraints);
    return b;
}

random_icp::random_icp(contractor & ctc, SMTConfig & config)
    : m_ctc(ctc), m_config(config), m_rg(m_config.nra_random_seed), m_dist(0, 1) {
}

box random_icp::solve(box b, double const precision ) {
    thread_local static std::unordered_set<std::shared_ptr<constraint>> used_constraints;
    used_constraints.clear();
    thread_local static vector<box> solns;
    thread_local static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(b);
    do {
        DREAL_LOG_INFO << "random_icp::solve - loop"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        box_stack.pop_back();
        try {
            m_ctc.prune(b, m_config);
            auto this_used_constraints = m_ctc.used_constraints();
            used_constraints.insert(this_used_constraints.begin(), this_used_constraints.end());
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!b.is_empty()) {
            tuple<int, box, box> splits = b.bisect(precision);
            int const i = get<0>(splits);
            if (i >= 0) {
                box const & first  = get<1>(splits);
                box const & second = get<2>(splits);
                if (random_bool()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                }
                if (m_config.nra_proof) {
                    m_config.nra_proof_out << "[branched on "
                                         << b.get_name(i)
                                         << "]" << endl;
                }
            } else {
                m_config.nra_found_soln++;
                if (m_config.nra_found_soln >= m_config.nra_multiple_soln) {
                    break;
                }
                if (m_config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(b, m_config, m_config.nra_found_soln);
                }
                solns.push_back(b);
            }
        }
    } while (box_stack.size() > 0);
    m_ctc.set_used_constraints(used_constraints);
    if (m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        assert(!b.is_empty() || box_stack.size() == 0);
        return b;
    }
}
}  // namespace dreal
