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

#include "icp/simulation_icp.h"

#include <assert.h>

#include <algorithm>
#include <exception>
#include <iostream>
#include <memory>
#include <thread>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "contractor/contractor_status.h"
#include "icp/icp.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/scoped_vec.h"
#include "util/stat.h"
#include "util/thread_local.h"

namespace dreal {

using std::all_of;
using std::cerr;
using std::static_pointer_cast;
using std::endl;
using std::endl;
using std::exception;
using std::get;
using std::lock_guard;
using std::mutex;
using std::ref;
using std::shared_ptr;
using std::thread;
using std::tuple;
using std::unordered_set;
using std::vector;

class icp_shared_status {
public:
    box m_sample_domain;
    bool m_is_icp_over;
    bool m_is_simulation_over;

public:
    explicit icp_shared_status(box sample_domain)
        : m_sample_domain(sample_domain), m_is_icp_over(false), m_is_simulation_over(false) {}
};

void naive_icp_worker(contractor_status & cs, box & ret, contractor & ctc,
                      icp_shared_status & status) {
    vector<box> box_stack;
    bool const & simulation_over = status.m_is_simulation_over;
    DREAL_THREAD_LOCAL static unordered_set<shared_ptr<constraint>> used_constraints;
    used_constraints.clear();
    DREAL_THREAD_LOCAL static vector<box> solns;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(cs.m_box);
    do {
        DREAL_LOG_INFO << "naive_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        cs.m_box = box_stack.back();
        status.m_sample_domain = cs.m_box;
        box_stack.pop_back();
        try {
            ctc.prune(cs);
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!cs.m_box.is_empty()) {
            tuple<int, box, box> splits = cs.m_box.bisect(cs.m_config.nra_precision);
            if (cs.m_config.nra_use_stat) {
                cs.m_config.nra_stat.increase_branch();
            }
            int const i = get<0>(splits);
            if (i >= 0) {
                box const & first = get<1>(splits);
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
    } while (!simulation_over && box_stack.size() > 0);
    if (!simulation_over) {
        if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
            ret = solns.back();
        } else {
            assert(!cs.m_box.is_empty() || box_stack.size() == 0);
            ret = cs.m_box;
        }
    }
    status.m_is_icp_over = true;
    return;
}

// void optimization_worker(box & ret, scoped_vec<std::shared_ptr<constraint>> const & ctrs,
// icp_shared_status & status, Egraph & e, SMTConfig & c) {
//     box local_domain(status.m_sample_domain);
//     box sample = local_domain.sample_point();
//     optimizer opt(local_domain, lits, e, c);
//     cerr << "before improving, the domain is\n" << local_domain << endl;
//     cerr << "before improving, the sample point is:\n" << sample << endl;
//     // loop continues if the sample point can be improved
//     while (!status.m_is_icp_over) {
//         if (!opt.improve(sample)) {
//             ret = sample;
//             status.m_is_simulation_over = true;
//             return;
//         }
//         cerr << "a better point:\n" << sample << endl;
//         // will add learned boxes etc.
//     }
//     status.m_is_simulation_over = true;
//     return;
// }

void simulation_worker(box & ret, scoped_vec<shared_ptr<constraint>> const & ctrs,
                       icp_shared_status & status, double prec) {
    box sample(ret);
    if (status.m_is_icp_over) {
        DREAL_LOG_INFO << "ICP has terminated before simulation.\n";
    } else {
        DREAL_LOG_INFO << "Sampling...\n";
    }
    while (!status.m_is_icp_over) {
        // 1. Sample a point from front(top) box in the shared box stack
        sample = status.m_sample_domain.sample_point();
        DREAL_LOG_INFO << ">>>Sampler working on domain:\n" << status.m_sample_domain << "\n<<<\n";
        DREAL_LOG_INFO << "Current sample point:\n" << sample << endl;
        // 2. Check consistency by evaluating the sample point
        bool const is_consistent =
            all_of(ctrs.begin(), ctrs.end(), [&sample, prec](shared_ptr<constraint> const ctr) {
                try {
                    // if not regular nonlinear constraint, return false for now
                    if (!ctr->is_simple_nonlinear()) return false;
                    // return eval_enode_formula(lit, sample, lit->getPolarity() == l_True) == true;
                    double const err = ctr->eval_error(sample);
                    bool const ans = err < prec;
                    if (!ans) {
                        DREAL_LOG_INFO << *ctr << " has this error: " << err
                                       << " [current delta: " << prec << ", ";
                        if (ans) {
                            DREAL_LOG_INFO << "satisfied]\n";
                        } else {
                            DREAL_LOG_INFO << "violated]\n";
                        }
                    }
                    return ans;
                } catch (exception & e) {
                    return false;
                }
            });
        if (is_consistent) {
            DREAL_LOG_INFO << "Delta-sat has been witnessed by the last sample.\n";
            ret = sample;
            status.m_is_simulation_over = true;
            return;
        }
    }
    DREAL_LOG_INFO << "Sampling has terminated because ICP has stopped.\n";
    status.m_is_simulation_over = true;
    return;
}

void simulation_icp::solve(contractor & ctc, contractor_status & cs,
                           scoped_vec<shared_ptr<constraint>> const & ctrs, double prec) {
    box ret(cs.m_box);
    icp_shared_status status(cs.m_box);
    thread icp_thread(naive_icp_worker, ref(cs), ref(ret), ref(ctc), ref(status));
    //    thread optimization_thread(optimization_worker, ref(ret), ref(ctrs), ref(status), ref(e),
    //    ref(cs.m_config));
    thread simulation_thread(simulation_worker, ref(ret), ref(ctrs), ref(status), ref(prec));
    simulation_thread.join();
    //    optimization_thread.join();
    icp_thread.join();
    cs.m_box = ret;
    // TODO(soonhok): need to setup output and used_constraints?
}
}  // namespace dreal
