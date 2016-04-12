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

#include <algorithm>
#include <mutex>
#include <thread>
#include <tuple>
#include <vector>
#include "icp/icp_simulation.h"
#include "util/logging.h"
#include "util/eval.h"
#include "optimizer/optimizer.h"

namespace dreal {

using std::all_of;
using std::endl;
using std::get;
using std::lock_guard;
using std::mutex;
using std::ref;
using std::thread;
using std::tuple;
using std::vector;
using std::cerr;
using std::endl;

class icp_shared_status {
public:
    box  m_sample_domain;
    bool m_is_icp_over;
    bool m_is_simulation_over;

public:
    explicit icp_shared_status(box sample_domain)
        : m_sample_domain(sample_domain), m_is_icp_over(false), m_is_simulation_over(false) {
    }
};

void naive_icp_worker(box b, box & ret, SMTConfig & config, contractor & ctc, icp_shared_status & status) {
    vector<box> box_stack;
    bool const & simulation_over = status.m_is_simulation_over;
    thread_local static std::unordered_set<std::shared_ptr<constraint>> used_constraints;
    used_constraints.clear();
    thread_local static vector<box> solns;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(b);
    do {
        DREAL_LOG_INFO << "naive_icp::solve - loop"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        status.m_sample_domain = b;
        box_stack.pop_back();
        try {
            ctc.prune(b, config);
            auto this_used_constraints = ctc.used_constraints();
            used_constraints.insert(this_used_constraints.begin(), this_used_constraints.end());
            if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!b.is_empty()) {
            tuple<int, box, box> splits = b.bisect(config.nra_precision);
            if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
            int const i = get<0>(splits);
            if (i >= 0) {
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
    } while (!simulation_over && box_stack.size() > 0);
    if (!simulation_over) {
        ctc.set_used_constraints(used_constraints);
        if (config.nra_multiple_soln > 1 && solns.size() > 0) {
            ret = solns.back();
        } else {
            assert(!b.is_empty() || box_stack.size() == 0);
            ret = b;
        }
    }
    status.m_is_icp_over = true;
    return;
}

void optimization_worker(box & ret, vector<Enode *> const & lits, icp_shared_status & status, Egraph & e, SMTConfig & c) {
    box local_domain(status.m_sample_domain);
    box sample = local_domain.sample_point();
    optimizer opt(local_domain, lits, e, c);
    cerr<<"before improving, the domain is\n"<<local_domain<<endl;
    cerr<<"before improving, the sample point is:\n"<<sample<<endl;
    //loop continues if the sample point can be improved
    while (!status.m_is_icp_over) {
	if (!opt.improve(sample)) {
	    ret = sample;
	    status.m_is_simulation_over = true;
	    return;
	}
	cerr<<"a better point:\n"<<sample<<endl;
	//will add learned boxes etc.
    }
    status.m_is_simulation_over = true;
    return;
}

void simulation_worker(box & ret, vector<Enode *> const & lits, icp_shared_status & status) {
    box sample(ret);
    while (!status.m_is_icp_over) {
        // 1. Sample a point from front(top) box in the shared box stack
        sample = status.m_sample_domain.sample_point();
        // 2. Check consistency by evaluating the sample point
        bool const is_consistent =
            all_of(lits.begin(), lits.end(), [&sample](Enode * const lit) {
                    return eval_enode_formula(lit, sample, lit->getPolarity() == l_True) == true;
                });
        if (is_consistent) {
            ret = sample;
            status.m_is_simulation_over = true;
            return;
        }
    }
    status.m_is_simulation_over = true;
    return;
}

box simulation_icp::solve(box b, contractor & ctc, vector<Enode *> const & lits, SMTConfig & config, Egraph & e) {
    box ret(b);
    icp_shared_status status(b);
    thread icp_thread(naive_icp_worker, b, ref(ret), ref(config), ref(ctc), ref(status));
    thread optimization_thread(optimization_worker, ref(ret), ref(lits), ref(status), ref(e), ref(config));
    thread simulation_thread(simulation_worker, ref(ret), ref(lits), ref(status));    
    simulation_thread.join();
    optimization_thread.join();
    icp_thread.join();
    return ret;
}
}  // namespace dreal
