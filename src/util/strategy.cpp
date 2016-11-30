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

#include "util/strategy.h"

#include <assert.h>
#include <algorithm>
#include <cmath>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <vector>

#include "./dreal_config.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "egraph/Enode.h"
#include "ibex_Interval.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/scoped_vec.h"

using std::any_of;
using std::cerr;
using std::endl;
using std::make_shared;
using std::numeric_limits;
using std::reverse;
using std::shared_ptr;
using std::static_pointer_cast;
using std::vector;

namespace dreal {

// termination condition (used as a stopping criterion for fixedpoint computation
//
//   - return true => Stop
//   - return false => Continue
//
bool default_strategy::term_cond(box const & old_box, box const & new_box) {
    double const threshold = 0.01;
    // If there is a dimension which is improved more than
    // threshold, we continue the current fixed-point computation (return false).
    for (unsigned i = 0; i < old_box.size(); i++) {
        double const new_box_i = new_box[i].diam();
        double const old_box_i = old_box[i].diam();
        // If the width of new interval is +oo, it has no improvement
        if (new_box_i == numeric_limits<double>::infinity()) {
            continue;
        }
        // If the i-th dimension was already a point, nothing to improve.
        if (old_box_i == 0) {
            continue;
        }
        double const improvement = 1 - new_box_i / old_box_i;
        assert(!std::isnan(improvement));
        if (improvement >= threshold) {
            return false;
        }
    }
    // If an execution reaches at this point, it means there was no
    // significant improvement. So return true to stop fixedpoint
    // computation
    return true;
}

contractor default_strategy::build_contractor(box const & box,
                                              scoped_vec<shared_ptr<constraint>> const & ctrs,
                                              bool const complete, SMTConfig const & config) const {
    bool const use_cache = true;

    // 1. Categorize constraints
    vector<shared_ptr<nonlinear_constraint>> nl_ctrs;
    vector<shared_ptr<ode_constraint>> ode_ctrs_rev;
    vector<shared_ptr<forall_constraint>> forall_ctrs;
    for (shared_ptr<constraint> const ctr : ctrs.get_reverse()) {
        switch (ctr->get_type()) {
            case constraint_type::Nonlinear: {
                auto nl_ctr = static_pointer_cast<nonlinear_constraint>(ctr);
                nl_ctrs.push_back(nl_ctr);
                break;
            }
            case constraint_type::ODE: {
                auto ode_ctr = static_pointer_cast<ode_constraint>(ctr);
                ode_ctrs_rev.push_back(ode_ctr);
                break;
            }
            case constraint_type::Forall: {
                auto gf_ctr = static_pointer_cast<forall_constraint>(ctr);
                forall_ctrs.push_back(gf_ctr);
                break;
            }
            case constraint_type::ForallT: {
                // Do nothing
                break;
            }
            default:
                DREAL_LOG_FATAL << "Unknown Constraint Type: " << ctr->get_type() << " " << *ctr
                                << endl;
        }
    }
    vector<shared_ptr<ode_constraint>> ode_ctrs(ode_ctrs_rev);
    reverse(ode_ctrs.begin(), ode_ctrs.end());

    vector<contractor> ctcs;
    ctcs.reserve(ctrs.size());
    // 2.0 Build Sample Contractor
    if (config.nra_sample > 0 && complete) {
        ctcs.push_back(mk_contractor_sample(box, config.nra_sample, ctrs.get_vec()));
    }
    // 2.1 Build nonlinear contractors
    vector<contractor> nl_ctcs;
    for (auto const & nl_ctr : nl_ctrs) {
        if (!nl_ctr->is_neq()) {
            nl_ctcs.push_back(mk_contractor_ibex_fwdbwd(nl_ctr, use_cache));
        } else {
            // Case: != (not equal), do nothing
        }
    }
    contractor nl_ctc = mk_contractor_seq(nl_ctcs);
    ctcs.insert(ctcs.end(), nl_ctcs.begin(), nl_ctcs.end());

// 2.2. Build Polytope Contractor
#ifdef USE_CLP
    if (config.nra_polytope) {
        ctcs.push_back(mk_contractor_ibex_polytope(config.nra_precision, box.get_vars(), nl_ctrs));
    }
#endif
    // 2.3. Int Contractor (only if there is a var of Int sort)
    if (any_of(box.get_vars().cbegin(), box.get_vars().cend(),
               [](Enode * const v) { return v->hasSortInt(); })) {
        ctcs.push_back(mk_contractor_int(box));
    }
    // 2.4. Build forall contractors
    for (auto const & forall_ctr : forall_ctrs) {
        ctcs.push_back(mk_contractor_forall(box, forall_ctr));
    }

#ifdef SUPPORT_ODE
    if (complete && ode_ctrs.size() > 0) {
        // Add ODE Contractors only for complete check
        // 2.5. Build GSL Contractors (using CAPD4)
        vector<contractor> ode_sampling_ctcs;
        if (config.nra_ODE_sampling) {
            // 2.5.1 Build Eval contractors
            vector<contractor> eval_ctcs;
            for (auto const & nl_ctr : nl_ctrs) {
                eval_ctcs.push_back(mk_contractor_eval(nl_ctr, false));
            }
            contractor eval_ctc = mk_contractor_seq(eval_ctcs);
            if (config.nra_parallel) {
                vector<contractor> nl_ctcs2;
                for (auto const & nl_ctr : nl_ctrs) {
                    if (!nl_ctr->is_neq()) {
                        nl_ctcs2.push_back(mk_contractor_ibex_fwdbwd(nl_ctr, false));
                    } else {
                        // Case: != (not equal), do nothing
                    }
                }
                contractor nl_ctc2 = mk_contractor_seq(nl_ctcs2);
                for (auto const & ode_ctr : ode_ctrs) {
                    // Add Forward ODE Pruning (Underapproximation, using CAPD non-rigorous)
                    ode_sampling_ctcs.push_back(
                        mk_contractor_capd_point(box, ode_ctr, eval_ctc, ode_direction::FWD, config,
                                                 use_cache, config.nra_ODE_fwd_timeout));
                    ode_sampling_ctcs.push_back(nl_ctc2);
                }
            } else {
                for (auto const & ode_ctr : ode_ctrs) {
                    // Add Forward ODE Pruning (Underapproximation, using CAPD non-rigorous)
                    ode_sampling_ctcs.push_back(
                        mk_contractor_capd_point(box, ode_ctr, eval_ctc, ode_direction::FWD, config,
                                                 use_cache, config.nra_ODE_fwd_timeout));
                    ode_sampling_ctcs.push_back(nl_ctc);
                }
            }
        }
        // 2.6. Build ODE Contractors (using CAPD4)
        vector<contractor> ode_capd4_fwd_ctcs;
        vector<contractor> ode_capd4_bwd_ctcs;
        for (auto const & ode_ctr : ode_ctrs) {
            // 2.6.1. Add Forward ODE Pruning (Overapproximation, using CAPD4)
            if (config.nra_ODE_cache) {
                ode_capd4_fwd_ctcs.emplace_back(mk_contractor_try(mk_contractor_cache(
                    mk_contractor_capd_full(box, ode_ctr, ode_direction::FWD, config, use_cache,
                                            config.nra_ODE_fwd_timeout))));
            } else {
                ode_capd4_fwd_ctcs.emplace_back(mk_contractor_try(
                    mk_contractor_capd_full(box, ode_ctr, ode_direction::FWD, config, use_cache,
                                            config.nra_ODE_fwd_timeout)));
            }
        }
        if (!config.nra_ODE_forward_only) {
            // 2.6.2. Add Backward ODE Pruning (Overapproximation, using CAPD4)
            for (auto const & ode_ctr : ode_ctrs_rev) {
                if (config.nra_ODE_cache) {
                    ode_capd4_bwd_ctcs.emplace_back(mk_contractor_try(mk_contractor_cache(
                        mk_contractor_capd_full(box, ode_ctr, ode_direction::BWD, config, use_cache,
                                                config.nra_ODE_bwd_timeout))));
                } else {
                    ode_capd4_bwd_ctcs.emplace_back(mk_contractor_try(
                        mk_contractor_capd_full(box, ode_ctr, ode_direction::BWD, config, use_cache,
                                                config.nra_ODE_bwd_timeout)));
                }
            }
        }
        if (config.nra_ODE_sampling) {
            if (config.nra_parallel) {
                ctcs.push_back(mk_contractor_parallel_any(
                    mk_contractor_try_or(
                        mk_contractor_throw_if_empty(mk_contractor_seq(ode_sampling_ctcs)),
                        mk_contractor_empty()),
                    mk_contractor_seq({mk_contractor_seq(ode_capd4_fwd_ctcs),
                                       mk_contractor_seq(ode_capd4_bwd_ctcs)})));
            } else {
                ctcs.push_back(mk_contractor_try_or(
                    // Try Underapproximation(GSL) if it fails try Overapproximation(CAPD4)
                    mk_contractor_throw_if_empty(mk_contractor_seq(ode_sampling_ctcs)),
                    mk_contractor_seq({mk_contractor_seq(ode_capd4_fwd_ctcs),
                                       mk_contractor_seq(ode_capd4_bwd_ctcs)})));
            }
        } else {
            for (auto const & ode_ctc : ode_capd4_fwd_ctcs) {
                ctcs.insert(ctcs.end(), ode_ctc);
                ctcs.insert(ctcs.end(), nl_ctcs.begin(), nl_ctcs.end());
            }
            for (auto const & ode_ctc : ode_capd4_bwd_ctcs) {
                ctcs.insert(ctcs.end(), ode_ctc);
                ctcs.insert(ctcs.end(), nl_ctcs.begin(), nl_ctcs.end());
            }
        }
    }
#endif
    if (complete) {
        // 2.7 Build Eval contractors
        vector<contractor> eval_ctcs;
        for (auto const & nl_ctr : nl_ctrs) {
            eval_ctcs.push_back(mk_contractor_eval(nl_ctr, use_cache));
        }
        return mk_contractor_seq({mk_contractor_fixpoint(default_strategy::term_cond, ctcs),
                                  mk_contractor_seq(eval_ctcs)});
    } else {
        return mk_contractor_fixpoint(default_strategy::term_cond, ctcs);
    }
}
}  // namespace dreal
