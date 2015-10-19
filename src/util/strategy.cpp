/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <limits>
#include <memory>
#include <vector>
#include "util/strategy.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "contractor/contractor.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/scoped_vec.h"

using std::cerr;
using std::dynamic_pointer_cast;
using std::endl;
using std::make_shared;
using std::numeric_limits;
using std::reverse;
using std::shared_ptr;
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
                                              bool const complete,
                                              SMTConfig const & config) const {
    // 1. Categorize constraints
    vector<shared_ptr<nonlinear_constraint>> nl_ctrs;
    vector<shared_ptr<ode_constraint>> ode_ctrs_rev;
    vector<shared_ptr<generic_forall_constraint>> generic_forall_ctrs;
    for (shared_ptr<constraint> const ctr : ctrs.get_reverse()) {
        switch (ctr->get_type()) {
        case constraint_type::Nonlinear: {
            auto nl_ctr = dynamic_pointer_cast<nonlinear_constraint>(ctr);
            nl_ctrs.push_back(nl_ctr);
            break;
        }
        case constraint_type::ODE: {
            auto ode_ctr = dynamic_pointer_cast<ode_constraint>(ctr);
            ode_ctrs_rev.push_back(ode_ctr); break;
        }
        case constraint_type::GenericForall: {
            auto gf_ctr = dynamic_pointer_cast<generic_forall_constraint>(ctr);
            generic_forall_ctrs.push_back(gf_ctr); break;
        }
        default:
            DREAL_LOG_FATAL << "Unknown Constraint Type: " << ctr->get_type() << " " <<  *ctr << endl;
        }
    }
    vector<shared_ptr<ode_constraint>> ode_ctrs(ode_ctrs_rev);
    reverse(ode_ctrs.begin(), ode_ctrs.end());

    vector<contractor> ctcs;
    ctcs.reserve(ctrs.size());
    // 2.0 Build Sample Contractor
    if (config.nra_sample > 0 && complete) {
        ctcs.push_back(mk_contractor_sample(config.nra_sample, ctrs.get_vec()));
    }
    // 2.1 Build nonlinear contractors
    vector<contractor> nl_ctcs;
    for (auto const & nl_ctr : nl_ctrs) {
        if (!nl_ctr->is_neq()) {
            nl_ctcs.push_back(mk_contractor_ibex_fwdbwd(nl_ctr));
        } else {
            // Case: != (not equal), do nothing
        }
    }
    contractor nl_ctc = mk_contractor_seq(nl_ctcs);
    ctcs.push_back(nl_ctc);

    // 2.2. Build Polytope Contractor
    if (config.nra_polytope) {
        ctcs.push_back(mk_contractor_ibex_polytope(config.nra_precision, box.get_vars(), nl_ctrs));
    }
    // 2.3. Int Contractor
    ctcs.push_back(mk_contractor_int());
    // 2.4. Build generic forall contractors
    for (auto const & generic_forall_ctr : generic_forall_ctrs) {
        ctcs.push_back(mk_contractor_generic_forall(box, generic_forall_ctr));
    }

    if (complete && ode_ctrs.size() > 0) {
        // Add ODE Contractors only for complete check
        // 2.5. Build GSL Contractors (using CAPD4)
        vector<contractor> ode_gsl_ctcs;
        if (config.nra_ODE_sampling) {
            // 2.5.1 Build Eval contractors
            vector<contractor> eval_ctcs;
            for (auto const & nl_ctr : nl_ctrs) {
                eval_ctcs.push_back(mk_contractor_eval(nl_ctr));
            }
            contractor eval_ctc = mk_contractor_seq(eval_ctcs);
            for (auto const & ode_ctr : ode_ctrs) {
                // Add Forward ODE Pruning (Underapproximation, using GNU GSL)
                ode_gsl_ctcs.push_back(mk_contractor_gsl(box, ode_ctr, eval_ctc, true, config.nra_ODE_fwd_timeout));
                ode_gsl_ctcs.push_back(nl_ctc);
            }
        }
        // 2.6. Build ODE Contractors (using CAPD4)
        vector<contractor> ode_capd4_fwd_ctcs;
        vector<contractor> ode_capd4_bwd_ctcs;
        for (auto const & ode_ctr : ode_ctrs) {
            // 2.6.1. Add Forward ODE Pruning (Overapproximation, using CAPD4)
            ode_capd4_fwd_ctcs.emplace_back(
                mk_contractor_try(
                    mk_contractor_seq(
                        mk_contractor_capd_full(box, ode_ctr, true, config.nra_ODE_taylor_order, config.nra_ODE_grid_size, config.nra_ODE_fwd_timeout),
                        nl_ctc)));
        }
        if (!config.nra_ODE_forward_only) {
            // 2.6.2. Add Backward ODE Pruning (Overapproximation, using CAPD4)
            for (auto const & ode_ctr : ode_ctrs_rev) {
                ode_capd4_bwd_ctcs.emplace_back(
                    mk_contractor_try(
                        mk_contractor_seq(
                            mk_contractor_capd_full(box, ode_ctr, false, config.nra_ODE_taylor_order, config.nra_ODE_grid_size, config.nra_ODE_bwd_timeout),
                            nl_ctc)));
            }
        }

        if (config.nra_ODE_sampling) {
            ctcs.push_back(
                mk_contractor_try_or(
                    // Try Underapproximation(GSL) if it fails try Overapproximation(CAPD4)
                    mk_contractor_seq(ode_gsl_ctcs),
                    mk_contractor_seq(mk_contractor_seq(ode_capd4_fwd_ctcs),
                                      mk_contractor_seq(ode_capd4_bwd_ctcs))));
        } else {
            ctcs.insert(ctcs.end(), ode_capd4_fwd_ctcs.begin(), ode_capd4_fwd_ctcs.end());
            ctcs.insert(ctcs.end(), ode_capd4_bwd_ctcs.begin(), ode_capd4_bwd_ctcs.end());
        }
    }

    // 2.7 Build Eval contractors
    for (auto const & nl_ctr : nl_ctrs) {
        ctcs.push_back(mk_contractor_eval(nl_ctr));
    }
    return mk_contractor_fixpoint(default_strategy::term_cond, ctcs);
}
}  // namespace dreal
