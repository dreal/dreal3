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

#include <limits>
#include <vector>
#include "util/strategy.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "contractor/contractor.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/scoped_vec.h"

using std::vector;
using std::cerr;
using std::endl;
using std::numeric_limits;

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
                                              scoped_vec<constraint *> const &ctrs,
                                              bool const complete,
                                              SMTConfig const & config) const {
    // 1. Categorize constraints
    vector<nonlinear_constraint const *> nl_ctrs;
    vector<ode_constraint const *> ode_ctrs;
    vector<generic_forall_constraint const *> generic_forall_ctrs;
    for (constraint * const ctr : ctrs.get_reverse()) {
        switch (ctr->get_type()) {
        case constraint_type::Nonlinear: {
            nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
            nl_ctrs.push_back(nl_ctr);
            break;
        }
        case constraint_type::ODE: {
            ode_constraint const * const ode_ctr = dynamic_cast<ode_constraint *>(ctr);
            ode_ctrs.push_back(ode_ctr); break;
        }
        case constraint_type::GenericForall: {
            generic_forall_constraint const * const gf_ctr = dynamic_cast<generic_forall_constraint *>(ctr);
            generic_forall_ctrs.push_back(gf_ctr); break;
        }
        default:
            DREAL_LOG_FATAL << "Unknown Constraint Type: " << ctr->get_type() << " " <<  *ctr << endl;
        }
    }

    vector<contractor> ctcs;
    ctcs.reserve(ctrs.size());
    // 2.0 Build Sample Contractor
    if (config.nra_sample > 0 && complete) {
        ctcs.push_back(mk_contractor_sample(config.nra_sample, ctrs.get_vec()));
    }
    // 2.1 Build nonlinear contractors
    for (auto nl_ctr : nl_ctrs) {
        if (!nl_ctr->is_neq()) {
            ctcs.push_back(mk_contractor_ibex_fwdbwd(box, nl_ctr));
        } else {
            // Case: != (not equal), do nothing
        }
    }
    // 2.2. Build Polytope Contractor
    if (config.nra_polytope) {
        ctcs.push_back(mk_contractor_ibex_polytope(config.nra_precision, box.get_vars(), nl_ctrs));
    }
    // 2.3. Int Contractor
    ctcs.push_back(mk_contractor_int());
    // 2.4. Build generic forall contractors
    for (auto generic_forall_ctr : generic_forall_ctrs) {
        ctcs.push_back(mk_contractor_generic_forall(box, generic_forall_ctr));
    }
    // 2.5. Build ODE constractors
    if (complete) {
        for (auto ode_ctr : ode_ctrs) {
            // For now, it always tries forward-ode-pruning first, and then backward-ode pruning later.
            ctcs.emplace_back(
                mk_contractor_try(
                    mk_contractor_capd_fwd_full(box, ode_ctr, config.nra_ODE_taylor_order, config.nra_ODE_grid_size)));
            if (!config.nra_ODE_forward_only) {
                ctcs.emplace_back(
                    mk_contractor_try(
                        mk_contractor_capd_bwd_full(box, ode_ctr, config.nra_ODE_taylor_order, config.nra_ODE_grid_size)));
            }
        }
    }
    // 2.6 Build Eval contractors
    for (auto nl_ctr : nl_ctrs) {
        ctcs.push_back(mk_contractor_eval(box, nl_ctr));
    }
    return mk_contractor_fixpoint(default_strategy::term_cond, ctcs);
}
}  // namespace dreal
