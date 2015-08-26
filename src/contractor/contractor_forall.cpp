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
#include <chrono>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "contractor/contractor.h"
#include "ibex/ibex.h"
#include "icp/icp.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "util/logging.h"
#include "util/proof.h"

using std::back_inserter;
using std::cerr;
using std::endl;
using std::function;
using std::initializer_list;
using std::make_shared;
using std::ostream;
using std::ostringstream;
using std::queue;
using std::set;
using std::unordered_set;
using std::vector;

namespace dreal {

static unordered_map<Enode*, ibex::Interval> make_subst_from_bound(box const & b, unordered_set<Enode *> const & vars) {
    unordered_map<Enode*, ibex::Interval> subst;
    for (Enode * const var : vars) {
        auto & bound = b.get_bound(var);
        subst.emplace(var, bound);
    }
    return subst;
}

static unordered_map<Enode*, ibex::Interval> make_subst_from_value(box const & b, unordered_set<Enode *> const & vars) {
    unordered_map<Enode*, ibex::Interval> subst;
    for (Enode * const var : vars) {
        auto & value = b[var];
        subst.emplace(var, value);
    }
    return subst;
}

contractor_forall::contractor_forall(box const & , forall_constraint const * const ctr)
    : contractor_cell(contractor_kind::FORALL), m_ctr(ctr) {
}

box contractor_forall::prune(box b, SMTConfig & config) const {
    // Prep
    static thread_local box old_box(b);
    lbool const p = m_ctr->get_polarity();
    Enode * const e = m_ctr->get_enode();
    unordered_set<Enode*> const & forall_vars = m_ctr->get_forall_vars();
    DREAL_LOG_DEBUG << "\n\n==================================" << endl;
    DREAL_LOG_DEBUG << "contractor_forall::prune: begin = " << b << endl;

    // ==================================================================
    // Stpe 1.
    // For ∃ x, ∀ y, f(x, y)
    // Check ∃ x, ∃ y, f(x, y) to try to reduce the range of y
    // If ∃ x, ∃ y, f(x, y) is UNSAT, then return empty box.
    // ==================================================================
    box extended_box(b, forall_vars);
    nonlinear_constraint const * const ctr0 = new nonlinear_constraint(e, p);
    contractor extended_ctc = mk_contractor_ibex_fwdbwd(extended_box, ctr0);
    extended_box = extended_ctc.prune(extended_box, config);
    // random_icp::solve(extended_box, extended_ctc, config);
    delete ctr0;
    if (extended_box.is_empty()) {
        b.set_empty();
        return b;
    }

    // ====================================================================================
    // Stpe 2.
    // For ∃ x, ∀ y, f(x, y)
    // Sample c for y (which is pruned by step 1), and prune x by solving ∃ x, f(x, c)
    // ====================================================================================

    // Make a random subst from forall_vars, prune b using
    unordered_map<Enode*, ibex::Interval> subst = make_subst_from_bound(extended_box, forall_vars);
    // DREAL_LOG_DEBUG << "subst = " << subst << endl;
    nonlinear_constraint const * const ctr = new nonlinear_constraint(e, p, subst);
    contractor ctc = mk_contractor_ibex_fwdbwd(b, ctr);
    old_box = b;
    DREAL_LOG_DEBUG << "prune using " << ctc << endl;
    b = ctc.prune(b, config);
    if (b == old_box) {
        // =========================================================
        // Step 3.
        // Check Counterexample -- ∃ x, ∃ y. ¬ f(x, y).
        // (note: we run icp_loop)
        // =========================================================
        DREAL_LOG_DEBUG << "Sampling doesn't help. Try to find a counter example" << endl;
        nonlinear_constraint const * const not_ctr = new nonlinear_constraint(e, !p);
        box counter_example(b, forall_vars);
        contractor not_ctc = mk_contractor_ibex_fwdbwd(counter_example, not_ctr);
        DREAL_LOG_DEBUG << "icp with " << not_ctc << endl;
        counter_example = random_icp::solve(counter_example, not_ctc, config);
        if (!counter_example.is_empty()) {
            // =========================================================
            // Step 4.
            // We've found a counterexample (c1, c2) where ¬ f(c1, c2) holds
            // Prune X using a point 'y = c2'. (technically, a point in c2, which is an interval)
            // =========================================================
            DREAL_LOG_DEBUG << "Found possible counterexample" << endl;
            DREAL_LOG_DEBUG << "not_ctc = " << not_ctc << endl;
            DREAL_LOG_DEBUG << counter_example << endl;
            subst = make_subst_from_value(counter_example, forall_vars);
            // DREAL_LOG_DEBUG << "subst = " << subst << endl;
            nonlinear_constraint const * const ctr2 = new nonlinear_constraint(e, p, subst);
            contractor ctc2 = mk_contractor_ibex_fwdbwd(b, ctr2);
            DREAL_LOG_DEBUG << "prune using " << ctc2 << endl;
            b = ctc2.prune(b, config);
            if (b != old_box) {
                DREAL_LOG_DEBUG << "Pruned from counterexample (stop)" << endl;
            } else {
                DREAL_LOG_DEBUG << "b == old_box. a counter example doesn't prune anything. repeat." << endl;
                DREAL_LOG_DEBUG << b << endl;
            }
            delete ctr2;
        } else {
            DREAL_LOG_DEBUG << "counter_example is empty. b should be the right answer." << endl;
        }
        delete not_ctr;
    } else {
        DREAL_LOG_DEBUG << "b != old_box, we made a progress, exit." << endl;
    }
    DREAL_LOG_DEBUG << "contractor_forall::prune: result = " << b << endl;
    DREAL_LOG_DEBUG << "==================================\n\n" << endl;
    m_used_constraints.insert(m_ctr);
    m_input  = ibex::BitSet::all(b.size());
    m_output = ibex::BitSet::all(b.size());
    delete ctr;
    return b;
}

ostream & contractor_forall::display(ostream & out) const {
    out << "contractor_forall(" << *m_ctr << ")";
    return out;
}

contractor mk_contractor_forall(box const & b, forall_constraint const * const ctr) {
    return contractor(make_shared<contractor_forall>(b, ctr));
}

}  // namespace dreal
