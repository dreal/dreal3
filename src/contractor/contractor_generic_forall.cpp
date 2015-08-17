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
using std::boolalpha;
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

static unordered_map<Enode*, ibex::Interval> make_subst_from_value(box const & b, unordered_set<Enode *> const & vars) {
    unordered_map<Enode*, ibex::Interval> subst;
    for (Enode * const var : vars) {
        auto value = b[var];
        subst.emplace(var, value);
    }
    return subst;
}

contractor_generic_forall::contractor_generic_forall(box const & , generic_forall_constraint const * const ctr)
    : contractor_cell(contractor_kind::FORALL), m_ctr(ctr) {
}

box contractor_generic_forall::handle(box b, unordered_set<Enode *> const & forall_vars, Enode * body, bool const p,  SMTConfig & config) const {
    if (body->isOr()) {
        vector<Enode *> vec = elist_to_vector(body->getCdr());
        return handle_disjunction(b, forall_vars, vec, p, config);
    } else if (body->isAnd()) {
        vector<Enode *> vec = elist_to_vector(body->getCdr());
        return handle_conjunction(b, forall_vars, vec, p, config);
    } else if (body->isNot()) {
        return handle(b, forall_vars, body->get1st(), !p, config);
    } else {
        return handle_atomic(b, forall_vars, body, p, config);
    }
}

static bool term_cond(dreal::box const & old_box, dreal::box const & new_box) {
    double const threshold = 0.01;
    // If there is a dimension which is improved more than
    // threshold, we stop the current fixed-point computation.
    for (unsigned i = 0; i < old_box.size(); i++) {
        double const new_box_i = new_box[i].diam();
        double const old_box_i = old_box[i].diam();
        if (new_box_i == numeric_limits<double>::infinity()) {
            continue;
        }
        if (old_box_i == 0) {
            // The i-th dimension was already a point, nothing to improve.
            continue;
        }
        double const improvement = 1 - new_box_i / old_box_i;
        assert(!std::isnan(improvement));
        if (improvement >= threshold) {
            return false;
        }
    }
    return true;
}

vector<Enode *> contractor_generic_forall::elist_to_vector(Enode * e) const {
    vector<Enode *> vec;
    while (!e->isEnil()) {
        vec.push_back(e->getCar());
        e = e->getCdr();
    }
    return vec;
}

box contractor_generic_forall::find_counterexample(box const & b, unordered_set<Enode*> const & forall_vars, vector<Enode*> const & vec, bool const p, SMTConfig & config) const {
    vector<nonlinear_constraint *> ctrs;
    vector<contractor> ctcs;
    box counterexample(b, forall_vars);
    for (Enode * e : vec) {
        lbool polarity = p ? l_False : l_True;
        if (e->isNot()) {
            polarity = !polarity;
            e = e->get1st();
        }
        nonlinear_constraint * ctr = new nonlinear_constraint(e, polarity);
        ctrs.push_back(ctr);
        contractor ctc = mk_contractor_ibex_fwdbwd(counterexample, ctr);
        ctcs.push_back(ctc);
    }
    contractor fp = mk_contractor_fixpoint(term_cond, ctcs);
    DREAL_LOG_DEBUG << "Counter Example = \n=============="
         << counterexample
         << "===================" << endl;
    counterexample = random_icp::solve(counterexample, fp, config);
    for (auto ctr : ctrs) {
        delete ctr;
    }
    return counterexample;
}

box contractor_generic_forall::handle_disjunction(box b, unordered_set<Enode *> const & forall_vars, std::vector<Enode *> const &vec, bool const p, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_generic_forall::handle_disjunction" << endl;
    // For now, we assume that body is a disjunction of *literals*. That is
    //
    //    body = l_1 ∨ .... ∨ l_n
    //
    // where l_i is either c_i or ¬ c_i
    //
    // TODO(soonhok): generalize this assumption
    // Step 1. Sample y \in By.
    box extended_box(b, forall_vars);
    unordered_map<Enode*, ibex::Interval> subst;
    box old_box = b;
    do {
        old_box = b;
        // Step 2. Find a counter-example
        //         Solve(¬ l_1 ∧ ¬ l_2 ∧ ... ∧ ¬ l_n)
        //
        //         Make each ¬ l_i as a contractor ctc_i
        //         Make a fixed_point contractor with ctc_is.
        //         Pass it to icp::solve
        box counterexample = find_counterexample(b, forall_vars, vec, p, config);
        if (counterexample.is_empty()) {
            // Step 2.1. (NO Counterexample)
            //           Return B.
            return b;
        } else {
            // Step 2.2. (There IS a counterexample C)
            //
            //           Using C, prune B.
            //
            // We've found a counterexample (c1, c2) where ¬ f(c1, c2) holds
            // Prune X using a point 'y = c2'. (technically, a point in c2, which is an interval)
            subst = make_subst_from_value(counterexample, forall_vars);
        }
        // Step 3. Compute B_i = prune(B, l_i)
        //         Update B with ∨ B_i
        //                       i
        std::vector<box> boxes;
        for (Enode * e : vec) {
            if (!e->get_exist_vars().empty()) {
                lbool polarity = p ? l_True : l_False;
                if (e->isNot()) {
                    polarity = !polarity;
                    e = e->get1st();
                }
                nonlinear_constraint * ctr = new nonlinear_constraint(e, polarity, subst);
                if (ctr->get_var_array().size() == 0) {
                    auto result = ctr->eval(b);
                    if (result.first != false) {
                        boxes.emplace_back(b);
                    }
                } else {
                    contractor ctc = mk_contractor_ibex_fwdbwd(b, ctr);
                    box const bt = ctc.prune(b, config);
                    boxes.emplace_back(bt);
                }
                delete ctr;
            }
        }
        b = hull(boxes);
    } while (b != old_box);
    return b;
}
box contractor_generic_forall::handle_conjunction(box b, unordered_set<Enode *> const & forall_vars, vector<Enode *> const & vec, bool const p, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_generic_forall::handle_conjunction" << endl;
    box old_b = b;
    do {
        old_b = b;
        for (Enode * e : vec) {
            DREAL_LOG_DEBUG << "process conjunction element : " << e << endl;
            b = handle(b, forall_vars, e, p, config);
            if (b.is_empty()) {
                return b;
            }
        }
    } while (old_b != b);
    return b;
}
box contractor_generic_forall::handle_atomic(box b, unordered_set<Enode *> const & forall_vars, Enode * body, bool const p, SMTConfig & config) const {
    vector<Enode*> vec;
    vec.push_back(body);
    return handle_disjunction(b, forall_vars, vec, p, config);
}

box contractor_generic_forall::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "prune: " << *m_ctr << endl;
    Enode * body = m_ctr->get_body();
    unordered_set<Enode *> const forall_vars = m_ctr->get_forall_vars();
    DREAL_LOG_DEBUG << "body = " << body << endl;
    return handle(b, forall_vars, body, true, config);
}

ostream & contractor_generic_forall::display(ostream & out) const {
    out << "contractor_generic_forall(" << *m_ctr << ")";
    return out;
}

contractor mk_contractor_generic_forall(box const & b, generic_forall_constraint const * const ctr) {
    return contractor(make_shared<contractor_generic_forall>(b, ctr));
}

}  // namespace dreal
