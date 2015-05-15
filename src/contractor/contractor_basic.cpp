/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

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
#include <functional>
#include <initializer_list>
#include <iterator>
#include <map>
#include <memory>
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "contractor/contractor.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/constraint.h"
#include "util/logging.h"
#include "util/proof.h"

using std::back_inserter;
using std::function;
using std::initializer_list;
using std::make_shared;
using std::queue;
using std::set;
using std::stringstream;
using std::unordered_set;
using std::vector;

namespace dreal {
std::ostream & operator<<(std::ostream & out, contractor_cell const & c) {
    return c.display(out);
}

contractor_seq::contractor_seq(initializer_list<contractor> const & l)
    : contractor_cell(contractor_kind::SEQ), m_vec(l) { }

contractor_seq::contractor_seq(contractor const & c, std::vector<contractor> const & v)
    : contractor_cell(contractor_kind::SEQ), m_vec(1, c) {
    copy(v.begin(), v.end(), back_inserter(m_vec));
}
contractor_seq::contractor_seq(contractor const & c1, std::vector<contractor> const & v, contractor const & c2)
    : contractor_cell(contractor_kind::SEQ), m_vec(1, c1) {
    copy(v.begin(), v.end(), back_inserter(m_vec));
    m_vec.push_back(c2);
}

box contractor_seq::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_seq::prune";
    m_input  = ibex::BitSet::empty(b.size());
    m_output = ibex::BitSet::empty(b.size());
    for (contractor const & c : m_vec) {
        b = c.prune(b, config);
        m_input.union_with(c.input());
        m_output.union_with(c.output());
        unordered_set<constraint const *> const & used_ctrs = c.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        if (b.is_empty()) {
            return b;
        }
    }
    return b;
}
ostream & contractor_seq::display(ostream & out) const {
    out << "contractor_seq(";
    for (contractor const & c : m_vec) {
        out << c << ", ";
    }
    out << ")";
    return out;
}

contractor_try::contractor_try(contractor const & c)
    : contractor_cell(contractor_kind::TRY), m_c(c) { }
box contractor_try::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_try::prune: ";
    try {
        b = m_c.prune(b, config);
    } catch (contractor_exception & e) {
        DREAL_LOG_INFO << "contractor_try: exception caught, \""
                       << e.what() << "\n";
        return b;
    }
    m_input  = m_c.input();
    m_output = m_c.input();
    unordered_set<constraint const *> const & used_ctrs = m_c.used_constraints();
    m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
    return b;
}
ostream & contractor_try::display(ostream & out) const {
    out << "contractor_try("
        << m_c << ")";
    return out;
}

contractor_try_or::contractor_try_or(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::TRY_OR), m_c1(c1), m_c2(c2) { }
box contractor_try_or::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_try_or::prune";
    try {
        b = m_c1.prune(b, config);
        m_input  = m_c1.input();
        m_output = m_c1.input();
        unordered_set<constraint const *> const & used_ctrs = m_c1.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    } catch (contractor_exception & e) {
        b = m_c2.prune(b, config);
        m_input  = m_c2.input();
        m_output = m_c2.input();
        unordered_set<constraint const *> const & used_ctrs = m_c2.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    }
}
ostream & contractor_try_or::display(ostream & out) const {
    out << "contractor_try_or("
        << m_c1 << ", "
        << m_c2 << ")";
    return out;
}


contractor_ite::contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else)
    : contractor_cell(contractor_kind::ITE), m_guard(guard), m_c_then(c_then), m_c_else(c_else) { }
box contractor_ite::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_ite::prune";
    if (m_guard(b)) {
        b = m_c_then.prune(b, config);
        m_input  = m_c_then.input();
        m_output = m_c_then.input();
        unordered_set<constraint const *> const & used_ctrs = m_c_then.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    } else {
        b = m_c_else.prune(b, config);
        m_input  = m_c_else.input();
        m_output = m_c_else.input();
        unordered_set<constraint const *> const & used_ctrs = m_c_else.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    }
}
ostream & contractor_ite::display(ostream & out) const {
    out << "contractor_ite("
        << m_c_then << ", "
        << m_c_else << ")";
    return out;
}

contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, contractor const & c)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(1, c) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, initializer_list<contractor> const & clist)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(clist) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, vector<contractor> const & cvec)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(cvec) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond,
                                         vector<contractor> const & cvec1, vector<contractor> const & cvec2)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(cvec1) {
    copy(cvec2.begin(), cvec2.end(), back_inserter(m_clist));
}
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond,
                                         vector<contractor> const & cvec1,
                                         vector<contractor> const & cvec2,
                                         vector<contractor> const & cvec3)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(cvec1) {
    copy(cvec2.begin(), cvec2.end(), back_inserter(m_clist));
    copy(cvec3.begin(), cvec3.end(), back_inserter(m_clist));
}

box contractor_fixpoint::prune(box old_b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_fix::prune -- begin";
    // TODO(soonhok): worklist_fixpoint still has a problem
    box const & naive_result = naive_fixpoint_alg(old_b, config);
    DREAL_LOG_DEBUG << "contractor_fix::prune -- end";
    return naive_result;
    // box const & worklist_result = worklist_fixpoint_alg(old_b, config);
    // return worklist_result;
}
ostream & contractor_fixpoint::display(ostream & out) const {
    out << "contractor_fixpoint(";
    for (contractor const & c : m_clist) {
        out << c << ", " << endl;
    }
    out << ")";
    return out;
}

box contractor_fixpoint::naive_fixpoint_alg(box old_box, SMTConfig & config) const {
    box new_box = old_box;
    m_input  = ibex::BitSet::empty(old_box.size());
    m_output = ibex::BitSet::empty(old_box.size());
    // Fixed Point Loop
    do {
        old_box = new_box;
        for (contractor const & c : m_clist) {
            new_box = c.prune(new_box, config);
            m_input.union_with(c.input());
            m_output.union_with(c.output());
            unordered_set<constraint const *> const & used_constraints = c.used_constraints();
            m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
            if (new_box.is_empty()) {
                return new_box;
            }
        }
    } while (!m_term_cond(old_box, new_box));
    return new_box;
}

box contractor_fixpoint::worklist_fixpoint_alg(box old_box, SMTConfig & config) const {
    box new_box = old_box;
    m_input  = ibex::BitSet::empty(old_box.size());
    m_output = ibex::BitSet::empty(old_box.size());

    // Add all contractors to the queue.
    unordered_set<contractor> c_set;
    queue<contractor> q;

    for (contractor const & c : m_clist) {
        if (c_set.find(c) == c_set.end()) {
            q.push(c);
            c_set.insert(c);
        }
    }
    unsigned const num_initial_ctcs = c_set.size();
    unsigned count = 0;
    // Fixed Point Loop
    do {
        old_box = new_box;
        contractor const & c = q.front();
        new_box = c.prune(new_box, config);
        count++;
        m_input.union_with(c.input());
        m_output.union_with(c.output());
        unordered_set<constraint const *> const & used_constraints = c.used_constraints();
        m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
        if (new_box.is_empty()) {
            return new_box;
        }
        c_set.erase(c);
        q.pop();

        vector<bool> diff_dims = new_box.diff_dims(old_box);
        for (unsigned i = 0; i < diff_dims.size(); i++) {
            if (diff_dims[i]) {
                for (contractor const & c : m_clist) {
                    if (c.input()[i]) {
                        if (c_set.find(c) == c_set.end()) {
                            q.push(c);
                            c_set.insert(c);
                        }
                        break;
                    }
                }
            }
        }
    } while (q.size() > 0 && ((count < num_initial_ctcs) || !m_term_cond(old_box, new_box)));
    return new_box;
}

contractor_int::contractor_int() : contractor_cell(contractor_kind::INT) { }
box contractor_int::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_int::prune";
    // ======= Proof =======
    thread_local static box old_box(b);
    if (config.nra_proof) { old_box = b; }

    m_input  = ibex::BitSet::empty(b.size());
    m_output = ibex::BitSet::empty(b.size());
    unsigned i = 0;
    ibex::IntervalVector & iv = b.get_values();
    for (Enode * e : b.get_vars()) {
        if (e->hasSortInt()) {
            auto old_iv = iv[i];
            iv[i] = ibex::integer(iv[i]);
            if (old_iv != iv[i]) {
                m_input.add(i);
                m_output.add(i);
            }
            if (iv[i].is_empty()) {
                b.set_empty();
                break;
            }
        }
        i++;
    }

    // ======= Proof =======
    if (config.nra_proof) {
        output_pruning_step(config.nra_proof_out, old_box, b, config.nra_readable_proof, "integer pruning");
    }
    return b;
}
ostream & contractor_int::display(ostream & out) const {
    out << "contractor_int()";
    return out;
}

contractor_eval::contractor_eval(box const & box, nonlinear_constraint const * const ctr)
    : contractor_cell(contractor_kind::EVAL), m_nl_ctr(ctr) {
    // // Set up input
    auto const & var_array = m_nl_ctr->get_var_array();
    for (int i = 0; i < var_array.size(); i++) {
        m_input.add(box.get_index(var_array[i].name));
    }
}

box contractor_eval::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_eval::prune";
    pair<lbool, ibex::Interval> eval_result = m_nl_ctr->eval(b);
    if (eval_result.first == l_False) {
        // ======= Proof =======
        if (config.nra_proof) {
            box old_box = b;
            b.set_empty();
            stringstream ss;
            Enode const * const e = m_nl_ctr->get_enode();
            ss << (e->getPolarity() == l_False ? "!" : "") << e;
            output_pruning_step(config.nra_proof_out, old_box, b, config.nra_readable_proof, ss.str());
        } else {
            b.set_empty();
        }
        m_used_constraints.insert(m_nl_ctr);
    }
    return b;
}
ostream & contractor_eval::display(ostream & out) const {
    out << "contractor_eval(" << *m_nl_ctr << ")";
    return out;
}

contractor_cache::contractor_cache(contractor const & ctc)
    : contractor_cell(contractor_kind::CACHE), m_ctc(ctc) {
    // TODO(soonhok): implement this
    //
    // Need to set up:
    //
    // - ibex::BitSet m_input;
    // - ibex::BitSet m_output;
    // - std::unordered_set<constraint const *> m_used_constraints;
}

box contractor_cache::prune(box b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_cache::prune";
    // TODO(soonhok): implement this
    thread_local static unordered_map<box, box> cache;
    auto const it = cache.find(b);
    if (it == cache.cend()) {
        // Not Found
        return m_ctc.prune(b, config);
    } else {
        // Found
        return it->second;
    }
}

ostream & contractor_cache::display(ostream & out) const {
    out << "contractor_cache(" << m_ctc << ")";
    return out;
}

contractor_sample::contractor_sample(unsigned const n, vector<constraint *> const & ctrs)
    : contractor_cell(contractor_kind::SAMPLE), m_num_samples(n), m_ctrs(ctrs) {
}

box contractor_sample::prune(box b, SMTConfig &) const {
    DREAL_LOG_DEBUG << "contractor_sample::prune";
    // Sample n points
    set<box> points = b.sample_points(m_num_samples);
    // If ∃p. ∀c. eval(c, p) = true, return 'SAT'
    unsigned count = 0;
    for (box const & p : points) {
        DREAL_LOG_DEBUG << "contractor_sample::prune -- sample " << ++count << "th point = " << p;
        bool check = true;
        for (constraint * const ctr : m_ctrs) {
            if (ctr->get_type() == constraint_type::Nonlinear) {
                nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
                pair<lbool, ibex::Interval> eval_result = nl_ctr->eval(p);
                if (eval_result.first == l_False) {
                    check = false;
                    DREAL_LOG_DEBUG << "contractor_sample::prune -- sampled point = " << p << " does not satisfy " << *ctr;
                    break;
                }
            }
        }
        if (check) {
            DREAL_LOG_DEBUG << "contractor_sample::prune -- sampled point = " << p << " satisfies all constraints";
            return p;
        }
    }
    return b;
}

ostream & contractor_sample::display(ostream & out) const {
    out << "contractor_sample(" << m_num_samples << ")";
    return out;
}

contractor_aggressive::contractor_aggressive(unsigned const n, vector<constraint *> const & ctrs)
    : contractor_cell(contractor_kind::SAMPLE), m_num_samples(n), m_ctrs(ctrs) {
}

box contractor_aggressive::prune(box b, SMTConfig &) const {
    DREAL_LOG_DEBUG << "contractor_eval::aggressive";
    // Sample n points
    set<box> points = b.sample_points(m_num_samples);
    // ∃c. ∀p. eval(c, p) = false   ===>  UNSAT
    for (constraint * const ctr : m_ctrs) {
        if (ctr->get_type() == constraint_type::Nonlinear) {
            nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
            bool check = false;
            for (box const & p : points) {
                pair<lbool, ibex::Interval> eval_result = nl_ctr->eval(p);
                if (eval_result.first != l_False) {
                    check = true;
                    break;
                }
            }
            if (!check) {
                m_used_constraints.insert(ctr);
                pair<lbool, ibex::Interval> eval_result = nl_ctr->eval(b);
                DREAL_LOG_DEBUG << "Constraint: " << *nl_ctr << " is violated by all " << points.size() << " points";
                DREAL_LOG_DEBUG << "FYI, the interval evaluation gives us : " << eval_result.second;
                b.set_empty();
                return b;
            }
        }
    }
    return b;
}

ostream & contractor_aggressive::display(ostream & out) const {
    out << "contractor_aggressive(" << m_num_samples << ")";
    return out;
}


contractor mk_contractor_seq(initializer_list<contractor> const & l) {
    return contractor(make_shared<contractor_seq>(l));
}
contractor mk_contractor_seq(contractor const & c, vector<contractor> const & v) {
    return contractor(make_shared<contractor_seq>(c, v));
}
contractor mk_contractor_seq(contractor const & c1, vector<contractor> const & v, contractor const & c2) {
    return contractor(make_shared<contractor_seq>(c1, v, c2));
}
contractor mk_contractor_try(contractor const & c) {
    return contractor(make_shared<contractor_try>(c));
}
contractor mk_contractor_try_or(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_try_or>(c1, c2));
}
contractor mk_contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else) {
    return contractor(make_shared<contractor_ite>(guard, c_then, c_else));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, contractor const & c) {
    return contractor(make_shared<contractor_fixpoint>(guard, c));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, initializer_list<contractor> const & clist) {
    return contractor(make_shared<contractor_fixpoint>(guard, clist));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, vector<contractor> const & cvec) {
    return contractor(make_shared<contractor_fixpoint>(guard, cvec));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard,
                                  vector<contractor> const & cvec1, vector<contractor> const & cvec2) {
    return contractor(make_shared<contractor_fixpoint>(guard, cvec1, cvec2));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard,
                                  vector<contractor> const & cvec1,
                                  vector<contractor> const & cvec2,
                                  vector<contractor> const & cvec3) {
    return contractor(make_shared<contractor_fixpoint>(guard, cvec1, cvec2, cvec3));
}
contractor mk_contractor_int() {
    return contractor(make_shared<contractor_int>());
}
contractor mk_contractor_eval(box const & box, nonlinear_constraint const * const ctr) {
    static thread_local unordered_map<nonlinear_constraint const *, contractor> cache;
    auto const it = cache.find(ctr);
    if (it == cache.cend()) {
        contractor ctc(make_shared<contractor_eval>(box, ctr));
        cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}
contractor mk_contractor_cache(contractor const & ctc) {
    return contractor(make_shared<contractor_cache>(ctc));
}
contractor mk_contractor_sample(unsigned const n, vector<constraint *> const & ctrs) {
    return contractor(make_shared<contractor_sample>(n, ctrs));
}
contractor mk_contractor_aggressive(unsigned const n, vector<constraint *> const & ctrs) {
    return contractor(make_shared<contractor_aggressive>(n, ctrs));
}
std::ostream & operator<<(std::ostream & out, contractor const & c) {
    out << *(c.m_ptr);
    return out;
}

}  // namespace dreal
