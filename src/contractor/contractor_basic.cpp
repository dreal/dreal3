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
#include "constraint/constraint.h"
#include "contractor/contractor_basic.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/proof.h"
#include "util/interruptible_thread.h"

using std::back_inserter;
using std::cerr;
using std::cout;
using std::dynamic_pointer_cast;
using std::endl;
using std::function;
using std::initializer_list;
using std::make_pair;
using std::make_shared;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::set;
using std::shared_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::tuple;
using std::get;

namespace dreal {

contractor_id::contractor_id()
    : contractor_cell(contractor_kind::ID) {
}
void contractor_id::prune(box &, SMTConfig &) {
    return;
}
ostream & contractor_id::display(ostream & out) const {
    out << "contractor_id()";
    return out;
}

void contractor_seq::init() {
    m_input = m_vec[0].input();
    for (unsigned i = 1; i < m_vec.size(); ++i) {
        m_input.union_with(m_vec[i].input());
    }
    m_output = m_input;
    m_output.clear();
}
contractor_seq::contractor_seq(initializer_list<contractor> const & l)
    : contractor_cell(contractor_kind::SEQ), m_vec(l) {
    assert(l.size() > 0);
    init();
}
contractor_seq::contractor_seq(vector<contractor> const & v)
    : contractor_cell(contractor_kind::SEQ), m_vec(v) {
    assert(v.size() > 0);
    init();
}
contractor_seq::contractor_seq(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::SEQ), m_vec(1, c1) {
    m_vec.push_back(c2);
    init();
}
void contractor_seq::prune_naive(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_seq::prune";
    for (contractor & c : m_vec) {
        interruption_point();
        c.prune(b, config);
        m_output.union_with(c.output());
        unordered_set<shared_ptr<constraint>> const & used_ctrs = c.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        if (b.is_empty()) {
            return;
        }
    }
    return;
}

double compute_cost(contractor & c, box const & b) {
    double cost = 0.0;
    unsigned num_of_non_zero = 0;
    auto in = c.input();
    if (in.empty()) {
        return numeric_limits<double>::lowest();
    } else {
        for (int i = in.min(); i <= in.max(); ++i) {
            if (in.contain(i)) {
                num_of_non_zero++;
                cost += log(b[i].diam());
            }
        }
        return cost / num_of_non_zero;
    }
}

void contractor_seq::prune_smart(box & b, SMTConfig & config) {
    vector<contractor> v(m_vec);
    while (v.size() > 0) {
        interruption_point();
        unsigned min_idx = 0;
        double min_cost = compute_cost(v[min_idx], b);
        for (unsigned i = 1; i < v.size(); ++i) {
            double cost_i = compute_cost(v[i], b);
            if (min_cost > cost_i) {
                min_idx = i;
                min_cost = cost_i;
            }
        }
        v[min_idx].prune(b, config);
        m_output.union_with(v[min_idx].output());
        unordered_set<shared_ptr<constraint>> const & used_ctrs = v[min_idx].used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        if (b.is_empty()) {
            return;
        }
        v.erase(v.begin() + min_idx);
    }
    return;
}

void contractor_seq::prune(box & b, SMTConfig & config) {
    if (m_vec.size() == 0) {
        return;
    }
    return prune_naive(b, config);
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
    : contractor_cell(contractor_kind::TRY), m_c(c) {
    m_input = m_c.input();
    m_output = m_input;
    m_output.clear();
}
void contractor_try::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_try::prune: ";
    thread_local static box old_box(b);
    old_box = b;
    try {
        m_c.prune(b, config);
        m_output = m_c.output();
        m_used_constraints = m_c.used_constraints();
    } catch (contractor_exception & e) {
        DREAL_LOG_INFO << "contractor_try: exception caught, \""
                       << e.what() << "\n";
        b = old_box;
        return;
    }
}
ostream & contractor_try::display(ostream & out) const {
    out << "contractor_try("
        << m_c << ")";
    return out;
}

contractor_try_or::contractor_try_or(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::TRY_OR), m_c1(c1), m_c2(c2) {
    m_input = m_c1.input();
    m_input.union_with(m_c2.input());
    m_output = m_input;
    m_output.clear();
}
void contractor_try_or::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_try_or::prune";
    thread_local static box old_box(b);
    old_box = b;
    try {
        m_c1.prune(b, config);
        m_output = m_c1.output();
        m_used_constraints = m_c1.used_constraints();
    } catch (contractor_exception & e) {
        b = old_box;
        m_c2.prune(b, config);
        m_output = m_c2.output();
        m_used_constraints = m_c2.used_constraints();
    }
}
ostream & contractor_try_or::display(ostream & out) const {
    out << "contractor_try_or("
        << m_c1 << ", "
        << m_c2 << ")";
    return out;
}

contractor_throw_if_empty::contractor_throw_if_empty(contractor const & c)
    : contractor_cell(contractor_kind::THROW_IF_EMPTY), m_c(c) {
    m_input = m_c.input();
    m_output = m_input;
    m_output.clear();
}
void contractor_throw_if_empty::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_throw_if_empty::prune";
    m_c.prune(b, config);
    m_output = m_c.output();
    m_used_constraints = m_c.used_constraints();
    if (b.is_empty()) {
        throw contractor_exception("throw if empty");
    }
}
ostream & contractor_throw_if_empty::display(ostream & out) const {
    out << "contractor_throw_if_empty(" << m_c << ")";
    return out;
}

contractor_join::contractor_join(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::JOIN), m_c1(c1), m_c2(c2) {
    m_input = m_c1.input();
    m_input.union_with(m_c2.input());
    m_output = m_input;
    m_output.clear();
}
void contractor_join::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_join::prune";
    m_output = ibex::BitSet::empty(b.size());

    // save b
    thread_local box tmp_b(b);
    tmp_b = b;

    // run m_c1
    m_c1.prune(b, config);
    m_output = m_c1.output();
    m_used_constraints = m_c1.used_constraints();

    // run m_c2 on b1
    m_c2.prune(tmp_b, config);
    m_output.union_with(m_c2.output());
    unordered_set<shared_ptr<constraint>> const & used_ctrs2 = m_c2.used_constraints();
    m_used_constraints.insert(used_ctrs2.begin(), used_ctrs2.end());

    // join(hull) b and tmp_b
    b.hull(tmp_b);
}
ostream & contractor_join::display(ostream & out) const {
    out << "contractor_join(" << m_c1 << ", " << m_c2 << ")";
    return out;
}

contractor_ite::contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else)
    : contractor_cell(contractor_kind::ITE), m_guard(guard), m_c_then(c_then), m_c_else(c_else) {
    m_input = m_c_then.input();
    m_input.union_with(m_c_else.input());
    m_output = m_input;
    m_output.clear();
}
void contractor_ite::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_ite::prune";
    if (m_guard(b)) {
        m_c_then.prune(b, config);
        m_output = m_c_then.output();
        m_used_constraints = m_c_then.used_constraints();
        return;
    } else {
        m_c_else.prune(b, config);
        m_output = m_c_else.output();
        m_used_constraints = m_c_else.used_constraints();
        return;
    }
}
ostream & contractor_ite::display(ostream & out) const {
    out << "contractor_ite(" << m_c_then << ", " << m_c_else << ")";
    return out;
}

void contractor_fixpoint::init() {
    m_input = m_clist[0].input();
    for (unsigned i = 1; i < m_clist.size(); ++i) {
        m_input.union_with(m_clist[i].input());
    }
    m_output = m_input;
    m_output.clear();
}

contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, contractor const & c)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(1, c) {
    init();
}
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, initializer_list<contractor> const & clist)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(clist) {
    assert(m_clist.size() > 0);
    init();
}
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, vector<contractor> const & cvec)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(cvec) {
    assert(m_clist.size() > 0);
    init();
}
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, initializer_list<vector<contractor>> const & cvec_list)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist() {
    for (auto const & cvec : cvec_list) {
        m_clist.insert(m_clist.end(), cvec.begin(), cvec.end());
    }
    assert(m_clist.size() > 0);
    init();
}

void contractor_fixpoint::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_fix::prune -- begin";
    if (config.nra_worklist_fp) {
        // TODO(soonhok): worklist_fixpoint still has a problem
        worklist_fixpoint_alg(b, config);
        DREAL_LOG_DEBUG << "contractor_fix::prune -- end";
        return;
    } else {
        naive_fixpoint_alg(b, config);
        DREAL_LOG_DEBUG << "contractor_fix::prune -- end";
        return;
    }
}
ostream & contractor_fixpoint::display(ostream & out) const {
    out << "contractor_fixpoint(";
    for (contractor const & c : m_clist) {
        out << c << ", " << endl;
    }
    out << ")";
    return out;
}

void contractor_fixpoint::naive_fixpoint_alg(box & b, SMTConfig & config) {
    // DREAL_LOG_FATAL << "===================";
    box old_box(b);
    // Fixed Point Loop
    do {
        interruption_point();
        old_box = b;
        for (contractor & c : m_clist) {
            // DREAL_LOG_FATAL << "naive: prune " << c;
            c.prune(b, config);
            m_output.union_with(c.output());
            unordered_set<shared_ptr<constraint>> const & used_constraints = c.used_constraints();
            m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
            if (b.is_empty()) {
                return;
            }
        }
    } while (b.max_diam() > config.nra_precision && !m_term_cond(old_box, b));
    return;
}

void contractor_fixpoint::worklist_fixpoint_alg(box & b, SMTConfig & config) const {
    box old_box(b);
    m_input  = ibex::BitSet::empty(b.size());
    m_output = ibex::BitSet::empty(b.size());
    m_used_constraints.clear();
void contractor_fixpoint::worklist_fixpoint_alg(box & b, SMTConfig & config) {
    thread_local static queue<unsigned> q;
    queue<unsigned>().swap(q);  // empty queue
    thread_local static ibex::BitSet ctc_bitset = ibex::BitSet::empty(m_clist.size());
    ctc_bitset.clear();

    // Add all contractors to the queue.
    for (unsigned i = 0; i < m_clist.size(); ++i) {
        contractor & c_i = m_clist[i];
        q.push(i);
        c_i.prune(b, config);
        m_output.union_with(c_i.output());
        unordered_set<shared_ptr<constraint>> const & used_constraints = c_i.used_constraints();
        m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
        if (b.is_empty()) { return; }
        ibex::BitSet const & output_i = c_i.output();
        if (output_i.empty()) {
            continue;
        }
        for (int j = output_i.min(); j <= output_i.max(); ++j) {
            if (output_i.contain(j)) {
                // The applied constraint changes var_j
                for (unsigned k = 0; k < m_clist.size(); ++k) {
                    if (!ctc_bitset.contain(k)) {
                        // Need to find c_k whose input depends on var_j
                        contractor const & c_k = m_clist[k];
                        if (c_k.input().contain(j)) {
                            q.push(k);
                            ctc_bitset.add(k);
                            break;
                        }
                    }
                }
            }
        }
    }

    // Fixed Point Loop
    thread_local static box old_box(b);
    do {
        interruption_point();
        old_box = b;
        int const idx = q.front();
        q.pop();
        ctc_bitset.remove(idx);
        contractor & c = m_clist[idx];
        c.prune(b, config);
        m_output.union_with(c.output());
        unordered_set<shared_ptr<constraint>> const & used_constraints = c.used_constraints();
        m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
        if (b.is_empty()) { return; }
        auto const & c_output = c.output();
        if (c_output.empty()) {
            continue;
        }
        for (int j = c_output.min(); j <= c_output.max(); ++j) {
            if (c_output.contain(j)) {
                for (unsigned k = 0; k < m_clist.size(); ++k) {
                    if (!ctc_bitset.contain(k)) {
                        contractor const & c_k = m_clist[k];
                        if (c_k.input().contain(j)) {
                            q.push(k);
                            ctc_bitset.add(k);
                            break;
                        }
                    }
                }
            }
        }
    } while (q.size() != 0 && b.max_diam() >= config.nra_precision && !m_term_cond(old_box, b));
    return;
}

contractor_int::contractor_int(box const & b) : contractor_cell(contractor_kind::INT) {
    m_input = ibex::BitSet::empty(b.size());
    auto const & vars = b.get_vars();
    for (unsigned i = 0; i < b.size(); ++i) {
        Enode * const e = vars[i];
        if (e->hasSortInt()) {
            m_input.add(i);
        }
    }
    m_output = m_input;
    m_output.clear();
}

void contractor_int::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_int::prune";
    // ======= Proof =======
    thread_local static box old_box(b);
    if (config.nra_proof) { old_box = b; }
    unsigned i = 0;
    ibex::IntervalVector & iv = b.get_values();
    for (Enode * e : b.get_vars()) {
        if (e->hasSortInt()) {
            thread_local static ibex::Interval old_iv(iv[i]);
            old_iv = iv[i];
            iv[i] = ibex::integer(iv[i]);
            if (old_iv != iv[i]) {
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
    return;
}
ostream & contractor_int::display(ostream & out) const {
    out << "contractor_int()";
    return out;
}

contractor_eval::contractor_eval(shared_ptr<nonlinear_constraint> const ctr)
    : contractor_cell(contractor_kind::EVAL), m_nl_ctr(ctr) {
    auto const & var_array = m_nl_ctr->get_var_array();
    m_input = ibex::BitSet::empty(m_nl_ctr->get_var_array().size());
    for (int i = 0; i < var_array.size(); i++) {
        m_input.add(i);
    }
    m_output = m_input;
    m_output.clear();
}

void contractor_eval::prune(box & b, SMTConfig & config) {
    DREAL_LOG_DEBUG << "contractor_eval::prune";
    pair<lbool, ibex::Interval> eval_result = m_nl_ctr->eval(b);
    if (eval_result.first == l_False) {
        // ======= Proof =======
        if (config.nra_proof) {
            box old_box = b;
            b.set_empty();
            ostringstream ss;
            Enode const * const e = m_nl_ctr->get_enode();
            ss << (e->getPolarity() == l_False ? "!" : "") << e;
            output_pruning_step(config.nra_proof_out, old_box, b, config.nra_readable_proof, ss.str());
        } else {
            b.set_empty();
            m_output.flip();  // empty -> all
        }
        m_used_constraints.insert(m_nl_ctr);
    }
    return;
}
ostream & contractor_eval::display(ostream & out) const {
    out << "contractor_eval(" << *m_nl_ctr << ")";
    return out;
}

contractor_cache::contractor_cache(contractor const & ctc)
    : contractor_cell(contractor_kind::CACHE), m_ctc(ctc), m_num_hit(0), m_num_nohit(0) {
    m_input = m_ctc.input();
}

contractor_cache::~contractor_cache() {
    DREAL_LOG_FATAL << m_num_hit << " / " << (m_num_hit + m_num_nohit) << "\t" << m_cache.size();
}

vector<ibex::Interval> extract_from_box_using_bitset(box const & b, ibex::BitSet const & s) {
    vector<ibex::Interval> v;
    if (s.empty()) { return v; }
    for (int i = s.min(); i <= s.max(); ++i) {
        if (s.contain(i)) {
            v.push_back(b[i]);
        }
    }
    return v;
}

void update_box_using_bitset(box & b, vector<ibex::Interval> const & v, ibex::BitSet const & s) {
    if (s.empty()) { return; }
    unsigned v_idx = 0;
    for (int i = s.min(); i <= s.max(); ++i) {
        if (s.contain(i)) {
            b[i] = v[v_idx++];
        }
    }
}

void contractor_cache::prune(box & b, SMTConfig & config) {
    // extract i-th interval where `m_input[i] == 1`
    vector<ibex::Interval> in = extract_from_box_using_bitset(b, m_input);
    auto it = m_cache.find(in);
    if (it == m_cache.end()) {
        // not found in cache, run m_ctc
        ++m_num_nohit;
        m_ctc.prune(b, config);
        m_output = m_ctc.output();
        m_used_constraints = m_ctc.used_constraints();

        // extract out from box.
        vector<ibex::Interval> out = extract_from_box_using_bitset(b, m_output);

        // save to the cache
        m_cache.emplace(in, make_tuple(out, m_output, m_used_constraints));
    } else {
        ++m_num_hit;
        // found in cache, use it
        auto const & m_cached_content = it->second;
        vector<ibex::Interval> out = get<0>(m_cached_content);
        m_output = get<1>(m_cached_content);
        m_used_constraints = get<2>(m_cached_content);

        // project out to box;
        update_box_using_bitset(b, out, m_output);
    }
}

ostream & contractor_cache::display(ostream & out) const {
    out << "contractor_cache(" << m_ctc << ")";
    return out;
}

contractor_sample::contractor_sample(box const & b, unsigned const n, vector<shared_ptr<constraint>> const & ctrs)
    : contractor_cell(contractor_kind::SAMPLE), m_num_samples(n), m_ctrs(ctrs) {
    m_input = ibex::BitSet::all(b.size());
    m_output = ibex::BitSet::empty(b.size());
}

void contractor_sample::prune(box & b, SMTConfig &) {
    DREAL_LOG_DEBUG << "contractor_sample::prune";
    // Sample n points
    set<box> points = b.sample_points(m_num_samples);
    // If ∃p. ∀c. eval(c, p) = true, return 'SAT'
    unsigned count = 0;
    for (box const & p : points) {
        interruption_point();
        DREAL_LOG_DEBUG << "contractor_sample::prune -- sample " << ++count << "th point = " << p;
        bool check = true;
        for (shared_ptr<constraint> const ctr : m_ctrs) {
            if (ctr->get_type() == constraint_type::Nonlinear) {
                auto const nl_ctr = dynamic_pointer_cast<nonlinear_constraint>(ctr);
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
            b = p;
            m_output = ibex::BitSet::all(b.size());
            m_used_constraints.insert(m_ctrs.begin(), m_ctrs.end());
            return;
        }
    }
    return;
}

ostream & contractor_sample::display(ostream & out) const {
    out << "contractor_sample(" << m_num_samples << ")";
    return out;
}

contractor_aggressive::contractor_aggressive(unsigned const n, vector<shared_ptr<constraint>> const & ctrs)
    : contractor_cell(contractor_kind::SAMPLE), m_num_samples(n), m_ctrs(ctrs) {
    // TODO(soonhok): set up input
    // m_input = ibex::BitSet::all(b.size());
}

void contractor_aggressive::prune(box & b, SMTConfig &) {
    DREAL_LOG_DEBUG << "contractor_eval::aggressive";
    // TODO(soonhok): set input & output
    // Sample n points
    set<box> points = b.sample_points(m_num_samples);
    // ∃c. ∀p. eval(c, p) = false   ===>  UNSAT
    for (shared_ptr<constraint> const ctr : m_ctrs) {
        interruption_point();
        if (ctr->get_type() == constraint_type::Nonlinear) {
            auto const nl_ctr = dynamic_pointer_cast<nonlinear_constraint>(ctr);
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
                return;
            }
        }
    }
    return;
}

ostream & contractor_aggressive::display(ostream & out) const {
    out << "contractor_aggressive(" << m_num_samples << ")";
    return out;
}
contractor mk_contractor_id() {
    return contractor(make_shared<contractor_id>());
}
contractor mk_contractor_seq(initializer_list<contractor> const & l) {
    if (l.size() == 0) {
        return mk_contractor_id();
    }
    return contractor(make_shared<contractor_seq>(l));
}
contractor mk_contractor_seq(vector<contractor> const & v) {
    if (v.size() == 0) {
        return mk_contractor_id();
    }
    return contractor(make_shared<contractor_seq>(v));
}
contractor mk_contractor_seq(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_seq>(c1, c2));
}
contractor mk_contractor_try(contractor const & c) {
    return contractor(make_shared<contractor_try>(c));
}
contractor mk_contractor_try_or(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_try_or>(c1, c2));
}
contractor mk_contractor_throw() {
    return contractor(make_shared<contractor_throw>());
}
contractor mk_contractor_throw_if_empty(contractor const & c) {
    return contractor(make_shared<contractor_throw_if_empty>(c));
}
contractor mk_contractor_join(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_join>(c1, c2));
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
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, initializer_list<vector<contractor>> const & cvec_list) {
    return contractor(make_shared<contractor_fixpoint>(guard, cvec_list));
}
contractor mk_contractor_int(box const & b) {
    return contractor(make_shared<contractor_int>(b));
}
contractor mk_contractor_eval(shared_ptr<nonlinear_constraint> const ctr, bool const use_cache) {
    if (!use_cache) {
        return contractor(make_shared<contractor_eval>(ctr));
    }
    static unordered_map<shared_ptr<nonlinear_constraint>, contractor> eval_ctc_cache;
    auto const it = eval_ctc_cache.find(ctr);
    if (it == eval_ctc_cache.end()) {
        contractor ctc(make_shared<contractor_eval>(ctr));
        eval_ctc_cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}
contractor mk_contractor_cache(contractor const & ctc) {
    return contractor(make_shared<contractor_cache>(ctc));
}
contractor mk_contractor_sample(box const & b, unsigned const n, vector<shared_ptr<constraint>> const & ctrs) {
    return contractor(make_shared<contractor_sample>(b, n, ctrs));
}
contractor mk_contractor_aggressive(unsigned const n, vector<shared_ptr<constraint>> const & ctrs) {
    return contractor(make_shared<contractor_aggressive>(n, ctrs));
}
ostream & operator<<(ostream & out, contractor const & c) {
    out << *(c.m_ptr);
    return out;
}

void contractor::prune_with_assert(box & b, SMTConfig & config) {
    assert(m_ptr != nullptr);
    thread_local static box old_box(b);
    old_box = b;
    m_ptr->prune(b, config);
    if (!b.is_subset(old_box)) {
        cerr << "Pruning Violation: " << (*m_ptr) << endl;
        cerr << "Old Box" << endl
             << "==============" << endl
             << old_box << endl;
        cerr << "New Box" << endl
             << "==============" << endl
             << b << endl;
        cerr << "==============" << endl;
        display_diff(cerr, old_box, b);
        cerr << "==============" << endl;
        exit(1);
    }
}
}  // namespace dreal
