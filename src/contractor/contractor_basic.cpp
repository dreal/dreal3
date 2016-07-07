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
#include <chrono>
#include <exception>
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
#include "contractor/contractor_common.h"
#include "contractor/contractor_basic.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/interruptible_thread.h"
#include "util/logging.h"
#include "util/proof.h"

using std::cerr;
using std::cout;
using std::dynamic_pointer_cast;
using std::endl;
using std::exception;
using std::function;
using std::get;
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
using std::string;
using std::tuple;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {

contractor_id::contractor_id()
    : contractor_cell(contractor_kind::ID) {
}
void contractor_id::prune(contractor_status &) {
    return;
}
ostream & contractor_id::display(ostream & out) const {
    out << "contractor_id()";
    return out;
}

contractor_debug::contractor_debug(string const & s)
    : contractor_cell(contractor_kind::DEBUG), m_msg(s) {
}
void contractor_debug::prune(contractor_status &) {
    DREAL_LOG_FATAL << "contractor_debug: " << m_msg;
}
ostream & contractor_debug::display(ostream & out) const {
    out << "contractor_debug(" << m_msg << ")";
    return out;
}

void contractor_seq::init() {
    m_input = m_vec[0].get_input();
    for (unsigned i = 1; i < m_vec.size(); ++i) {
        m_input.union_with(m_vec[i].get_input());
    }
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
void contractor_seq::prune_naive(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_seq::prune";
    for (contractor & c : m_vec) {
        interruption_point();
        c.prune(cs);
        if (cs.m_box.is_empty()) {
            return;
        }
    }
    return;
}

void contractor_seq::prune(contractor_status & cs) {
    if (m_vec.size() == 0) { return; }
    prune_naive(cs);
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
    m_input = m_c.get_input();
}
void contractor_try::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_try::prune: ";
    contractor_status old_cs(cs);
    try {
        m_c.prune(cs);
    } catch (contractor_exception & e) {
        DREAL_LOG_INFO << "contractor_try: exception caught, \""
                       << e.what() << "\n";
        cs.reset(old_cs);
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
    m_input = m_c1.get_input();
    m_input.union_with(m_c2.get_input());
}
void contractor_try_or::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_try_or::prune";
    contractor_status old_cs(cs);
    try {
        m_c1.prune(cs);
    } catch (contractor_exception & e) {
        cs.reset(old_cs);
        m_c2.prune(cs);
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
    m_input = m_c.get_input();
}
void contractor_throw_if_empty::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_throw_if_empty::prune";
    m_c.prune(cs);
    if (cs.m_box.is_empty()) {
        throw contractor_exception("throw if empty");
    }
}
ostream & contractor_throw_if_empty::display(ostream & out) const {
    out << "contractor_throw_if_empty(" << m_c << ")";
    return out;
}

contractor_join::contractor_join(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::JOIN), m_c1(c1), m_c2(c2) {
    m_input = m_c1.get_input();
    m_input.union_with(m_c2.get_input());
}
void contractor_join::prune(contractor_status & cs1) {
    DREAL_LOG_DEBUG << "contractor_join::prune";
    // duplicate cs1
    contractor_status cs2(cs1);
    // run m_c1
    m_c1.prune(cs1);
    // run m_c2 on b1
    m_c2.prune(cs2);
    cs1.join(cs2);
}
ostream & contractor_join::display(ostream & out) const {
    out << "contractor_join(" << m_c1 << ", " << m_c2 << ")";
    return out;
}

contractor_ite::contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else)
    : contractor_cell(contractor_kind::ITE), m_guard(guard), m_c_then(c_then), m_c_else(c_else) {
    m_input = m_c_then.get_input();
    m_input.union_with(m_c_else.get_input());
}
void contractor_ite::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_ite::prune";
    if (m_guard(cs.m_box)) {
        m_c_then.prune(cs);
    } else {
        m_c_else.prune(cs);
    }
}

ostream & contractor_ite::display(ostream & out) const {
    out << "contractor_ite(" << m_c_then << ", " << m_c_else << ")";
    return out;
}

void contractor_fixpoint::init() {
    m_input = m_clist[0].get_input();
    for (unsigned i = 1; i < m_clist.size(); ++i) {
        m_input.union_with(m_clist[i].get_input());
    }
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

void contractor_fixpoint::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_fix::prune -- begin";
    if (cs.m_config.nra_worklist_fp) {
        worklist_fixpoint_alg(cs);
        DREAL_LOG_DEBUG << "contractor_fix::prune -- end";
        return;
    } else {
        naive_fixpoint_alg(cs);
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

void contractor_fixpoint::naive_fixpoint_alg(contractor_status & cs) {
    // First Iteration (run always)
    for (contractor & c : m_clist) {
        interruption_point();
        c.prune(cs);
        if (cs.m_box.is_empty()) {
            return;
        }
    }
    unsigned i = 0;
    // Next Iterations: stop when 1) a box is smaller enough or 2) termination condition holds
    thread_local static box old_box(cs.m_box);
    do {
        interruption_point();
        old_box = cs.m_box;
        contractor & c = m_clist[i];
        c.prune(cs);
        if (cs.m_box.is_empty()) {
            return;
        }
        i = (i + 1) % m_clist.size();
    } while (cs.m_box.max_diam() > cs.m_config.nra_precision && !m_term_cond(old_box, cs.m_box));
    return;
}

void contractor_fixpoint::worklist_fixpoint_alg(contractor_status & cs) {
    thread_local static queue<unsigned> q;
    q = queue<unsigned>();  // empty queue
    thread_local static ibex::BitSet ctc_bitset = ibex::BitSet::empty(m_clist.size());
    ctc_bitset = ibex::BitSet::empty(m_clist.size());
    // Add all contractors to the queue.
    for (unsigned i = 0; i < m_clist.size(); ++i) {
        contractor & c_i = m_clist[i];
        contractor_status_guard csg(cs);
        c_i.prune(cs);
        if (cs.m_box.is_empty()) { return; }
        ibex::BitSet const & output_i = cs.m_output;
        if (output_i.empty()) {
            continue;
        }
        assert(!ctc_bitset.contain(i));
        q.push(i);
        ctc_bitset.add(i);
    }

    if (q.size() == 0) { return; }
    // Fixed Point Loop
    thread_local static box old_box(cs.m_box);
    do {
        interruption_point();
        old_box = cs.m_box;
        unsigned const idx = q.front();
        q.pop();
        ctc_bitset.remove(idx);
        assert(!ctc_bitset.contain(idx));
        assert(idx < m_clist.size());
        contractor & c = m_clist[idx];
        contractor_status_guard csg(cs);
        c.prune(cs);

        // (old_box == new_box -> output == empty)
        assert(!(old_box == cs.m_box) || cs.m_output.empty());
        if (cs.m_box.is_empty()) {
            return;
        }
        auto const & c_output = cs.m_output;
        if (!c_output.empty()) {
            // j-th dimension is changed as a result of pruning
            // need to add a contractor which takes j-th dim as an input
            for (int j = c_output.min(); j <= c_output.max(); ++j) {
                if (!c_output.contain(j)) {
                    continue;
                }
                for (unsigned k = 0; k < m_clist.size(); ++k) {
                    // Only add if it's not in the current queue
                    if (!ctc_bitset.contain(k)) {
                        contractor const & c_k = m_clist[k];
                        auto const & c_k_input = c_k.get_input();
                        if (c_k_input.contain(j)) {
                            assert(!ctc_bitset.contain(k));
                            q.push(k);
                            ctc_bitset.add(k);
                        }
                    }
                }
            }
        }
    } while (q.size() > 0 && cs.m_box.max_diam() >= cs.m_config.nra_precision && !m_term_cond(old_box, cs.m_box));
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
}

void contractor_int::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_int::prune";
    if (m_input.empty()) {
        return;
    }
    // ======= Proof =======
    thread_local static box old_box(cs.m_box);
    if (cs.m_config.nra_proof) { old_box = cs.m_box; }
    unsigned i = 0;
    ibex::IntervalVector & iv = cs.m_box.get_values();
    for (Enode * e : cs.m_box.get_vars()) {
        if (e->hasSortInt()) {
            thread_local static ibex::Interval old_iv(iv[i]);
            old_iv = iv[i];
            iv[i] = ibex::integer(iv[i]);
            if (old_iv != iv[i]) {
                cs.m_output.add(i);
            }
            if (iv[i].is_empty()) {
                cs.m_box.set_empty();
                break;
            }
        }
        i++;
    }
    // ======= Proof =======
    if (cs.m_config.nra_proof) {
        output_pruning_step(old_box, cs, "integer pruning");
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
}

void contractor_eval::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_eval::prune";
    pair<lbool, ibex::Interval> eval_result = m_nl_ctr->eval(cs.m_box);
    if (eval_result.first == l_False) {
        // ======= Proof =======
        if (cs.m_config.nra_proof) {
            box const old_box = cs.m_box;
            cs.m_box.set_empty();
            ostringstream ss;
            Enode const * const e = m_nl_ctr->get_enode();
            ss << (e->getPolarity() == l_False ? "!" : "") << e;
            output_pruning_step(old_box, cs, ss.str());
        } else {
            cs.m_box.set_empty();
            cs.m_output.fill();
        }
        cs.m_used_constraints.insert(m_nl_ctr);
    }
    return;
}
ostream & contractor_eval::display(ostream & out) const {
    out << "contractor_eval(" << *m_nl_ctr << ")";
    return out;
}

contractor_cache::contractor_cache(contractor const & ctc)
    : contractor_cell(contractor_kind::CACHE), m_ctc(ctc), m_num_hit(0), m_num_nohit(0) {
    m_input = m_ctc.get_input();
}

contractor_cache::~contractor_cache() {
    DREAL_LOG_DEBUG << m_num_hit << " / " << (m_num_hit + m_num_nohit) << "\t" << m_cache.size();
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

void contractor_cache::prune(contractor_status & cs) {
    // extract i-th interval where `m_input[i] == 1`
    vector<ibex::Interval> const in = extract_from_box_using_bitset(cs.m_box, m_input);
    auto const it = m_cache.find(in);
    if (it == m_cache.end()) {
        // not found in cache, run m_ctc
        ++m_num_nohit;
        {
            contractor_status_guard csg(cs);
            assert(cs.m_output.empty());
            assert(cs.m_used_constraints.empty());
            try {
                // run contractor
                m_ctc.prune(cs);
                // extract out from box.
                vector<ibex::Interval> const out = extract_from_box_using_bitset(cs.m_box, cs.m_output);
                // save the result to the cache
                m_cache.emplace(in, make_tuple(out, cs.m_output, cs.m_used_constraints, false));
            } catch (exception & e) {
                m_cache.emplace(in, make_tuple(vector<ibex::Interval>(), cs.m_output, cs.m_used_constraints, true));
                throw contractor_exception(e.what());
            }
        }
    } else {
        ++m_num_hit;
        // found in cache, use it
        auto const & m_cached_content = it->second;
        vector<ibex::Interval> const & out = get<0>(m_cached_content);
        auto const & output_bitset = get<1>(m_cached_content);
        auto const & used_constraints = get<2>(m_cached_content);
        bool const was_exception_thrown = get<3>(m_cached_content);
        cs.m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
        if (was_exception_thrown) {
            cs.m_output.union_with(output_bitset);
            throw contractor_exception("previously there was an exception in the cached computation");
        } else {
            // project out to box;
            update_box_using_bitset(cs.m_box, out, output_bitset);
            cs.m_output.union_with(output_bitset);
        }
    }
}

ostream & contractor_cache::display(ostream & out) const {
    out << "contractor_cache(" << m_ctc << ")";
    return out;
}

contractor_sample::contractor_sample(box const & b, unsigned const n, vector<shared_ptr<constraint>> const & ctrs)
    : contractor_cell(contractor_kind::SAMPLE), m_num_samples(n), m_ctrs(ctrs) {
    m_input = ibex::BitSet::all(b.size());
}

void contractor_sample::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_sample::prune";
    // Sample n points
    set<box> points = cs.m_box.sample_points(m_num_samples);
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
            cs.m_box = p;
            cs.m_output = ibex::BitSet::all(cs.m_box.size());
            cs.m_used_constraints.insert(m_ctrs.begin(), m_ctrs.end());
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

void contractor_aggressive::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_eval::aggressive";
    // TODO(soonhok): set input & output
    // Sample n points
    set<box> points = cs.m_box.sample_points(m_num_samples);
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
                cs.m_used_constraints.insert(ctr);
                pair<lbool, ibex::Interval> eval_result = nl_ctr->eval(cs.m_box);
                DREAL_LOG_DEBUG << "Constraint: " << *nl_ctr << " is violated by all " << points.size() << " points";
                DREAL_LOG_DEBUG << "FYI, the interval evaluation gives us : " << eval_result.second;
                cs.m_box.set_empty();
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
contractor mk_contractor_debug(string const & s) {
    return contractor(make_shared<contractor_debug>(s));
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
contractor mk_contractor_empty() {
    return contractor(make_shared<contractor_empty>());
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
    if (c.m_ptr) {
        out << *(c.m_ptr);
    }
    return out;
}
}  // namespace dreal
