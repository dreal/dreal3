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

#include <functional>
#include <queue>
#include <string>
#include <vector>
#include "constraint/constraint.h"
#include "contractor/contractor_basic.h"
#include "contractor/contractor_common.h"
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

void contractor_fixpoint::init() {
    m_input = m_clist[0].get_input();
    for (unsigned i = 1; i < m_clist.size(); ++i) {
        m_input.union_with(m_clist[i].get_input());
    }
}

contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, contractor const & c)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(1, c), m_old_box({}) {
    init();
}
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, initializer_list<contractor> const & clist)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(clist), m_old_box({}) {
    assert(m_clist.size() > 0);
    init();
}
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, vector<contractor> const & cvec)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(cvec), m_old_box({}) {
    assert(m_clist.size() > 0);
    init();
}
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, initializer_list<vector<contractor>> const & cvec_list)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(), m_old_box({}) {
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
    do {
        interruption_point();
        m_old_box = cs.m_box;
        contractor & c = m_clist[i];
        c.prune(cs);
        if (cs.m_box.is_empty()) {
            return;
        }
        i = (i + 1) % m_clist.size();
    } while (m_old_box != cs.m_box && cs.m_box.is_bisectable(cs.m_config.nra_precision) && !m_term_cond(m_old_box, cs.m_box));
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
    do {
        interruption_point();
        m_old_box = cs.m_box;
        unsigned const idx = q.front();
        q.pop();
        ctc_bitset.remove(idx);
        assert(!ctc_bitset.contain(idx));
        assert(idx < m_clist.size());
        contractor & c = m_clist[idx];
        contractor_status_guard csg(cs);
        c.prune(cs);

        // (m_old_box == new_box -> output == empty)
        assert(!(m_old_box == cs.m_box) || cs.m_output.empty());
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
    } while (q.size() > 0 && (m_old_box != cs.m_box) && cs.m_box.is_bisectable(cs.m_config.nra_precision) && !m_term_cond(m_old_box, cs.m_box));
    return;
}
}  // namespace dreal
