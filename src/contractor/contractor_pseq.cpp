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

#include "contractor/contractor_pseq.h"

#include <algorithm>
#include <atomic>
#include <exception>
#include <functional>
#include <future>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <memory>
#include <queue>
#include <set>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "contractor/contractor.h"
#include "contractor/extract_bitset.h"
#include "ibex/ibex.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/thread_local.h"

using std::async;
using std::back_inserter;
using std::cerr;
using std::condition_variable;
using std::cout;
using std::endl;
using std::function;
using std::future;
using std::initializer_list;
using std::make_pair;
using std::make_shared;
using std::mutex;
using std::min;
using std::max;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::ref;
using std::set;
using std::shared_ptr;
using std::unique_lock;
using std::lock_guard;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::atomic_int;
using std::thread;
using std::exception;

namespace dreal {

contractor_pseq::contractor_pseq(initializer_list<contractor> const & l)
    : contractor_cell{contractor_kind::PSEQ, extract_bitset(l)}, m_vec{l} {
    init();
}
contractor_pseq::contractor_pseq(vector<contractor> const & v)
    : contractor_cell{contractor_kind::PSEQ, extract_bitset(v)}, m_vec{v} {
    init();
}

void contractor_pseq::init() {
    DREAL_LOG_DEBUG << "contractor_pseq::prune";

    auto const num_thread =
        min(thread::hardware_concurrency(), static_cast<unsigned>(m_vec.size()));

    cerr << m_vec.size() << " constraints\t" << num_thread << " threads" << endl;

    if (m_vec.size() < num_thread) {
        m_ctc = mk_contractor_seq(m_vec);
        m_use_threads = false;
        return;
    }

    vector<vector<contractor>> vv(num_thread);
    vector<contractor> v(num_thread);
    for (unsigned i = 0; i < m_vec.size(); i++) {
        vv[i % num_thread].push_back(m_vec[i]);
    }
    for (unsigned i = 0; i < num_thread; i++) {
        cerr << "vv[" << i << "].size() = " << vv[i].size() << endl;
        v[i] = mk_contractor_seq(vv[i]);
    }
    m_ctc = mk_contractor_parallel_all(v);
    m_use_threads = true;
}

void contractor_pseq::prune(contractor_status & cs) {
    if (m_use_threads) {
        unsigned num_iter = m_vec.size() / thread::hardware_concurrency();
        if (num_iter == 0) {
            num_iter = 1;
        }
        DREAL_THREAD_LOCAL static box old_box(cs.m_box);
        for (unsigned i = 0; i < num_iter; i++) {
            // interruption_point();
            old_box = cs.m_box;
            m_ctc.prune(cs);
            if (cs.m_box.is_empty()) {
                cerr << "pseq::prune - empty detected\t" << i << "/" << num_iter << endl;
                return;
            }
            if (old_box == cs.m_box) {
                // reach the fixpoint
                cerr << "pseq::prune - fixpoint detected\t" << i << "/" << num_iter << endl;
                return;
            }
        }
        return;
    } else {
        // use single thread
        m_ctc.prune(cs);
        return;
    }
}

ostream & contractor_pseq::display(ostream & out) const {
    out << "contractor_pseq(";
    for (contractor const & c : m_vec) {
        out << c << ", ";
    }
    out << ")";
    return out;
}

contractor mk_contractor_pseq(initializer_list<contractor> const & l) {
    return contractor(make_shared<contractor_pseq>(l));
}
contractor mk_contractor_pseq(vector<contractor> const & v) {
    return contractor(make_shared<contractor_pseq>(v));
}

}  // namespace dreal
