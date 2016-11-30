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

#include "contractor/contractor_parallel_any.h"

#include <algorithm>
#include <atomic>
#include <cassert>
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

#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "contractor/contractor_parallel.h"
#include "contractor/extract_bitset.h"
#include "ibex/ibex.h"
#include "util/box.h"
#include "util/interruptible_thread.h"
#include "util/logging.h"

using std::async;
using std::atomic_int;
using std::back_inserter;
using std::cerr;
using std::condition_variable;
using std::cout;
using std::endl;
using std::exception;
using std::function;
using std::future;
using std::initializer_list;
using std::lock_guard;
using std::make_pair;
using std::make_shared;
using std::max;
using std::min;
using std::mutex;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::ref;
using std::set;
using std::shared_ptr;
using std::thread;
using std::unique_lock;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {

contractor_parallel_any::contractor_parallel_any(initializer_list<contractor> const & l)
    : contractor_cell{contractor_kind::PARALLEL_ANY, extract_bitset(l)}, m_vec{l} {}
contractor_parallel_any::contractor_parallel_any(vector<contractor> const & v)
    : contractor_cell{contractor_kind::PARALLEL_ANY, extract_bitset(v)}, m_vec{v} {}
contractor_parallel_any::contractor_parallel_any(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::PARALLEL_ANY, {c1.get_input(), c2.get_input()}),
      m_vec{c1, c2} {}

#define PARALLEL_LOG DREAL_LOG_DEBUG

void contractor_parallel_any::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_parallel_any::prune";
    PARALLEL_LOG << "-------------------------------------------------------------";
    if (m_vec.size() == 0) {
        // Do nothing for empty vec
        return;
    }

    // 1. Make n copies of contractor_status
    vector<contractor_status> ctc_statuses(m_vec.size(), cs);
    vector<pruning_thread_status> thread_statuses(m_vec.size(), pruning_thread_status::READY);
    m_index = -1;

    // PARALLEL_LOG << "parallel_any: Boxes are copied";

    // 2. Trigger execution with each contractor and a copied box
    vector<interruptible_thread> threads;
    atomic_int tasks_to_run(m_vec.size());
    // PARALLEL_LOG << "parallel_any: tasks to run = " << tasks_to_run.load();
    for (unsigned i = 0; i < m_vec.size(); ++i) {
        PARALLEL_LOG << "parallel_any: thread " << i << " / " << (tasks_to_run.load() - 1)
                     << " spawning...";
        threads.emplace_back(parallel_helper_fn, i, m_vec[i], ctc_statuses[i], thread_statuses[i],
                             m_mutex, m_cv, m_index, tasks_to_run);
        PARALLEL_LOG << "parallel_any: thread " << i << " / " << (tasks_to_run.load() - 1)
                     << " spawned...";
    }
    PARALLEL_LOG << "parallel_any: " << m_vec.size() << " thread(s) got created";

    while (true) {
        PARALLEL_LOG << "parallel_any: waiting for the lock";
        unique_lock<mutex> lk(m_mutex);
        PARALLEL_LOG << "parallel_any: get a lock. " << tasks_to_run.load() << " tasks to go";
        if (tasks_to_run.load() == 0) {
            break;
        }
        PARALLEL_LOG << "parallel_any: WAIT for CV." << tasks_to_run.load() << " tasks to go";
        m_index = -1;
        m_cv.wait(lk, [&]() { return m_index != -1; });
        PARALLEL_LOG << "parallel_any: wake up" << tasks_to_run.load();
        pruning_thread_status const & s = thread_statuses[m_index];
        // PARALLEL_LOG << "parallel_any: thread " << m_index << " " << s;
        if (s == pruning_thread_status::SAT || s == pruning_thread_status::EXCEPTION) {
            // Interrupt all the rest threads
            for (unsigned i = 0; i < thread_statuses.size(); i++) {
                if (i - m_index != 0 && (thread_statuses[i] == pruning_thread_status::READY ||
                                         thread_statuses[i] == pruning_thread_status::RUNNING)) {
                    threads[i].interrupt();
                }
            }

            if (s == pruning_thread_status::SAT) {
                PARALLEL_LOG << "parallel_any: " << m_index << " got SAT";
                cs.reset(ctc_statuses[m_index]);
                lk.unlock();
                for (unsigned i = 0; i < m_vec.size(); i++) {
                    threads[i].join();
                }
                PARALLEL_LOG << "parallel_any: return SAT";
                return;
            }
            if (s == pruning_thread_status::EXCEPTION) {
                PARALLEL_LOG << "parallel_any: " << m_index << " got EXCEPTION";
                lk.unlock();
                for (unsigned i = 0; i < m_vec.size(); i++) {
                    threads[i].join();
                }
                PARALLEL_LOG << "parallel_any: throw exception";
                throw contractor_exception("exception during parallel contraction");
            }

        } else {
            assert(s == pruning_thread_status::UNSAT);
            // Why?
            //  - Not READY/RUNNING: It's a job already done.
            //  - Not SAT/EXCEPTION: already handled above.
            //  - Not KILLED: There must be one which kill the killed
            //                job, and this loop stops after handling
            //                the first one
        }
    }

    // Assertion: All of them got UNSAT
    // for (pruning_thread_status const & s : thread_statuses) {
    //     assert(s == pruning_thread_status::UNSAT);
    // }
    // PARALLEL_LOG << "All of them are UNSAT";
    cs.m_box.set_empty();

    // TODO(soonhok): the following could be simplified. When all of
    // contractors return UNSATs, we can simply pick up a contractor
    // and only propagate information from that contractor while
    // ignoring the rest of contractors.
    for (unsigned i = 0; i < m_vec.size(); i++) {
        cs.m_output.union_with(ctc_statuses[i].m_output);
        unordered_set<shared_ptr<constraint>> const & used_ctrs =
            ctc_statuses[i].m_used_constraints;
        cs.m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
    }
    for (unsigned i = 0; i < m_vec.size(); i++) {
        threads[i].join();
    }
    PARALLEL_LOG << "parallel_any: return UNSAT";
    return;
}
ostream & contractor_parallel_any::display(ostream & out) const {
    out << "contractor_parallel_any(";
    for (contractor const & c : m_vec) {
        out << c << ", ";
    }
    out << ")";
    return out;
}

}  // namespace dreal
