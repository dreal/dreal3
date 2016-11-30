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

#include "contractor/contractor_parallel_all.h"

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

#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "contractor/contractor_kind.h"
#include "contractor/contractor_parallel.h"
#include "contractor/contractor_status.h"
#include "contractor/extract_bitset.h"
#include "ibex/ibex.h"
#include "util/box.h"
#include "util/interruptible_thread.h"
#include "util/logging.h"

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

contractor_parallel_all::contractor_parallel_all(initializer_list<contractor> const & l)
    : contractor_cell{contractor_kind::PARALLEL_ALL, extract_bitset(l)}, m_vec{l} {}
contractor_parallel_all::contractor_parallel_all(vector<contractor> const & v)
    : contractor_cell{contractor_kind::PARALLEL_ALL, extract_bitset(v)}, m_vec{v} {}
contractor_parallel_all::contractor_parallel_all(contractor const & c1, contractor const & c2)
    : contractor_cell{contractor_kind::PARALLEL_ALL, {c1.get_input(), c2.get_input()}},
      m_vec{c1, c2} {}

void contractor_parallel_all::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_parallel_all::prune";
    DREAL_LOG_FATAL << "-------------------------------------------------------------";
    // TODO(soonhok): implement this
    if (m_vec.size() == 0) {
        // Do nothing for empty vec
        return;
    }

    // 1. Make n copies of contractor_status
    vector<contractor_status> ctc_statuses(m_vec.size(), cs);
    vector<pruning_thread_status> thread_statuses(m_vec.size(), pruning_thread_status::READY);
    m_index = -1;

    // DREAL_LOG_FATAL << "parallel: Boxes are copied";

    // 2. Trigger execution with each contractor and a copied box
    vector<interruptible_thread> threads;
    atomic_int tasks_to_run(m_vec.size());
    // DREAL_LOG_FATAL << "parallel: tasks to run = " << tasks_to_run.load();
    for (unsigned i = 0; i < m_vec.size(); ++i) {
        DREAL_LOG_FATAL << "parallel : thread " << i << " / " << (tasks_to_run.load() - 1)
                        << " spawning...";

        threads.emplace_back(parallel_helper_fn, i, m_vec[i], ctc_statuses[i], thread_statuses[i],
                             m_mutex, m_cv, m_index, tasks_to_run);
        DREAL_LOG_FATAL << "parallel : thread " << i << " / " << (tasks_to_run.load() - 1)
                        << " spawned...";
    }
    DREAL_LOG_FATAL << "parallel : " << m_vec.size() << " thread(s) got created";

    while (true) {
        DREAL_LOG_FATAL << "parallel: waiting for the lock";
        unique_lock<mutex> lk(m_mutex);
        DREAL_LOG_FATAL << "parallel: get a lock. " << tasks_to_run.load() << " tasks to go";
        if (tasks_to_run.load() == 0) {
            break;
        }
        DREAL_LOG_FATAL << "parallel: WAIT for CV." << tasks_to_run.load() << " tasks to go";
        m_index = -1;
        m_cv.wait(lk, [&]() { return m_index != -1; });
        DREAL_LOG_FATAL << "parallel: wake up" << tasks_to_run.load();
        pruning_thread_status const & s = thread_statuses[m_index];
        // DREAL_LOG_FATAL << "parallel: thread " << m_index << " " << s;
        if (s == pruning_thread_status::UNSAT || s == pruning_thread_status::EXCEPTION) {
            // Interrupt all the rest threads
            for (unsigned i = 0; i < thread_statuses.size(); i++) {
                if (i - m_index != 0 && (thread_statuses[i] == pruning_thread_status::READY ||
                                         thread_statuses[i] == pruning_thread_status::RUNNING)) {
                    threads[i].interrupt();
                }
            }

            if (s == pruning_thread_status::UNSAT) {
                DREAL_LOG_FATAL << "parallel: " << m_index << " got UNSAT";
                cs.m_box.set_empty();
                cs.m_output.union_with(ctc_statuses[m_index].m_output);
                unordered_set<shared_ptr<constraint>> const & used_ctrs =
                    ctc_statuses[m_index].m_used_constraints;
                cs.m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
                lk.unlock();
                for (unsigned i = 0; i < m_vec.size(); i++) {
                    threads[i].join();
                }
                DREAL_LOG_FATAL << "parallel: return UNSAT";
                return;
            }
            if (s == pruning_thread_status::EXCEPTION) {
                DREAL_LOG_FATAL << "parallel: " << m_index << " got EXCEPTION";
                lk.unlock();
                for (unsigned i = 0; i < m_vec.size(); i++) {
                    threads[i].join();
                }
                DREAL_LOG_FATAL << "parallel: throw exception";
                throw contractor_exception("exception during parallel contraction");
            }

        } else {
            // if (s != pruning_thread_status::SAT) {
            //     // DREAL_LOG_FATAL << "parallel: " << m_index << " got " << s;
            //     // DREAL_LOG_FATAL << "parallel: " << m_index << " got " <<
            //     thread_statuses[m_index];
            assert(s == pruning_thread_status::SAT);
            // }
            // if (threads[m_index].joinable()) {
            // threads[m_index].join();
            // }
            // DREAL_LOG_FATAL << "parallel: " << m_index << " got SAT";
            // Why?
            //  - Not READY/RUNNING: It's a job already done.
            //  - Not UNSAT/EXCEPTION: already handled above.
            //  - Not KILLED: There must be one which kill the killed
            //                job, and this loop stops after handling
            //                the first one
        }
    }

    // Assertion: All of them got SAT
    // for (pruning_thread_status const & s : thread_statuses) {
    //     assert(s == pruning_thread_status::SAT);
    // }

    // DREAL_LOG_FATAL << "All of them are SAT";
    cs.m_box = ctc_statuses[0].m_box;
    for (unsigned i = 0; i < m_vec.size(); i++) {
        cs.m_output.union_with(ctc_statuses[i].m_output);
        unordered_set<shared_ptr<constraint>> const & used_ctrs =
            ctc_statuses[i].m_used_constraints;
        cs.m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        cs.m_box.intersect(ctc_statuses[i].m_box);
        if (cs.m_box.is_empty()) {
            // DREAL_LOG_FATAL << "Found an empty while intersecting...";
            for (unsigned i = 0; i < m_vec.size(); i++) {
                // if (threads[i].joinable()) {
                // DREAL_LOG_FATAL << "Try to join " << i << "...";
                threads[i].join();
                // DREAL_LOG_FATAL << "Try to join " << i << "... done";
                // }
            }
            // DREAL_LOG_FATAL << "parallel: return UNSAT";
            return;
        }
    }
    // DREAL_LOG_FATAL << "Intersection is nonempty exiting...";
    for (unsigned i = 0; i < m_vec.size(); i++) {
        // if (threads[i].joinable()) {
        threads[i].join();
        // }
    }
    // DREAL_LOG_FATAL << "parallel: return SAT";
    return;
}
ostream & contractor_parallel_all::display(ostream & out) const {
    out << "contractor_parallel_all(";
    for (contractor const & c : m_vec) {
        out << c << ", ";
    }
    out << ")";
    return out;
}

}  // namespace dreal
