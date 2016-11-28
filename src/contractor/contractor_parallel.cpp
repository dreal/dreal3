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

#include "contractor/contractor_parallel.h"

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
#include "contractor/contractor_exception.h"
#include "contractor/contractor_status.h"
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

ostream & operator<<(ostream & out, pruning_thread_status const & s) {
    switch (s) {
        case pruning_thread_status::READY:
            out << "READY";
            break;
        case pruning_thread_status::RUNNING:
            out << "RUNNING";
            break;
        case pruning_thread_status::SAT:
            out << "SAT";
            break;
        case pruning_thread_status::UNSAT:
            out << "UNSAT";
            break;
        case pruning_thread_status::EXCEPTION:
            out << "EXCEPTION";
            break;
        case pruning_thread_status::KILLED:
            out << "KILLED";
            break;
    }
    return out;
}

#define PARALLEL_LOG DREAL_LOG_DEBUG

void parallel_helper_fn(unsigned const id, contractor & c, contractor_status & cs,
                        pruning_thread_status & ps, mutex & m, condition_variable & cv, int & index,
                        atomic_int & tasks_to_run) {
    ps = pruning_thread_status::RUNNING;
    PARALLEL_LOG << "parallel_helper: thread " << id << " is running. " << tasks_to_run
                 << "tasks to run";
    // PARALLEL_LOG << "parallel_helper: thread " << id << " ctc = " << c;
    try {
        c.prune(cs);
        if (cs.m_box.is_empty()) {
            // do something for UNSAT
            ps = pruning_thread_status::UNSAT;
            PARALLEL_LOG << "parallel_helper: thread " << id << " is UNSAT.";
        } else {
            ps = pruning_thread_status::SAT;
            PARALLEL_LOG << "parallel_helper: thread " << id << " is SAT.";
            // do something for SAT
        }
    } catch (contractor_exception & e) {
        // handle for exception
        ps = pruning_thread_status::EXCEPTION;
        PARALLEL_LOG << "parallel_helper: thread " << id
                     << " throws an contractor_exception: " << e.what();
    } catch (thread_interrupted & e) {
        // just killed
        ps = pruning_thread_status::KILLED;
        tasks_to_run--;
        PARALLEL_LOG << "parallel_helper: thread " << id << " is KILLED.";
        return;
    } catch (exception & e) {
        tasks_to_run--;
        PARALLEL_LOG << "parallel_helper: thread " << id
                     << " throws an unexpected exception: " << e.what();
        return;
    }
    PARALLEL_LOG << "parallel_helper: thread " << id << " is waiting for a mutex lock";
    unique_lock<mutex> lk(m);
    PARALLEL_LOG << "parallel_helper: thread " << id << " get a lock";
    index = id;
    tasks_to_run--;
    PARALLEL_LOG << "parallel_helper: thread " << id << " unlocks";
    lk.unlock();
    cv.notify_one();
    PARALLEL_LOG << "parallel_helper: thread " << id << " notifies CV";
    return;
}
}  // namespace dreal
