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
#include "util/thread_local.h"

using std::back_inserter;
using std::cerr;
using std::cout;
using std::endl;
using std::function;
using std::initializer_list;
using std::make_pair;
using std::make_shared;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::set;
using std::shared_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {
std::ostream & operator<<(std::ostream & out, ode_direction const & d) {
    switch (d) {
    case ode_direction::FWD:
        out << "FWD";
        break;
    case ode_direction::BWD:
        out << "BWD";
        break;
    }
    return out;
}

ostream & operator<<(ostream & out, contractor_cell const & c) {
    return c.display(out);
}

void contractor::prune_with_assert(contractor_status & cs) {
    assert(m_ptr != nullptr);
    DREAL_THREAD_LOCAL static box old_box(cs.m_box);
    old_box = cs.m_box;
    m_ptr->prune(cs);
    if (!cs.m_box.is_subset(old_box)) {
        ostringstream ss;
        ss << "Pruning Violation: " << (*m_ptr) << endl
           << "Old Box" << endl
           << "==============" << endl
           << old_box << endl
           << "New Box" << endl
           << "==============" << endl
           << cs.m_box << endl
           << "==============" << endl;
        display_diff(ss, old_box, cs.m_box);
        ss << "==============" << endl;
        DREAL_LOG_FATAL << ss.str();
        exit(1);
    }
}
}  // namespace dreal
