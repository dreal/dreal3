/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>

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

#include <iostream>
#include <chrono>
#include "util/stat.h"

using std::ostream;
using std::cerr;
using std::endl;

namespace dreal {

stat::stat() : m_start_time(std::chrono::high_resolution_clock::now()) {
    reset();
}

void stat::increase_check(bool complete) {
    if (complete) {
        m_num_of_complete_check++;
    } else {
        m_num_of_incomplete_check++;
    }
}

void stat::increase_assert() {
    m_num_of_assert++;
}

void stat::increase_push() {
    m_num_of_push++;
}

void stat::increase_pop() {
    m_num_of_pop++;
}

void stat::increase_branch() {
    m_num_of_branch++;
}

void stat::increase_prune() {
    m_num_of_prune++;
}

void stat::increase_non_trivial_prune() {
    m_num_of_non_trivial_prune++;
}

void stat::reset() {
    m_num_of_complete_check    = 0;
    m_num_of_incomplete_check  = 0;
    m_num_of_assert            = 0;
    m_num_of_push              = 0;
    m_num_of_pop               = 0;
    m_num_of_branch            = 0;
    m_num_of_prune             = 0;
    m_num_of_non_trivial_prune = 0;
    m_heuristic_time           = std::chrono::duration<double>::zero();
}

ostream & operator<<(ostream & out, stat const & stat) {
    out << "Number of Complete   Check  = " << stat.m_num_of_complete_check << endl;
    out << "Number of Incomplete Check  = " << stat.m_num_of_incomplete_check << endl;
    out << "Number of Assert            = " << stat.m_num_of_assert << endl;
    out << "Number of Push              = " << stat.m_num_of_push << endl;
    out << "Number of Pop               = " << stat.m_num_of_pop << endl;
    out << "Number of Branch            = " << stat.m_num_of_branch << endl;
    out << "Number of Non-trivial Prune = " << stat.m_num_of_non_trivial_prune
        << " (" << (100.0 * stat.m_num_of_non_trivial_prune / stat.m_num_of_prune)
        << "%)" << endl;
    out << "Number of Total Prune       = " << stat.m_num_of_prune << endl;
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end_time - stat.m_start_time;
    out << "Running time                = " << diff.count() << " s" << endl;
    out << "Heuristic Running time      = " << stat.m_heuristic_time.count() << " s" << endl;
    out << "Number of Heuristic Paths   = " << stat.m_num_heuristic_paths <<  endl;
    return out;
}
}  // namespace dreal
