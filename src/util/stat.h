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

#pragma once
#include <chrono>
#include <iostream>
namespace dreal {
class stat {
public:
    unsigned m_num_of_incomplete_check;
    unsigned m_num_of_complete_check;
    unsigned m_num_of_assert;
    unsigned m_num_of_push;
    unsigned m_num_of_pop;
    unsigned m_num_of_branch;
    unsigned m_num_of_prune;
    unsigned m_num_of_CE;
    unsigned m_num_of_non_trivial_prune;
    std::chrono::time_point<std::chrono::high_resolution_clock> m_start_time;
    std::chrono::duration<double> m_heuristic_time;
    unsigned m_num_heuristic_paths;
    stat();
    void reset();
    void increase_check(bool complete);
    void increase_assert();
    void increase_push();
    void increase_pop();
    void increase_branch();
    void increase_prune();
    void increase_CE();
    void increase_non_trivial_prune();
    void increase_heuristic_time(std::chrono::duration<double> span) { m_heuristic_time += span; }
    void increase_heuristic_paths() { m_num_heuristic_paths++; }

    friend std::ostream & operator<<(std::ostream & out, stat const & stat);
};

std::ostream & operator<<(std::ostream & out, stat const & stat);
}  // namespace dreal
