/*********************************************************************
Author: Sicun Gao <sicung@mit.edu>

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

#include <memory>
#include <unordered_map>
#include <vector>

#include "constraint/constraint.h"
#include "util/box.h"
#include "util/scoped_vec.h"

namespace dreal {

class constraint;
template <typename T>
class scoped_vec;

class stacker {
public:
    stacker(std::vector<box> & boxes, scoped_vec<std::shared_ptr<constraint>> const & ctrs,
            double const prec);
    box pop_best();  // pop the best box
    void push(box const &);
    bool playout();  // return true if sat solution is found
    inline unsigned get_size() { return m_stack.size(); }
    inline void update_solution(box & b) { m_sol = b; }
    inline box & get_solution() { return m_sol; }
    inline double get_best_score() { return m_best_score; }

private:
    std::vector<box> & m_stack;
    scoped_vec<std::shared_ptr<constraint>> const & m_ctrs;
    std::vector<double> m_score_board;
    double m_prec;
    double m_best_score;
    box m_sol;
    std::unordered_map<unsigned, unsigned> m_sample_budgets;  // decides how many samples on box
    void update_budgets();
};

}  // namespace dreal
