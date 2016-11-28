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

#include "util/stacker.h"

#include <assert.h>
#include <algorithm>
#include <cmath>
#include <limits>
#include <memory>
#include <vector>

#include "constraint/constraint.h"
#include "util/logging.h"

namespace dreal {

template <typename T>
class scoped_vec;

using std::vector;
using std::shared_ptr;
using std::numeric_limits;

stacker::stacker(vector<box> & boxes, scoped_vec<shared_ptr<constraint>> const & ctrs,
                 double const prec)
    : m_stack(boxes), m_ctrs(ctrs), m_prec(prec), m_sol(boxes[0]) {
    m_best_score = numeric_limits<double>::max();
}

bool stacker::playout() {
    // clear the score vector
    // run samples on each box, of numbers based on current scores
    // update the scores on each box and put them in the score set
    m_score_board.clear();
    for (unsigned i = 0; i < m_stack.size(); i++) {
        double score = numeric_limits<double>::max();
        for (unsigned j = 0; j < 5; j++) {
            box sample = m_stack[i].sample_point();
            // DREAL_LOG_INFO<<"testing sample: "<<sample;
            double total_err = 0;
            for (auto ctr : m_ctrs) {
                assert(ctr->get_type() == constraint_type::Nonlinear);
                double err = ctr->eval_error(sample);
                DREAL_LOG_INFO << "playout current err: " << err << " obtained on ctr " << *ctr;
                if (err >= m_prec) {
                    total_err += err;
                }
            }
            // DREAL_LOG_INFO<<"finished evaluation on box "<<m_stack[i];
            if (total_err <= m_prec) {  // solution found
                update_solution(sample);
                DREAL_LOG_INFO << "best score right now " << total_err << "\t";
                return true;
            } else if (score > total_err) {
                score = total_err;
            } else {
                DREAL_LOG_INFO << "skipped a useless sample -- current error " << total_err << ">"
                               << " best score on board " << score;
            }
        }
        assert(score > m_prec);
        score = m_stack[i].test_score(score);
        m_score_board.push_back(score);
    }
    return false;
}

void stacker::update_budgets() {
    // assuming score board has been sorted
    m_sample_budgets.clear();
    assert(m_stack.size() == m_score_board.size());  // pop operations shouldn't mess with this
    unsigned total = m_stack.size();                 // total num of boxes
    double range = m_score_board[total - 1] - m_score_board[0];
    unsigned total_budget = 5 * total;  // 10 votes from each box, to be reassigned;
    for (unsigned i = 0; i < total; i++) {
        m_sample_budgets.emplace(i, total_budget * ceil(range / m_score_board[i]));
    }
}

box stacker::pop_best() {
    sort(m_score_board.begin(), m_score_board.end());
    update_budgets();
    unsigned index_of_best = 0;
    for (unsigned i = 0; i < m_stack.size(); i++) {
        DREAL_LOG_INFO << "score board 0: " << m_score_board[0];
        DREAL_LOG_INFO << "current score of box " << i << ": " << m_stack[i].get_score();
        if (m_stack[i].get_score() <= m_score_board[0]) {
            index_of_best = i;
            break;
        }
    }
    box result = m_stack[index_of_best];
    m_stack.erase(m_stack.begin() + index_of_best);
    if (m_best_score > m_score_board[0]) {
        m_best_score = m_score_board[0];
    }
    DREAL_LOG_INFO << "m_best_score: " << m_score_board[0];
    return result;
}

void stacker::push(box const & b) { m_stack.push_back(b); }

}  // namespace dreal;
