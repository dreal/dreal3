/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/logging.h"

using std::copy;
using std::endl;
using std::initializer_list;
using std::ostream;
using std::pair;
using std::sort;
using std::string;
using std::unordered_set;
using std::vector;

namespace dreal {
box::box(std::vector<Enode *> const & vars)
    : m_vars(vars), m_values(m_vars.size()), m_domains(m_vars.size()) {
    constructFromVariables(m_vars);
}

box::box(std::vector<Enode *> const & vars, ibex::IntervalVector values)
    : m_vars(vars), m_values(values), m_domains(values) { }


void box::constructFromVariables(vector<Enode *> const & vars) {
    DREAL_LOG_DEBUG << "box::constructFromVariables";
    m_vars = vars;
    // Construct ibex::IntervalVector
    m_values.resize(m_vars.size());
    m_domains.resize(m_vars.size());
    unsigned num_var = m_vars.size();
    for (unsigned i = 0; i < num_var; i++) {
        Enode const * const e = m_vars[i];
        double const lb = e->getLowerBound();
        double const ub = e->getUpperBound();
        m_values[i] = ibex::Interval(lb, ub);
        m_domains[i] = ibex::Interval(lb, ub);
        m_name_index_map.emplace(e->getCar()->getName(), i);
    }
    return;
}

void box::constructFromLiterals(vector<Enode *> const & lit_vec) {
    DREAL_LOG_DEBUG << "box::constructFromLiterals";
    // Construct a list of variables
    unordered_set<Enode *> var_set;
    for (auto const & lit : lit_vec) {
        unordered_set<Enode *> const & temp_vars = lit->get_vars();
        var_set.insert(temp_vars.begin(), temp_vars.end());
    }
    std::copy(var_set.begin(), var_set.end(), std::back_inserter(m_vars));
    std::sort(m_vars.begin(), m_vars.end(),
              [](Enode const * e1, Enode const * e2) {
                  return e1->getCar()->getName() < e2->getCar()->getName();
              });
    constructFromVariables(m_vars);
    return;
}

ostream& operator<<(ostream& out, box const & b) {
    unsigned const s = b.size();
    for (unsigned i = 0; i < s; i++) {
        Enode * e = b.m_vars[i];
        ibex::Interval const & v = b.m_values[i];
        ibex::Interval const & d = b.m_domains[i];
        out << e->getCar()->getName()
            << " : " << d << " = " << v << endl;
    }
    return out;
}

pair<box, box> box::split() const {
    // TODO(soonhok): implement other split policy

    // static int i = -1;
    // i++;
    // i = i % size();
    // return split(i);

    return split(m_values.extr_diam_index(false));
}

// Split a box into two boxes by bisecting i-th interval.
pair<box, box> box::split(int i) const {
    DREAL_LOG_INFO << "box::split(" << i << ")";
    assert(0 <= i && i < m_values.size());
    box b1(*this);
    box b2(*this);
    ibex::Interval iv = b1.m_values[i];
    pair<ibex::Interval, ibex::Interval> new_intervals = iv.bisect();
    b1.m_values[i] = new_intervals.first;
    b2.m_values[i] = new_intervals.second;
    return make_pair(b1, b2);
}
}  // namespace dreal
