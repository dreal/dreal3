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
#include <chrono>
#include <limits>
#include <random>
#include <set>
#include <string>
#include <tuple>
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
using std::numeric_limits;
using std::ostream;
using std::pair;
using std::set;
using std::sort;
using std::string;
using std::unordered_set;
using std::vector;
using std::make_tuple;

namespace dreal {
box::box(std::vector<Enode *> const & vars)
    : m_vars(vars), m_values(m_vars.size() == 0 ? 1 : m_vars.size()), m_domains(m_values.size()) {
    if (m_vars.size() > 0) {
        constructFromVariables(m_vars);
    }
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
    std::streamsize ss = out.precision();
    out.precision(16);
    for (unsigned i = 0; i < s; i++) {
        Enode * e = b.m_vars[i];
        ibex::Interval const & v = b.m_values[i];
        ibex::Interval const & d = b.m_domains[i];
        out << e->getCar()->getName()
            << " : " << d << " = " << v << endl;
    }
    out.precision(ss);
    return out;
}

ostream& box::display_old_style_model(ostream& out) const {
    out << "SAT with the following box:" << endl;
    std::streamsize ss = out.precision();
    out.precision(16);
    unsigned const s = size();
    for (unsigned i = 0; i < s; i++) {
        Enode * e = m_vars[i];
        string const & name = e->getCar()->getName();
        ibex::Interval const & v = m_values[i];
        out << "\t" << name << " : " << v;
        if (i != (s - 1)) {
            out << ";";
        }
        out << endl;
    }
    out.precision(ss);
    return out;
}

tuple<int, box, box> box::bisect() const {
    // TODO(soonhok): implement other bisect policy
    int index = 0;
    double max_diam = numeric_limits<double>::min();

    for (int i = 0; i < m_values.size(); i++) {
        double current_diam = m_values[i].diam();
        if (current_diam > max_diam && m_values[i].is_bisectable()) {
            index = i;
            max_diam = current_diam;
        }
    }
    return bisect(index);
}

// Bisect a box into two boxes by bisecting i-th interval.
tuple<int, box, box> box::bisect(int i) const {
    assert(0 <= i && i < m_values.size());
    box b1(*this);
    box b2(*this);
    ibex::Interval iv = b1.m_values[i];
    assert(iv.is_bisectable());
    pair<ibex::Interval, ibex::Interval> new_intervals = iv.bisect();
    b1.m_values[i] = new_intervals.first;
    b2.m_values[i] = new_intervals.second;
    DREAL_LOG_INFO << "box::bisect on " << m_vars[i] << " = " << m_values[i]
                   << " into " << b1.m_values[i] << " and " << b2.m_values[i];
    return make_tuple(i, b1, b2);
}

double box::max_diam() const {
    double max_diam = numeric_limits<double>::min();
    for (int i = 0; i < m_values.size(); i++) {
        double current_diam = m_values[i].diam();
        if (current_diam > max_diam && m_values[i].is_bisectable()) {
            max_diam = current_diam;
        }
    }
    return max_diam;
}

vector<bool> box::diff_dims(box const & b) const {
    assert(size() == b.size());
    vector<bool> ret(size(), false);
    for (unsigned i = 0; i < b.size(); i++) {
        if (m_values[i] != b.m_values[i]) { ret[i] = true; }
    }
    return ret;
}

box sample_point(box b) {
    static thread_local std::mt19937_64 rg(std::chrono::system_clock::now().time_since_epoch().count());
    unsigned const n = b.size();
    ibex::IntervalVector & values = b.get_values();
    for (unsigned i = 0; i < n; i++) {
        ibex::Interval & iv = values[i];
        double const lb = iv.lb();
        double const ub = iv.ub();
        if (lb != ub) {
            std::uniform_real_distribution<double> m_dist(lb, ub);
            iv = ibex::Interval(m_dist(rg));
        }
    }
    return b;
}

set<box> box::sample_points(unsigned const n) const {
    set<box> points;
    for (unsigned i = 0; i < n; i++) {
        points.insert(sample_point(*this));
    }
    return points;
}

bool box::operator==(box const & b) const {
    assert(m_values.size() == b.m_values.size());
    for (int i = 0; i < m_values.size(); i++) {
        if (m_values[i] == b.m_values[i]) {
            return true;
        }
    }
    return false;
}

bool box::operator<(box const & b) const {
    assert(m_values.size() == b.m_values.size());
    for (int i = 0; i < m_values.size(); i++) {
        if (m_values[i] < b.m_values[i]) {
            return true;
        }
    }
    return false;
}

bool box::operator>(box const & b) const {
    assert(m_values.size() == b.m_values.size());
    for (int i = 0; i < m_values.size(); i++) {
        if (m_values[i] > b.m_values[i]) {
            return true;
        }
    }
    return false;
}

bool box::operator<=(box const & b) const {
    return *this == b || *this < b;
}

bool box::operator>=(box const & b) const {
    return *this == b || *this > b;
    return false;
}

bool operator<(ibex::Interval const & a, ibex::Interval const & b) {
    if (a.is_empty() || b.is_empty()) {
        return false;
    }
    return a.ub() < b.lb();
    return false;
}
bool operator>(ibex::Interval const & a, ibex::Interval const & b) {
    if (a.is_empty() || b.is_empty()) {
        return false;
    }
    return a.lb() > b.ub();
}
bool operator<=(ibex::Interval const & a, ibex::Interval const & b) {
    return a == b || a < b;
}
bool operator>=(ibex::Interval const & a, ibex::Interval const & b) {
    return a == b || a > b;
}
}  // namespace dreal
