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
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/hexfloat.h"
#include "util/logging.h"

using std::copy;
using std::endl;
using std::initializer_list;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::set;
using std::sort;
using std::string;
using std::unordered_set;
using std::vector;
using std::make_tuple;

namespace dreal {
box::box(std::vector<Enode *> const & vars)
    : m_vars(vars), m_values(m_vars.size() == 0 ? 1 : m_vars.size()),
      m_bounds(m_values.size()), m_domains(m_values.size()), m_precisions(m_values.size(), 0.0) {
    if (m_vars.size() > 0) {
        constructFromVariables(m_vars);
    }
}

box::box(std::vector<Enode *> const & vars, ibex::IntervalVector values)
    : m_vars(vars), m_values(values), m_bounds(values), m_domains(values), m_precisions(values.size(), 0.0) { }

void box::constructFromVariables(vector<Enode *> const & vars) {
    DREAL_LOG_DEBUG << "box::constructFromVariables";
    m_vars = vars;
    // Construct ibex::IntervalVector
    m_values.resize(m_vars.size());
    m_bounds.resize(m_vars.size());
    m_domains.resize(m_vars.size());
    m_precisions.resize(m_vars.size());
    unsigned num_var = m_vars.size();
    for (unsigned i = 0; i < num_var; i++) {
        Enode const * const e = m_vars[i];
        double const lb = e->getDomainLowerBound();
        double const ub = e->getDomainUpperBound();
        if (e->hasPrecision()) {
            m_precisions[i] = e->getPrecision();
        }
        m_values[i] = ibex::Interval(lb, ub);
        m_bounds[i] = ibex::Interval(lb, ub);
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
        unordered_set<Enode *> const & temp_vars = lit->get_exist_vars();
        var_set.insert(temp_vars.begin(), temp_vars.end());
    }
    m_vars.clear();
    std::copy(var_set.begin(), var_set.end(), std::back_inserter(m_vars));
    std::sort(m_vars.begin(), m_vars.end(),
              [](Enode const * e1, Enode const * e2) {
                  return e1->getCar()->getName() < e2->getCar()->getName();
              });
    constructFromVariables(m_vars);
    return;
}

box::box(box const & b, std::unordered_set<Enode *> const & extra_vars)
    : m_vars(b.m_vars), m_values(m_vars.size() + extra_vars.size()),
      m_bounds(m_values.size()), m_domains(m_values.size()), m_precisions(m_values.size(), 0.0) {
    copy(extra_vars.begin(), extra_vars.end(), back_inserter(m_vars));
    std::sort(m_vars.begin(), m_vars.end(),
              [](Enode const * e1, Enode const * e2) {
                  return e1->getCar()->getName() < e2->getCar()->getName();
              });
    if (m_vars.size() > 0) {
        constructFromVariables(m_vars);
        for (unsigned i = 0; i < b.m_vars.size(); i++) {
            m_values[get_index(b.m_vars[i])] = b.m_values[i];
        }
    }
}

ostream& display(ostream& out, ibex::Interval const & iv, bool const exact) {
    if (exact) {
        out << "[" << to_hexfloat(iv.lb()) << ","
            << to_hexfloat(iv.ub()) << "]";
    } else {
        out << iv;
    }
    return out;
}

ostream& display_diff(ostream& out, box const & b1, box const & b2) {
    if (b1 == b2) {
        return out;
    }
    std::streamsize ss = out.precision();
    out.precision(16);
    assert(b1.size() == b2.size());
    unsigned const s = b1.size();
    for (unsigned i = 0; i < s; i++) {
        Enode * e1 = b1.m_vars[i];
        assert(e1 == b2.m_vars[i]);
        ibex::Interval const & v1 = b1.m_values[i];
        ibex::Interval const & v2 = b2.m_values[i];
#ifdef DEBUG
        ibex::Interval const & d1 = b1.m_domains[i];
        ibex::Interval const & d2 = b2.m_domains[i];
        assert(d1 == d2);
#endif
        if (v1 != v2) {
            out << e1->getCar()->getName()
                << " : ";
            display(out, v1, false);
            out << " => ";
            display(out, v2, false);
        }
        out << endl;
    }
    out.precision(ss);
    return out;
}

ostream& display(ostream& out, box const & b, bool const exact, bool const old_style) {
    std::streamsize ss = out.precision();
    out.precision(16);
    if (old_style) {
        out << "delta-sat with the following box:" << endl;
        unsigned const s = b.size();
        for (unsigned i = 0; i < s; i++) {
            if (i != 0) {
                out << endl;
            }
            Enode * e = b.m_vars[i];
            string const & name = e->getCar()->getName();
            ibex::Interval const & v = b.m_values[i];
            out << "\t" << name << " : " << v;
            if (i != (s - 1)) {
                out << ";";
            }
        }
    } else {
        unsigned const s = b.size();
        for (unsigned i = 0; i < s; i++) {
            if (i != 0) {
                out << endl;
            }
            Enode * e = b.m_vars[i];
            ibex::Interval const & v = b.m_values[i];
            ibex::Interval const & d = b.m_domains[i];
            out << e->getCar()->getName()
                << " : ";
            display(out, d, exact);
            out << " = ";
            display(out, v, exact);
        }
    }
    out.precision(ss);
    return out;
}

ostream& operator<<(ostream& out, box const & b) {
    return display(out, b);
}

tuple<int, box, box> box::bisect(double precision) const {
    // TODO(soonhok): implement other bisect policy
    int index = -1;
    double max_diam = numeric_limits<double>::min();

    for (int i = 0; i < m_values.size(); i++) {
        double current_diam = m_values[i].diam();
        double ith_precision = m_precisions[i] == 0 ? precision : m_precisions[i];
        if (current_diam > max_diam && current_diam > ith_precision && m_values[i].is_bisectable()) {
            index = i;
            max_diam = current_diam;
        }
    }

    if (index == -1) {
        // Fail to find a dimension to bisect
        return make_tuple(-1, *this, *this);
    } else {
        return bisect_at(index);
    }
}


  //select bisection ratio for interval
double box::get_bisection_ratio(int i) const {
  if (is_time_variable(i) && m_values[i].contains(0.0)) {
    DREAL_LOG_DEBUG << "Splitting time variable";
    return 0.0001;
  } else {
    return 0.5;
  }
}
  
tuple<int, box, box> box::bisect_int_at(int i) const {
    assert(0 <= i && i < m_values.size());
    box b1(*this);
    box b2(*this);
    ibex::Interval iv = ibex::integer(b1.m_values[i]);
    double const lb = iv.lb();
    double const ub = iv.ub();
    double const mid = iv.mid();
    double const mid_floor = floor(mid);
    double const mid_ceil  = ceil(mid);
    pair<ibex::Interval, ibex::Interval> new_intervals = iv.bisect();
    b1.m_values[i] = ibex::Interval(lb, mid_floor);
    b2.m_values[i] = ibex::Interval(mid_ceil, ub);
    DREAL_LOG_DEBUG << "box::bisect on " << m_vars[i] << " : int = " << m_values[i]
                    << " into " << b1.m_values[i] << " and " << b2.m_values[i];
    return make_tuple(i, b1, b2);
}

// Bisect a box into two boxes by bisecting i-th interval.
tuple<int, box, box> box::bisect_real_at(int i) const {
    assert(0 <= i && i < m_values.size());
    box b1(*this);
    box b2(*this);
    ibex::Interval iv = b1.m_values[i];
    assert(iv.is_bisectable());
    pair<ibex::Interval, ibex::Interval> new_intervals = iv.bisect(get_bisection_ratio(i));
    b1.m_values[i] = new_intervals.first;
    b2.m_values[i] = new_intervals.second;
    DREAL_LOG_DEBUG << "box::bisect on " << m_vars[i] << " : real = " << m_values[i]
                    << " into " << b1.m_values[i] << " and " << b2.m_values[i];
    return make_tuple(i, b1, b2);
}

// Bisect a box into two boxes by bisecting i-th interval.
tuple<int, box, box> box::bisect_at(int i) const {
    Enode * const e = m_vars[i];
    if (e->hasSortInt()) {
        return bisect_int_at(i);
    } else if (e->hasSortReal()) {
        return bisect_real_at(i);
    } else {
        ostringstream os;
        os << "variable " << e << " has neither Int sort nor Real sort." << endl;
        throw runtime_error(os.str());
    }
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
        if (m_values[i] != b.m_values[i]) {
            return false;
        }
    }
    return true;
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

void box::assign_to_enode() const {
    for (unsigned i = 0; i < m_vars.size(); i++) {
        m_vars[i]->setValueLowerBound(m_values[i].lb());
        m_vars[i]->setValueUpperBound(m_values[i].ub());
        m_vars[i]->setBoundLowerBound(m_values[i].lb());
        m_vars[i]->setBoundUpperBound(m_values[i].ub());
    }
}

void box::intersect(box const & b) {
    m_values &= b.m_values;
}
void box::intersect(vector<box> const & vec) {
    assert(vec.size() > 0);
    for (box const & b : vec) {
        this->intersect(b);
    }
}
box intersect(box b1, box const & b2) {
    b1.intersect(b2);
    return b1;
}
box intersect(vector<box> const & vec) {
    assert(vec.size() > 0);
    box b = vec.front();
    b.intersect(vec);
    return b;
}

void box::hull(box const & b) {
    m_values |= b.m_values;
}
void box::hull(vector<box> const & vec) {
    assert(vec.size() > 0);
    for (box const & b : vec) {
        this->hull(b);
    }
}
box hull(box b1, box const & b2) {
    b1.hull(b2);
    return b1;
}
box hull(vector<box> const & vec) {
    assert(vec.size() > 0);
    box b = vec.front();
    b.hull(vec);
    return b;
}

void box::adjust_bound(vector<box> const & box_stack) {
    if (!is_empty() && box_stack.size() > 0) {
        box bound(*this);
        bound.hull(box_stack);
        set_bounds(bound.get_values());
    }
}
}  // namespace dreal
