/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, the dReal Team

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
#include <cmath>
#include <climits>
#include <iomanip>
#include <limits>
#include <memory>
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

using std::ceil;
using std::chrono::system_clock;
using std::copy;
using std::endl;
using std::floor;
using std::initializer_list;
using std::make_shared;
using std::make_tuple;
using std::mt19937_64;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::setprecision;
using std::pair;
using std::runtime_error;
using std::set;
using std::sort;
using std::streamsize;
using std::string;
using std::tuple;
using std::uniform_real_distribution;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {
box::box(vector<Enode *> const & vars)
    : m_vars(nullptr), m_values(vars.size() == 0 ? 1 : vars.size()), m_idx_last_branched(-1) {
    if (vars.size() > 0) {
        m_vars = make_shared<vector<Enode *>>(vars);
        m_name_index_map = make_shared<unordered_map<string, int>>();
        constructFromVariables(*m_vars);
    }
}

void box::constructFromVariables(vector<Enode *> const & vars) {
    DREAL_LOG_DEBUG << "box::constructFromVariables";
    // m_vars should be alreday allocated and filled.
    assert(m_vars);
    // m_name_index_map should be alreday allocated.
    assert(m_name_index_map);
    unsigned const num_var = m_vars->size();
    if (num_var > 0) {
        m_values.resize(num_var);
        // Fill m_values, and m_name_index_map
        for (unsigned i = 0; i < num_var; i++) {
            Enode const * const e = vars[i];
            double const lb = e->getDomainLowerBound();
            double const ub = e->getDomainUpperBound();
            m_values[i] = ibex::Interval(lb, ub);
            m_name_index_map->emplace(e->getCar()->getNameFull(), i);
        }
    }
}

struct enode_lex_cmp {
    bool operator() (Enode const * e1, Enode const * e2) {
        return e1->getCar()->getNameFull() < e2->getCar()->getNameFull();
    }
};

void box::constructFromLiterals(vector<Enode *> const & lit_vec) {
    DREAL_LOG_DEBUG << "box::constructFromLiterals";
    // Construct a list of variables
    set<Enode *, enode_lex_cmp> var_set;
    for (auto const & lit : lit_vec) {
        unordered_set<Enode *> const & temp_vars = lit->get_exist_vars();
        var_set.insert(temp_vars.begin(), temp_vars.end());
    }
    m_vars = make_shared<vector<Enode*>>(var_set.begin(), var_set.end());
    m_name_index_map = make_shared<unordered_map<string, int>>();
    constructFromVariables(*m_vars);
    return;
}

box::box(box const & b, unordered_set<Enode *> const & extra_vars)
    : m_vars(make_shared<vector<Enode* > >(*b.m_vars)),
      m_values(m_vars->size() + extra_vars.size()),
      m_name_index_map(make_shared<unordered_map<string, int>>()),
      m_idx_last_branched(-1) {
    m_vars->insert(m_vars->end(), extra_vars.begin(), extra_vars.end());
    if (m_vars->size() > 0) {
        sort(m_vars->begin(), m_vars->end(), enode_lex_cmp());
        constructFromVariables(*m_vars);
        for (unsigned i = 0; i < b.m_vars->size(); i++) {
            m_values[get_index((*b.m_vars)[i])] = b.m_values[i];
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

nlohmann::json box::to_JSON() const {
    nlohmann::json entry;
    for (unsigned i = 0; i < size(); ++i) {
        string const & name = get_name(i);
        auto const & iv = get_value(i);
        entry[name] = { iv.lb(), iv.ub() };
    }
    return entry;
}

ostream& display_diff(ostream& out, box const & b1, box const & b2) {
    if (b1 == b2) {
        return out;
    }
    streamsize ss = out.precision();
    out.precision(16);
    assert(b1.size() == b2.size());
    unsigned const s = b1.size();
    for (unsigned i = 0; i < s; i++) {
        Enode * e1 = (*b1.m_vars)[i];
        assert(e1 == (*b2.m_vars)[i]);
        ibex::Interval const & v1 = b1.m_values[i];
        ibex::Interval const & v2 = b2.m_values[i];
#ifdef DEBUG
        ibex::Interval const & d1 = b1.get_domain(i);
        ibex::Interval const & d2 = b2.get_domain(i);
        assert(d1 == d2);
#endif
        if (v1 != v2) {
            out << e1->getCar()->getNameFull()
                << " : ";
            display(out, v1, false);
            out << " => ";
            display(out, v2, false);
            out << endl;
        }
    }
    out.precision(ss);
    return out;
}

ostream& display(ostream& out, box const & b, bool const exact, bool const old_style) {
    streamsize ss = out.precision();
    out.precision(16);
    if (old_style) {
        out << "delta-sat with the following box:" << endl;
        unsigned const s = b.size();
        for (unsigned i = 0; i < s; i++) {
            if (i != 0) {
                out << endl;
            }
            Enode * e = (*b.m_vars)[i];
            string const & name = e->getCar()->getNameFull();
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
            Enode * e = (*b.m_vars)[i];
            ibex::Interval const & v = b.m_values[i];
            ibex::Interval const & d = b.get_domain(i);
            out << e->getCar()->getNameFull()
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

vector<int> box::bisectable_dims(double const precision, ibex::BitSet const & input) const {
    thread_local static vector<int> dims;
    dims.clear();
    for (int i = 0; i < m_values.size(); i++) {
        if (input.contain(i) && is_bisectable_at(i, precision)) {
            dims.push_back(i);
        }
    }
    return dims;
}

bool box::is_bisectable_at(int const idx, double const precision) const {
    assert(idx >= 0);
    assert(idx < m_values.size());
    assert(precision >= 0.0);
    Enode * const var = (*m_vars)[idx];
    ibex::Interval const & iv = m_values[idx];
    if (!iv.is_bisectable()) {
        if (!iv.is_unbounded() && !iv.is_degenerated() && iv.diam() > precision) {
            ostringstream ss;
            string const var_name = get_name(idx);
            ss << setprecision(20);
            ss << "Warning: The width of interval "
               << var_name << " = " << iv
               << " is larger than the required precision";
            if (precision > 0.0) {
                ss << setprecision(6);
                ss << " (" << precision << ")";
            }
            ss << " but is no longer bisectable in the platform-native floating-point representation";
            ss << " (" << (CHAR_BIT * sizeof(double)) << "-bit).";
            DREAL_LOG_WARNING << ss.str();
        }
        return false;
    }
    double const current_diam = iv.diam();
    double const ith_precision = var->hasPrecision() ? var->getPrecision() : precision;
    if (var->hasSortInt()) {
        //     [       iv        ]
        //         [         ]
        //   ceil(lb)    floor(ub)
        if (ceil(iv.lb()) == floor(iv.ub())) {
            return false;
        }
    }
    return current_diam > ith_precision;
}

bool box::is_bisectable(double const precision) const {
    assert(precision >= 0.0);
    for (int i = 0; i < m_values.size(); ++i) {
        if (is_bisectable_at(i, precision)) {
            return true;
        }
    }
    return false;
}

tuple<int, box, box> box::bisect(double const precision) const {
    // TODO(soonhok): implement other bisect policy
    int index = -1;
    double max_diam = 0.0;
    for (int i = 0; i < m_values.size(); i++) {
        double const current_diam = m_values[i].diam();
        if (is_bisectable_at(i, precision) && current_diam > max_diam) {
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

  // select bisection ratio for interval
double box::get_bisection_ratio(int const i) const {
  if (is_time_variable(i) && m_values[i].contains(0.0)) {
    // DREAL_LOG_DEBUG << "Splitting time variable";
    // cout << "Splitting time variable" << i;
    return 0.00001;
  } else {
    return 0.5;
  }
}

tuple<int, box, box> box::bisect_int_at(int const i) const {
    assert(0 <= i && i < m_values.size());
    assert(!m_values[i].is_empty());
    assert(m_values[i].is_bisectable());
    box b1(*this);
    box b2(*this);
    ibex::Interval const iv = ibex::integer(b1.m_values[i]);
    double const lb = iv.lb();
    double const ub = iv.ub();
    double const mid = iv.mid();
    double const mid_floor = floor(mid);
    double const mid_ceil  = ceil(mid);
    if (!iv.is_bisectable()) {
        DREAL_LOG_FATAL << "NOT BISECTABLE = " << iv;
    }
    pair<ibex::Interval, ibex::Interval> new_intervals = iv.bisect();
    b1.m_values[i] = ibex::Interval(lb, mid_floor);
    b2.m_values[i] = ibex::Interval(mid_ceil, ub);
    b1.m_idx_last_branched = i;
    b2.m_idx_last_branched = i;
    DREAL_LOG_DEBUG << "box::bisect on " << (*m_vars)[i] << " : int = " << m_values[i]
                    << " into " << b1.m_values[i] << " and " << b2.m_values[i];
    return make_tuple(i, b1, b2);
}

// Bisect a box into two boxes by bisecting i-th interval.
tuple<int, box, box> box::bisect_real_at(int const i) const {
    assert(0 <= i && i < m_values.size());
    box b1(*this);
    box b2(*this);
    ibex::Interval iv = b1.m_values[i];
    assert(iv.is_bisectable());
    pair<ibex::Interval, ibex::Interval> new_intervals = iv.bisect(get_bisection_ratio(i));
    b1.m_values[i] = new_intervals.first;
    b2.m_values[i] = new_intervals.second;
    b1.m_idx_last_branched = i;
    b2.m_idx_last_branched = i;
    DREAL_LOG_DEBUG << "box::bisect on " << (*m_vars)[i] << " : real = " << m_values[i]
                    << " into " << b1.m_values[i] << " and " << b2.m_values[i];
    return make_tuple(i, b1, b2);
}

// Bisect a box into two boxes by bisecting i-th interval.
tuple<int, box, box> box::bisect_at(int const i) const {
    Enode * const e = (*m_vars)[i];
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

box box::sample_point() const {
    static mt19937_64 rg(system_clock::now().time_since_epoch().count());
    unsigned const n = size();
    box b(*this);
    ibex::IntervalVector const & values = get_values();
    for (unsigned i = 0; i < n; i++) {
        ibex::Interval const & iv = values[i];
        double const lb = iv.lb();
        double const ub = iv.ub();
        if (lb != ub) {
            uniform_real_distribution<double> m_dist(lb, ub);
            b[i] = ibex::Interval(m_dist(rg));
        }
    }
    return b;
}

set<box> box::sample_points(unsigned const n) const {
    set<box> points;
    for (unsigned i = 0; i < n; i++) {
        points.insert(sample_point());
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
    if (m_vars) {
        for (unsigned i = 0; i < m_vars->size(); i++) {
            (*m_vars)[i]->setValueLowerBound(m_values[i].lb());
            (*m_vars)[i]->setValueUpperBound(m_values[i].ub());
        }
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

ibex::Interval box::get_domain(int const i) const {
    Enode const * const e = (*m_vars)[i];
    double const lb = e->getDomainLowerBound();
    double const ub = e->getDomainUpperBound();
    return ibex::Interval(lb, ub);
}

ibex::IntervalVector box::get_domains() const {
    ibex::IntervalVector dom(m_vars->size());
    for (unsigned i = 0; i < m_vars->size(); i++) {
        Enode const * const e = (*m_vars)[i];
        double const lb = e->getDomainLowerBound();
        double const ub = e->getDomainUpperBound();
        dom[i] = ibex::Interval(lb, ub);
    }
    return dom;
}
}  // namespace dreal
