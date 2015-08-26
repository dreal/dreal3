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

#pragma once
#include <iostream>
#include <initializer_list>
#include <unordered_map>
#include <unordered_set>
#include <set>
#include <vector>
#include <utility>
#include <string>
#include <tuple>
#include "opensmt/egraph/Enode.h"
#include "ibex/ibex.h"

namespace dreal {

class box {
private:
    // m_vars.size() == m_ivec.size()
    // Invariant: m_vars[i] ~ m_ivec[i]
    std::vector<Enode *> m_vars;
    ibex::IntervalVector m_values;
    ibex::IntervalVector m_bounds;
    ibex::IntervalVector m_domains;
    std::vector<double>  m_precisions;
    std::unordered_map<std::string, int> m_name_index_map;
    std::tuple<int, box, box> bisect_int_at(int i) const;
    std::tuple<int, box, box> bisect_real_at(int i) const;
    std::tuple<int, box, box> bisect_at(int i) const;
    void constructFromVariables(std::vector<Enode *> const & vars);

public:
    explicit box(std::vector<Enode *> const & vars);
    box(box const & b, std::unordered_set<Enode *> const & extra_vars);
    box(std::vector<Enode *> const & vars, ibex::IntervalVector ivec);
    void constructFromLiterals(std::vector<Enode *> const & lit_vec);

    std::tuple<int, box, box> bisect(double precision) const;
    vector<bool> diff_dims(box const & b) const;
    std::set<box> sample_points(unsigned const n) const;
    inline bool is_bisectable() const { return m_values.is_bisectable(); }
    inline bool is_empty() const { return size() == 0 || m_values.is_empty(); }
    inline ibex::IntervalVector & get_values() { return m_values; }
    inline ibex::IntervalVector const & get_values() const { return m_values; }
    inline ibex::IntervalVector const & get_domains() const { return m_domains; }
    inline ibex::IntervalVector const & get_bounds() const { return m_bounds; }
    inline std::vector<Enode *> const & get_vars() const { return m_vars; }
    inline unsigned size() const { return m_values.size(); }
    inline void set_empty() { m_values.set_empty(); }
    inline void set_bounds(ibex::IntervalVector const & iv) { m_bounds = iv; }
    inline unsigned get_index(Enode * e) const {
        return get_index(e->getCar()->getName());
    }
    inline unsigned get_index(string const & s) const {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return it->second;
        } else {
            throw std::logic_error("box::get_index(" + s + "): doesn not have the key " + s);
        }
    }
    inline box & shrink_bounds() {
        m_bounds = m_values;
        return *this;
    }

    // get_value
    inline ibex::Interval & get_value(int i) { return m_values[i]; }
    inline ibex::Interval const & get_value(int i) const { return m_values[i]; }
    inline ibex::Interval & get_value(string const & s) {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_values[it->second];
        } else {
            throw std::logic_error("get_value : Box does not have a key " + s);
        }
    }
    inline ibex::Interval const & get_value(string const & s) const {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_values[it->second];
        } else {
            throw std::logic_error("get_value : Box does not have a key " + s);
        }
    }
    inline const ibex::Interval& get_value(Enode * const e) const {
        return get_value(e->getCar()->getName());
    }
    inline ibex::Interval& get_value(Enode * const e) {
        return get_value(e->getCar()->getName());
    }

    // get_bound
    inline ibex::Interval & get_bound(int i) { return m_bounds[i]; }
    inline ibex::Interval const & get_bound(int i) const { return m_bounds[i]; }
    inline ibex::Interval & get_bound(string const & s) {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_bounds[it->second];
        } else {
            throw std::logic_error("get_bound : Box does not have a key " + s);
        }
    }
    inline ibex::Interval const & get_bound(string const & s) const {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_bounds[it->second];
        } else {
            throw std::logic_error("get_bound : Box does not have a key " + s);
        }
    }
    inline const ibex::Interval& get_bound(Enode * const e) const {
        return get_bound(e->getCar()->getName());
    }
    inline ibex::Interval& get_bound(Enode * const e) {
        return get_bound(e->getCar()->getName());
    }

    // get_domain
    inline ibex::Interval & get_domain(int i) { return m_domains[i]; }
    inline ibex::Interval const & get_domain(int i) const { return m_domains[i]; }
    inline ibex::Interval & get_domain(string const & s) {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_domains[it->second];
        } else {
            throw std::logic_error("get_domain : Box does not have a key " + s);
        }
    }
    inline ibex::Interval const & get_domain(string const & s) const {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_domains[it->second];
        } else {
            throw std::logic_error("get_domain : Box does not have a key " + s);
        }
    }
    inline const ibex::Interval& get_domain(Enode * const e) const {
        return get_domain(e->getCar()->getName());
    }
    inline ibex::Interval& get_domain(Enode * const e) {
        return get_domain(e->getCar()->getName());
    }

    // get_precision
    inline double get_precision(int i) const { return m_precisions[i]; }
    inline double get_precision(string const & s) const {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_precisions[it->second];
        } else {
            throw std::logic_error("get_precision : Box does not have a key " + s);
        }
    }
    inline double get_precision(Enode * const e) {
        return get_precision(e->getCar()->getName());
    }

    // operator[]
    inline const ibex::Interval& operator[](int i) const { return get_value(i); }
    inline ibex::Interval& operator[](int i) { return get_value(i); }
    inline const ibex::Interval& operator[](std::string const & s) const { return get_value(s); }
    inline ibex::Interval& operator[](std::string const & s) { return get_value(s); }
    inline const ibex::Interval& operator[](Enode * const e) const { return get_value(e); }
    inline ibex::Interval& operator[](Enode * const e) { return get_value(e); }

    inline bool is_subset(box const & b) const {
        return m_values.is_subset(b.m_values);
    }
    inline bool is_superset(box const & b) const {
        return m_values.is_superset(b.m_values);
    }

    bool operator==(box const & b) const;
    bool operator<(box const & b) const;
    bool operator<=(box const & b) const;
    bool operator>(box const & b) const;
    bool operator>=(box const & b) const;
    inline bool operator!=(box const & b) const { return !(*this == b); }

    inline string get_name(unsigned i) const {
        return m_vars[i]->getCar()->getName();
    }

    double max_diam() const;
    inline double volume() const { return m_values.volume(); }

    friend ostream& display_diff(ostream& out, box const & b1, box const & b2);
    friend ostream& display(ostream& out, box const & b, bool const exact, bool const old_style);
    inline std::size_t hash() const {
        std::size_t seed = 0;
        for (int i = 0; i < m_values.size(); i++) {
            seed ^= (size_t)(m_values[i].lb()) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            seed ^= (size_t)(m_values[i].ub()) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
    void intersect(box const & b);
    void intersect(std::vector<box> const & vec);
    void hull(box const & b);
    void hull(std::vector<box> const & vec);
    friend box intersect(box b1, box const & b2);
    friend box hull(std::vector<box> const & s);
    friend box hull(box b1, box const & b2);

    void assign_to_enode() const;
    void adjust_bound(vector<box> const & box_stack);
};

bool operator<(ibex::Interval const & a, ibex::Interval const & b);
bool operator>(ibex::Interval const & a, ibex::Interval const & b);
bool operator<=(ibex::Interval const & a, ibex::Interval const & b);
bool operator>=(ibex::Interval const & a, ibex::Interval const & b);

box intersect(box b1, box const & b2);
box intersect(std::vector<box> const & vec);
box hull(box b1, box const & b2);
box hull(std::vector<box> const & vec);

ostream& display_diff(ostream& out, box const & b1, box const & b2);
ostream& display(ostream& out, box const & b, bool const exact = false, bool const old_style = false);
std::ostream& operator<<(ostream& out, box const & b);
}  // namespace dreal

namespace std {
template <>
struct hash<dreal::box> {
    std::size_t operator()(dreal::box const & c) const { return c.hash(); }
};
}  // namespace std
