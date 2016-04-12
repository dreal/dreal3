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

#pragma once
#include <initializer_list>
#include <iostream>
#include <memory>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "ibex/ibex.h"
#include "json/json.hpp"
#include "opensmt/egraph/Enode.h"
#include "util/hash_combine.h"

namespace dreal {

class box {
private:
    // m_vars.size() == m_ivec.size()
    // Invariant: m_vars[i] ~ m_ivec[i]
    std::shared_ptr<std::vector<Enode *>> m_vars;
    ibex::IntervalVector m_values;
    std::shared_ptr<std::unordered_map<std::string, int>> m_name_index_map;
    int m_idx_last_branched;

    // Methods
    std::tuple<int, box, box> bisect_int_at(int i) const;
    std::tuple<int, box, box> bisect_real_at(int i) const;
    void constructFromVariables(std::vector<Enode *> const & vars);

public:
    explicit box(std::vector<Enode *> const & vars);
    box(box const & b, std::unordered_set<Enode *> const & extra_vars);
    void constructFromLiterals(std::vector<Enode *> const & lit_vec);

    std::tuple<int, box, box> bisect(double precision) const;
    std::vector<int> bisectable_dims(double precision) const;
    std::tuple<int, box, box> bisect_at(int i) const;
    std::vector<bool> diff_dims(box const & b) const;
    box sample_point() const;
    std::set<box> sample_points(unsigned const n) const;
    double get_bisection_ratio(int i) const;
    inline bool is_time_variable(int i) const { return get_name(i).find("time_") == 0; }
    inline bool is_bisectable() const { return m_values.is_bisectable(); }
    inline bool is_empty() const { return size() == 0 || m_values.is_empty(); }
    inline ibex::IntervalVector & get_values() { return m_values; }
    inline ibex::IntervalVector const & get_values() const { return m_values; }
    ibex::IntervalVector get_domains() const;
    inline std::vector<Enode *> const & get_vars() const { return *m_vars; }
    inline unsigned size() const { return m_vars ? (m_vars->size()) : 0; }
    inline void set_empty() { m_values.set_empty(); }
    inline unsigned get_index(Enode * e) const {
        return get_index(e->getCar()->getNameFull());
    }
    inline unsigned get_index(std::string const & s) const {
        auto const it = m_name_index_map->find(s);
        if (it != m_name_index_map->end()) {
            return it->second;
        } else {
            throw std::logic_error("box::get_index(" + s + "): doesn not have the key " + s);
        }
    }

    // get_value
    inline ibex::Interval & get_value(int i) { return m_values[i]; }
    inline ibex::Interval const & get_value(int i) const { return m_values[i]; }
    inline ibex::Interval & get_value(std::string const & s) { return m_values[get_index(s)]; }
    inline ibex::Interval const & get_value(std::string const & s) const {
        return m_values[get_index(s)];
    }
    inline const ibex::Interval& get_value(Enode * const e) const {
        return get_value(e->getCar()->getNameFull());
    }
    inline ibex::Interval& get_value(Enode * const e) {
        return get_value(e->getCar()->getNameFull());
    }

    // set_value
    inline void set_value (Enode * e, double lb, double ub) {
        m_values[get_index(e)] = ibex::Interval(lb,ub);
    }

    // get_domain
    ibex::Interval get_domain(int i) const;
    inline ibex::Interval get_domain(std::string const & s) const {
        return get_domain(get_index(s));
    }
    inline ibex::Interval get_domain(Enode * const e) const {
        return get_domain(e->getCar()->getNameFull());
    }

    int get_idx_last_branched() const { return m_idx_last_branched; }

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

    inline std::string get_name(unsigned i) const {
        return (*m_vars)[i]->getCar()->getNameFull();
    }

    double max_diam() const;
    inline double volume() const { return m_values.volume(); }

    friend std::ostream& display_diff(std::ostream& out, box const & b1, box const & b2);
    friend std::ostream& display(std::ostream& out, box const & b, bool const exact, bool const old_style);
    inline std::size_t hash() const {
        std::size_t seed = 23;
        for (int i = 0; i < m_values.size(); i++) {
            hash_combine<double>(seed, m_values[i].lb());
            hash_combine<double>(seed, m_values[i].ub());
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
    nlohmann::json to_JSON() const;

    void assign_to_enode() const;
};

bool operator<(ibex::Interval const & a, ibex::Interval const & b);
bool operator>(ibex::Interval const & a, ibex::Interval const & b);
bool operator<=(ibex::Interval const & a, ibex::Interval const & b);
bool operator>=(ibex::Interval const & a, ibex::Interval const & b);

box intersect(box b1, box const & b2);
box intersect(std::vector<box> const & vec);
box hull(box b1, box const & b2);
box hull(std::vector<box> const & vec);

std::ostream& display_diff(std::ostream& out, box const & b1, box const & b2);
std::ostream& display(std::ostream& out, box const & b, bool const exact = false, bool const old_style = false);
std::ostream& operator<<(std::ostream& out, box const & b);
}  // namespace dreal

namespace std {
template <>
struct hash<dreal::box> {
    std::size_t operator()(dreal::box const & c) const { return c.hash(); }
};
}  // namespace std
