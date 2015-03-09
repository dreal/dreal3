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
    ibex::IntervalVector m_domains;
    std::unordered_map<std::string, int> m_name_index_map;

    void constructFromVariables(std::vector<Enode *> const & vars);

public:
    explicit box(std::vector<Enode *> const & vars);
    box(std::vector<Enode *> const & vars, ibex::IntervalVector ivec);
    void constructFromLiterals(std::vector<Enode *> const & lit_vec);

    std::tuple<int, box, box> bisect() const;
    std::tuple<int, box, box> bisect(int i) const;
    vector<bool> diff_dims(box const & b) const;
    std::set<box> sample_points(unsigned const n) const;
    inline bool is_bisectable() const { return m_values.is_bisectable(); }
    inline bool is_empty() { return size() == 0 || m_values.is_empty(); }
    inline ibex::IntervalVector & get_values() { return m_values; }
    inline ibex::IntervalVector const & get_values() const { return m_values; }
    inline ibex::IntervalVector const & get_domains() const { return m_domains; }
    inline std::vector<Enode *> const & get_vars() const { return m_vars; }
    inline unsigned size() const { return m_values.size(); }
    inline void set_empty() { m_values.set_empty(); }
    inline unsigned get_index(string const & s) const {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return it->second;
        } else {
            throw std::logic_error("box::get_index(" + s + "): doesn not have the key " + s);
        }
    }
    inline const ibex::Interval& operator[](int i) const {
        assert(i >= 0 && i < static_cast<int>(size()));
        return m_values[i];
    }
    inline ibex::Interval& operator[](int i) {
        assert(i >= 0 && i < static_cast<int>(size()));
        return m_values[i];
    }
    inline const ibex::Interval& operator[](std::string const & s) const {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_values[it->second];
        } else {
            throw std::logic_error("Box[] (const): Box does not have a key " + s);
        }
    }
    inline ibex::Interval& operator[](std::string const & s) {
        auto const it = m_name_index_map.find(s);
        if (m_name_index_map.find(s) != m_name_index_map.end()) {
            return m_values[it->second];
        } else {
            throw std::logic_error("Box[] : Box does not have a key " + s);
        }
    }
    inline const ibex::Interval& operator[](Enode * const e) const {
        return operator[](e->getCar()->getName());
    }

    inline ibex::Interval& operator[](Enode * const e) {
        return operator[](e->getCar()->getName());
    }

    bool operator==(box const & b) const;
    bool operator<(box const & b) const;
    bool operator<=(box const & b) const;
    bool operator>(box const & b) const;
    bool operator>=(box const & b) const;

    inline string get_name(unsigned i) const {
        return m_vars[i]->getCar()->getName();
    }

    double max_diam() const;
    inline double volume() const { return m_values.volume(); }

    friend std::ostream& operator<<(ostream& out, box const & b);
    std::ostream& display_old_style_model(ostream& out) const;
    inline std::size_t hash() const {
        // TODO(soonhok): possibly cache the hash value?
        std::size_t seed = 0;
        for (int i = 0; i < m_values.size(); i++) {
            seed ^= (size_t)(m_values[i].lb()) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            seed ^= (size_t)(m_values[i].ub()) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }

    void assign_to_enode() const;
};

bool operator<(ibex::Interval const & a, ibex::Interval const & b);
bool operator>(ibex::Interval const & a, ibex::Interval const & b);
bool operator<=(ibex::Interval const & a, ibex::Interval const & b);
bool operator>=(ibex::Interval const & a, ibex::Interval const & b);

std::ostream& operator<<(ostream& out, box const & b);
}  // namespace dreal

namespace std {
template <>
struct hash<dreal::box> {
    std::size_t operator()(dreal::box const & c) const { return c.hash(); }
};
}  // namespace std
