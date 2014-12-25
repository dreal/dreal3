/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include "opensmt/egraph/Enode.h"
#include "util/interval.h"

namespace dreal {
enum class var_type { INT, REAL };
std::ostream & operator<<(std::ostream & out, var_type const & ty);

class var {
private:
    Enode * m_enode;
    interval m_domain;
    interval m_value;
    std::string m_name;
    var_type m_type;

public:
    var() : m_enode(nullptr), m_domain(), m_name("nullVar"), m_type(var_type::INT) {}
    var(Enode * e);

    inline bool operator==(var const & rhs) const { return m_enode == rhs.m_enode; }
    inline bool operator!=(var const & rhs) const { return !(*this == rhs); }
    Enode * getEnode() const {
        return m_enode;
    }
    inline std::string getName() const {
        return m_name;
    }
    void intersect(var const v);
    friend std::ostream & operator<<(std::ostream & out, var const & v);
};

std::ostream & operator<<(std::ostream & out, var const & v);
void swap(var & v1, var & v2);

}

namespace std {
template <>
struct hash<dreal::var> {
    std::size_t operator()(const dreal::var& k) const {
        return std::hash<Enode*>()(k.getEnode());
    }
};
}
