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
#include <vector>

namespace dreal {

class point {
private:
    std::vector<double> m_values;

public:
    point() : m_values() { }
    explicit point(std::vector<double> const & values) : m_values(values) { }

    friend std::ostream& operator<<(std::ostream& out, point const & b);
    inline bool operator<(point const & other) const {
        return m_values < other.m_values;
    }
    inline bool operator==(point const & other) const {
        return m_values == other.m_values;
    }
};

std::ostream& operator<<(std::ostream& out, point const & b);
}  // namespace dreal
