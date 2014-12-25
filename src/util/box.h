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
#include <iostream>
#include <initializer_list>
#include <unordered_map>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "util/interval.h"
#include "util/var.h"

namespace dreal {

class box {
private:
    std::vector<dreal::var> m_vec;
    std::unordered_map<std::string, std::vector<var>::size_type> m_name_map;

public:
    box();
    box(std::initializer_list<var> const & var_list);

    inline std::vector<dreal::var>::size_type size() const { return m_vec.size(); }
    void add(var const & v);
    void add(std::initializer_list<var> const & var_list);
    void intersect(box const & other);

    friend std::ostream& operator<<(ostream& out, box const & b);
};
std::ostream& operator<<(ostream& out, box const & b);
}
