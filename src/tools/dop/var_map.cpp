/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

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

#include <string>
#include <exception>
#include "tools/dop/var_map.h"

namespace dop {

using std::string;
using std::runtime_error;

double var_map::pop_num() {
    double const v = m_double_vec.back();
    m_double_vec.pop_back();
    return v;
}

void var_map::push_num(double const n) { m_double_vec.push_back(n); }

void var_map::push_id(string const & name) { m_str = name; }

void var_map::push_var_decl() {
    Snode * const sort = m_ctx.mkSortReal();
    m_ctx.DeclareFun(m_str.c_str(), sort);
    Enode * const e = m_ctx.mkVar(m_str.c_str(), true);
    double const lb = m_double_vec[0];
    double const ub = m_double_vec[1];
    m_double_vec.clear();
    e->setDomainLowerBound(lb);
    e->setDomainUpperBound(ub);
    e->setValueLowerBound(lb);
    e->setValueUpperBound(ub);
    m_map.emplace(m_str, e);
}

Enode * var_map::find(string const & name) const {
    auto it = m_map.find(name);
    if (it != m_map.end()) {
        return it->second;
    }
    throw runtime_error("variable " + name + " is not found in the definition.");
}

}  // namespace dop
