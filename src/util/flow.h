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

#pragma once
#include <string>
#include <iostream>
#include <initializer_list>
#include <unordered_map>
#include <vector>
#include <utility>
#include "opensmt/egraph/Enode.h"
#include "ibex/ibex.h"

namespace dreal {
class flow {
private:
    std::vector<Enode *> m_vars;
    std::vector<Enode *> m_odes;

public:
    flow();
    flow(Enode * const v, Enode * const e);
    void add(Enode * const v, Enode * const e);
    inline std::vector<Enode *> const & get_vars() const { return m_vars; }
    inline std::vector<Enode *>         get_vars()       { return m_vars; }
    inline std::vector<Enode *> const & get_odes() const { return m_odes; }
    inline std::vector<Enode *>         get_odes()       { return m_odes; }
    friend std::ostream & operator<<(std::ostream & out, flow const & _flow);
};
std::ostream & operator<<(std::ostream & out, flow const & _flow);
}  // namespace dreal
