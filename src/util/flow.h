/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"

class Enode;

namespace dreal {
class flow {
public:
    flow() = default;
    flow(Enode * const v, Enode * const e);
    void add(Enode * const v, Enode * const e);
    std::vector<Enode *> const & get_vars() const { return m_vars; }
    std::vector<Enode *> get_vars() { return m_vars; }
    std::vector<Enode *> const & get_odes() const { return m_odes; }
    std::vector<Enode *> get_odes() { return m_odes; }
    friend std::ostream & operator<<(std::ostream & out, flow const & _flow);

private:
    std::vector<Enode *> m_vars;
    std::vector<Enode *> m_odes;
};
std::ostream & operator<<(std::ostream & out, flow const & _flow);
}  // namespace dreal
