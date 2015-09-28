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
#include <map>
#include <string>
#include <unordered_map>
#include "ibex/ibex.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"

namespace dreal {
ibex::ExprNode const * translate_enode_to_exprnode(std::map<std::string, ibex::Variable const> & var_map, Enode * const e, std::unordered_map<Enode*, ibex::Interval> const & subst = std::unordered_map<Enode*, ibex::Interval>());
ibex::ExprCtr  const * translate_enode_to_exprctr(std::map<std::string, ibex::Variable const> & var_map, Enode * const e, lbool p = l_Undef, std::unordered_map<Enode*, ibex::Interval> const & subst = std::unordered_map<Enode*, ibex::Interval>());
std::map<std::string, ibex::Variable const> build_var_map(std::unordered_set<Enode *> const & vars);
}
