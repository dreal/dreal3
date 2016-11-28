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

#include <unordered_map>

#include "opensmt/egraph/Enode.h"
#include "util/box.h"

class Enode;

namespace dreal {
class box;

double eval_enode(Enode * const e, std::unordered_map<Enode *, double> const & var_map);
double eval_enode_term(Enode * const e, box const & b);
bool eval_enode_formula(Enode * const e, box const & b, bool const polarity);
double deriv_enode(Enode * const e, Enode * const v,
                   std::unordered_map<Enode *, double> const & var_map);
}  // namespace dreal
