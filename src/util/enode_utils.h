/*********************************************************************
Author: Soonho Kong

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

#include "api/OpenSMTContext.h"
#include "opensmt/api/OpenSMTContext.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"

class Egraph;
class Enode;
class OpenSMTContext;

namespace dreal {

/// strengthening a constraint (Enode) by eps (positive constant)
Enode * strengthen_enode(Egraph & eg, Enode * const e, double const eps, bool const polarity);
/// Add forall quantifier if Enode e includes universally quantified variables
Enode * wrap_enode_including_forall_vars(OpenSMTContext * ctx, Enode * const e);
/// Susbtitute e with a map (Enode -> Enode)
Enode * subst(OpenSMTContext & ctx, Enode * e, std::unordered_map<Enode *, Enode *> const & m);
}  // namespace dreal
