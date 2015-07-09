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

#include <algorithm>
#include <initializer_list>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include "./config.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"

namespace dreal {
class contractor_generic_forall : public contractor_cell {
private:
    generic_forall_constraint const * const m_ctr;
    box handle(box b, std::unordered_set<Enode *> const & forall_vars, Enode * body, bool const p, SMTConfig & config) const;
    std::vector<Enode *> elist_to_vector(Enode * e) const;
    box handle_disjunction(box b, std::unordered_set<Enode *> const & forall_vars, std::vector<Enode *> const & vec, bool const p, SMTConfig & config) const;
    box handle_conjunction(box b, std::unordered_set<Enode *> const & forall_vars, std::vector<Enode *> const & vec, bool const p, SMTConfig & config) const;
    box handle_atomic(box b, std::unordered_set<Enode *> const & forall_vars, Enode * body, bool const p, SMTConfig & config) const;

public:
    contractor_generic_forall(box const & b, generic_forall_constraint const * const ctr);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};
contractor mk_contractor_generic_forall(box const & box, generic_forall_constraint const * const ctr);
}  // namespace dreal
