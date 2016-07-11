/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, the dReal Team

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
#include "contractor/contractor.h"

namespace dreal {
class contractor_generic_forall : public contractor_cell {
private:
    std::shared_ptr<generic_forall_constraint> const m_ctr;
    box find_CE(box const & b, std::unordered_set<Enode*> const & forall_vars, std::vector<Enode*> const & vec, bool const p, SMTConfig & config) const;
    void handle(contractor_status & cs, Enode * body, bool const p);
    std::vector<Enode *> elist_to_vector(Enode * e) const;
    void handle_disjunction(contractor_status & cs, std::vector<Enode *> const & vec, bool const p);
    void handle_conjunction(contractor_status & cs, std::vector<Enode *> const & vec, bool const p);
    void handle_atomic(contractor_status & cs, Enode * body, bool const p);

public:
    contractor_generic_forall(box const & b, std::shared_ptr<generic_forall_constraint> const ctr);
    void prune(contractor_status & s);
    std::ostream & display(std::ostream & out) const;
};
contractor mk_contractor_generic_forall(box const & box, std::shared_ptr<generic_forall_constraint> const ctr);
}  // namespace dreal
