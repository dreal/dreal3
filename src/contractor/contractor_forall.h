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

#include <algorithm>
#include <initializer_list>
#include <iosfwd>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "./dreal_config.h"
#include "contractor/contractor.h"
#include "contractor/contractor_cell.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"

class Egraph;
class Enode;
struct SMTConfig;

namespace dreal {
/// Contractor for handling forall constraint
class contractor_status;
class forall_constraint;

class contractor_forall : public contractor_cell {
public:
    contractor_forall(box const & b, std::shared_ptr<forall_constraint> const ctr);
    void prune(contractor_status & s);
    std::ostream & display(std::ostream & out) const;

private:
    std::shared_ptr<forall_constraint> const m_ctr;
    std::unordered_map<Enode *, Enode *> m_strengthen_map;

    box find_CE(box const & b, std::unordered_set<Enode *> const & forall_vars,
                std::vector<Enode *> const & vec, bool const p, SMTConfig & config, Egraph & eg);
    box find_CE_via_underapprox(box const & b, std::unordered_set<Enode *> const & forall_vars,
                                std::vector<Enode *> const & vec, bool const p, SMTConfig & config,
                                Egraph & eg);
    box find_CE_via_overapprox(box const & b, std::unordered_set<Enode *> const & forall_vars,
                               std::vector<Enode *> const & vec, bool const p, SMTConfig & config,
                               Egraph & eg);

    /// Given a list Enode, return a vector<Enode *>
    std::vector<Enode *> elist_to_vector(Enode * e) const;
    /// Pruning function. @p body can be and (conjunction), or
    /// (disjunction), not (negation), or a leaf (a constraint). For
    /// each type, it calls corresponding 'prune_' function.
    void prune_tree(contractor_status & cs, Enode * body, bool const p);
    /// Pruning function. It handles \/ {t_1, ..., t_n} where @p vec includes t_i
    void prune_disjunction(contractor_status & cs, std::vector<Enode *> const & vec, bool const p);
    /// Pruning function. It handles /\ {t_1, ..., t_n} where @p vec includes t_i
    void prune_conjunction(contractor_status & cs, std::vector<Enode *> const & vec, bool const p);
    /// Pruning function. It handles a leaf node (a constraint without Boolean structure)
    void prune_leaf(contractor_status & cs, Enode * body, bool const p);

    static ibex::BitSet extract_bitset(box const & b, std::shared_ptr<forall_constraint> const ctr);
};
}  // namespace dreal
