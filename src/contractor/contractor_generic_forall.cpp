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

#include <algorithm>
#include <chrono>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "contractor/contractor.h"
#include "ibex/ibex.h"
#include "icp/icp.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "util/logging.h"
#include "util/proof.h"

using std::back_inserter;
using std::cerr;
using std::endl;
using std::function;
using std::initializer_list;
using std::make_shared;
using std::ostream;
using std::ostringstream;
using std::queue;
using std::set;
using std::unordered_set;
using std::vector;

namespace dreal {

static unordered_map<Enode*, double> make_random_subst_from_bound(box const & b, unordered_set<Enode *> const & vars) {
    static thread_local std::mt19937_64 rg(std::chrono::system_clock::now().time_since_epoch().count());
    unordered_map<Enode*, double> subst;
    for (Enode * const var : vars) {
        auto const & bound = b.get_bound(var);
        double const lb = bound.lb();
        double const ub = bound.ub();
        std::uniform_real_distribution<double> m_dist(lb, ub);
        double const v = m_dist(rg);
        subst.emplace(var, v);
    }
    return subst;
}

static unordered_map<Enode*, double> make_random_subst_from_value(box const & b, unordered_set<Enode *> const & vars) {
    static thread_local std::mt19937_64 rg(std::chrono::system_clock::now().time_since_epoch().count());
    unordered_map<Enode*, double> subst;
    for (Enode * const var : vars) {
        auto const & value = b[var];
        double const lb = value.lb();
        double const ub = value.ub();
        std::uniform_real_distribution<double> m_dist(lb, ub);
        double const v = m_dist(rg);
        subst.emplace(var, v);
    }
    return subst;
}

static ostream & operator<<(ostream & out, unordered_map<Enode *, double> const & subst) {
    for (auto const & p : subst) {
        out << p.first << " |-> " << p.second << endl;
    }
    return out;
}

contractor_generic_forall::contractor_generic_forall(box const & , generic_forall_constraint const * const ctr)
    : contractor_cell(contractor_kind::FORALL), m_ctr(ctr) {
}

box contractor_generic_forall::prune(box b, SMTConfig & config) const
{
    // TODO(soonhok): implement
    return b;
}

ostream & contractor_generic_forall::display(ostream & out) const {
    out << "contractor_generic_forall(" << *m_ctr << ")";
    return out;
}

contractor mk_contractor_generic_forall(box const & b, generic_forall_constraint const * const ctr) {
    return contractor(make_shared<contractor_generic_forall>(b, ctr));
}

}  // namespace dreal
