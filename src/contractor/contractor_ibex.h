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
#include <unordered_map>
#include <vector>
#include <initializer_list>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"

namespace dreal {

class contractor_ibex_fwdbwd : public contractor_cell {
private:
    nonlinear_constraint const * m_ctr;
    ibex::NumConstraint const * m_numctr;
    ibex::Array<ibex::ExprSymbol const> const & m_var_array;
    ibex::CtcFwdBwd * m_ctc = nullptr;

public:
    contractor_ibex_fwdbwd(box const & box, nonlinear_constraint const * const ctr);
    ~contractor_ibex_fwdbwd();
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_ibex_polytope : contractor using IBEX POLYTOPE
class contractor_ibex_polytope : public contractor_cell {
private:
    vector<nonlinear_constraint const *> m_ctrs;
    double const                         m_prec;

    // TODO(soonhok): this is a hack to avoid const problem, we need to fix them
    mutable ibex::SystemFactory *            m_sf  = nullptr;
    mutable ibex::System *                   m_sys = nullptr;
    mutable ibex::System *                   m_sys_eqs = nullptr;
    mutable ibex::LinearRelaxCombo *         m_lrc = nullptr;
    mutable std::vector<ibex::Ctc *>         m_sub_ctcs;
    mutable ibex::Ctc *                      m_ctc = nullptr;

    void init(box const & box) const;

public:
    contractor_ibex_polytope(double const prec, std::vector<nonlinear_constraint const *> const & ctrs);
    ~contractor_ibex_polytope();
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

contractor mk_contractor_ibex_polytope(double const prec, std::vector<nonlinear_constraint const *> const & ctrs);
contractor mk_contractor_ibex_fwdbwd(box const & box, nonlinear_constraint const * const ctr);

}  // namespace dreal
