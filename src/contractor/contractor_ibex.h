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
#include <unordered_set>
#include <vector>
#include <initializer_list>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "contractor/contractor_basic.h"

namespace dreal {

class contractor_ibex_fwdbwd : public contractor_cell {
private:
    nonlinear_constraint const * m_ctr;
    ibex::NumConstraint const * m_numctr;
    ibex::Array<ibex::ExprSymbol const> const & m_var_array;
    std::unique_ptr<ibex::CtcFwdBwd> m_ctc;

public:
    contractor_ibex_fwdbwd(box const & box, nonlinear_constraint const * const ctr);
    void prune(box & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_ibex_newton : public contractor_cell {
private:
    nonlinear_constraint const * m_ctr;
    ibex::NumConstraint const * m_numctr;
    ibex::Array<ibex::ExprSymbol const> const & m_var_array;
    std::unique_ptr<ibex::CtcNewton> m_ctc;

public:
    contractor_ibex_newton(box const & box, nonlinear_constraint const * const ctr);
    void prune(box & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_ibex_hc4 : contractor using IBEX HC4
class contractor_ibex_hc4 : public contractor_cell {
private:
    std::unordered_set<Enode *>               m_vars_in_ctrs;
    std::vector<nonlinear_constraint const *> m_ctrs;
    double const                              m_prec;
    std::unique_ptr<ibex::Ctc>              m_ctc = nullptr;;

public:
    contractor_ibex_hc4(double const prec, std::vector<Enode *> const & vars, std::vector<nonlinear_constraint const *> const & ctrs);
    void prune(box & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_ibex_polytope : contractor using IBEX POLYTOPE
class contractor_ibex_polytope : public contractor_cell {
private:
    std::unordered_set<Enode *>               m_vars_in_ctrs;
    std::vector<nonlinear_constraint const *> m_ctrs;
    double const                              m_prec;
    std::unordered_map<Enode *, ibex::Variable const *> m_var_cache;
    std::unordered_map<Enode *, ibex::ExprCtr const *> m_exprctr_cache_pos;
    std::unordered_map<Enode *, ibex::ExprCtr const *> m_exprctr_cache_neg;

    // TODO(soonhok): this is a hack to avoid const problem, we need to fix them
    mutable std::unique_ptr<ibex::SystemFactory>    m_sf = nullptr;
    mutable std::unique_ptr<ibex::System>           m_sys = nullptr;
    mutable ibex::System *                          m_sys_eqs = nullptr;
    mutable std::unique_ptr<ibex::LinearRelaxCombo> m_lrc = nullptr;
    mutable std::vector<std::unique_ptr<ibex::Ctc>> m_sub_ctcs;
    mutable std::unique_ptr<ibex::Ctc>              m_ctc = nullptr;;
    ibex::SystemFactory* build_system_factory(std::vector<Enode *> const & vars, std::vector<nonlinear_constraint const *> const & ctrs);

public:
    contractor_ibex_polytope(double const prec, std::vector<Enode *> const & vars, std::vector<nonlinear_constraint const *> const & ctrs);
    ~contractor_ibex_polytope();
    void prune(box & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

contractor mk_contractor_ibex_fwdbwd(box const & box, nonlinear_constraint const * const ctr);
contractor mk_contractor_ibex_newton(box const & box, nonlinear_constraint const * const ctr);
contractor mk_contractor_ibex_hc4(double const prec, std::vector<Enode *> const & vars, std::vector<nonlinear_constraint const *> const & ctrs);
contractor mk_contractor_ibex_polytope(double const prec, std::vector<Enode *> const & vars, std::vector<nonlinear_constraint const *> const & ctrs);

}  // namespace dreal
