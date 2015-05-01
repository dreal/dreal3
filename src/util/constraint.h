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
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <initializer_list>
#include <iostream>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/flow.h"

namespace dreal {

enum class constraint_type { Nonlinear, ODE, Integral, ForallT, Forall, Exists };
std::ostream & operator<<(std::ostream & out, constraint_type const & ty);

class constraint {
protected:
    constraint_type const m_type;
    std::vector<Enode *> m_enodes;
    std::unordered_set<Enode *> m_vars;

public:
    explicit constraint(constraint_type ty);
    constraint(constraint_type ty, Enode * const e);
    constraint(constraint_type ty, std::vector<Enode *> const & enodes);
    constraint(constraint_type ty, std::vector<Enode *> const & enodes_1, std::vector<Enode *> const & enodes_2);
    inline constraint_type const & get_type() const { return m_type; }
    inline std::vector<Enode *> const & get_enodes() const { return m_enodes; }
    inline std::unordered_set<Enode *> const & get_vars() const { return m_vars; }
    virtual std::ostream & display(std::ostream & out) const = 0;
    virtual ~constraint() { }
    friend std::ostream & operator<<(std::ostream & out, constraint const & c);
};

std::ostream & operator<<(ostream & out, constraint const & c);

class nonlinear_constraint : public constraint {
private:
    Enode * const m_enode;
    ibex::ExprCtr const * m_exprctr;
    ibex::NumConstraint const * m_numctr;
    ibex::NumConstraint const * m_numctr_ineq;
    ibex::Array<ibex::ExprSymbol const> m_var_array;
    std::pair<lbool, ibex::Interval> eval(ibex::IntervalVector const & iv) const;

public:
    explicit nonlinear_constraint(Enode * const e, lbool p = l_Undef);
    virtual ~nonlinear_constraint();
    virtual std::ostream & display(std::ostream & out) const;
    std::pair<lbool, ibex::Interval> eval(box const & b) const;
    inline ibex::ExprCtr const * get_exprctr() const { return m_exprctr; }
    inline ibex::NumConstraint const * get_numctr() const { return m_numctr; }
    ibex::Array<ibex::ExprSymbol const> const & get_var_array() const { return m_var_array; }
};

class integral_constraint : public constraint {
private:
    unsigned const             m_flow_id;
    Enode * const              m_time_0;
    Enode * const              m_time_t;
    std::vector<Enode *> const m_vars_0;
    std::vector<Enode *> const m_pars_0;
    std::vector<Enode *> const m_vars_t;
    std::vector<Enode *> const m_pars_t;
    std::vector<string>  const m_par_lhs_names;
    std::vector<std::pair<std::string, Enode *>> const m_odes;

public:
    inline unsigned get_flow_id()                    const { return m_flow_id; }
    inline Enode * get_time_0()                      const { return m_time_0; }
    inline Enode * get_time_t()                      const { return m_time_t; }
    inline std::vector<Enode *> const & get_vars_0() const { return m_vars_0; }
    inline std::vector<Enode *> const & get_vars_t() const { return m_vars_t; }
    inline std::vector<Enode *> const & get_pars_0() const { return m_pars_0; }
    inline std::vector<Enode *> const & get_pars_t() const { return m_pars_t; }
    inline std::vector<string>  const & get_par_lhs_names() const { return m_par_lhs_names; }
    inline std::vector<std::pair<std::string, Enode *>> const & get_odes() const { return m_odes; }
    integral_constraint(Enode * const e, unsigned const flow_id, Enode * const time_0, Enode * const time_t,
                        std::vector<Enode *> const & vars_0, std::vector<Enode *> const & pars_0,
                        std::vector<Enode *> const & vars_t, std::vector<Enode *> const & pars_t,
                        std::vector<string>  const & par_lhs_names,
                        std::vector<std::pair<std::string, Enode *>> const & odes);
    virtual ~integral_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

integral_constraint mk_integral_constraint(Enode * const e, std::unordered_map<std::string, flow> const & flow_map);

class forallt_constraint : public constraint {
private:
    unsigned const m_flow_id;
    Enode * const m_time_0;
    Enode * const m_time_t;
    Enode * const m_inv;

public:
    inline unsigned get_flow_id()  const { return m_flow_id; }
    inline Enode * get_time_0() const { return m_time_0; }
    inline Enode * get_time_t() const { return m_time_t; }
    inline Enode * get_inv()    const { return m_inv; }
    explicit forallt_constraint(Enode * e);
    forallt_constraint(Enode * const e, unsigned const flow_id, Enode * const time_0, Enode * const time_t, Enode * const inv);
    virtual ~forallt_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

forallt_constraint mk_forallt_constraint(Enode * const e);

class ode_constraint : public constraint {
private:
    integral_constraint const m_int;
    std::vector<forallt_constraint> const m_invs;

public:
    ode_constraint(integral_constraint const & integral, std::vector<forallt_constraint> const & invs);
    inline integral_constraint const & get_ic() const { return m_int; }
    inline std::vector<forallt_constraint> const & get_invs() const { return m_invs; }
    virtual ~ode_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

class forall_constraint : public constraint {
private:
    std::vector<nonlinear_constraint> m_ctrs;
    std::vector<Enode *> m_vars;
public:
    forall_constraint(Enode * const e, lbool const p);
    virtual ~forall_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

class exists_constraint : public constraint {
private:
    std::vector<nonlinear_constraint> m_ctrs;
    std::vector<Enode *> m_vars;
public:
    exists_constraint(Enode * const e, lbool const p);
    virtual ~exists_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

constraint * mk_quantified_constraint(Enode * const e, lbool const p);

}  // namespace dreal
