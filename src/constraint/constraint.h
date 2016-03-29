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
#include <iostream>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/flow.h"

namespace dreal {
enum class constraint_type { Nonlinear, ODE, Integral, ForallT, Exists, GenericForall };
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
    virtual ~constraint() noexcept { }
    friend std::ostream & operator<<(std::ostream & out, constraint const & c);
};
std::ostream & operator<<(std::ostream & out, constraint const & c);

class nonlinear_constraint : public constraint {
private:
    bool const                               m_is_neq;
    std::shared_ptr<ibex::NumConstraint>     m_numctr;
    ibex::Array<ibex::ExprSymbol const>      m_var_array;
    std::pair<lbool, ibex::Interval> eval(ibex::IntervalVector const & iv) const;

public:
    nonlinear_constraint(Enode * const e, std::unordered_set<Enode*> const & var_set, lbool const p, std::unordered_map<Enode*, ibex::Interval> const & subst = std::unordered_map<Enode *, ibex::Interval>());
    virtual std::ostream & display(std::ostream & out) const;
    std::pair<lbool, ibex::Interval> eval(box const & b) const;
    inline std::shared_ptr<ibex::NumConstraint> get_numctr() const { return m_numctr; }
    ibex::Array<ibex::ExprSymbol const> const & get_var_array() const { return m_var_array; }
    inline Enode * get_enode() const { return get_enodes()[0]; }
    bool is_neq() const { return m_is_neq; }
    bool operator==(nonlinear_constraint const & nc) const {
        return m_numctr == nc.m_numctr;
    }
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
    std::vector<Enode *> const m_par_lhs_names;
    std::vector<std::pair<Enode *, Enode *>> const m_odes;

public:
    inline unsigned get_flow_id()                    const { return m_flow_id; }
    inline Enode * get_time_0()                      const { return m_time_0; }
    inline Enode * get_time_t()                      const { return m_time_t; }
    inline std::vector<Enode *> const & get_vars_0() const { return m_vars_0; }
    inline std::vector<Enode *> const & get_vars_t() const { return m_vars_t; }
    inline std::vector<Enode *> const & get_pars_0() const { return m_pars_0; }
    inline std::vector<Enode *> const & get_pars_t() const { return m_pars_t; }
    inline std::vector<Enode *>  const & get_par_lhs_names() const { return m_par_lhs_names; }
    inline std::vector<std::pair<Enode *, Enode *>> const & get_odes() const { return m_odes; }
    inline Enode * get_enode() const { return get_enodes()[0]; }
    integral_constraint(Enode * const e, unsigned const flow_id, Enode * const time_0, Enode * const time_t,
                        std::vector<Enode *> const & vars_0, std::vector<Enode *> const & pars_0,
                        std::vector<Enode *> const & vars_t, std::vector<Enode *> const & pars_t,
                        std::vector<Enode *> const & par_lhs_names,
                        std::vector<std::pair<Enode *, Enode *>> const & odes);
    virtual std::ostream & display(std::ostream & out) const;
};

integral_constraint mk_integral_constraint(Enode * const e, std::unordered_map<std::string, flow> const & flow_map);

class forallt_constraint;
forallt_constraint mk_forallt_constraint(Enode * const e, std::unordered_set<Enode*> const & var_set);

class forallt_constraint : public constraint {
private:
    std::vector<std::shared_ptr<nonlinear_constraint>> m_nl_ctrs;
    unsigned const m_flow_id;
    Enode * const m_time_0;
    Enode * const m_time_t;
    Enode * const m_inv;

public:
    std::vector<std::shared_ptr<nonlinear_constraint>> get_nl_ctrs() const { return m_nl_ctrs; }
    inline unsigned get_flow_id()  const { return m_flow_id; }
    inline Enode * get_time_0() const { return m_time_0; }
    inline Enode * get_time_t() const { return m_time_t; }
    inline Enode * get_inv()    const { return m_inv; }
    forallt_constraint(Enode * const e, std::unordered_set<Enode*> const & var_set, unsigned const flow_id, Enode * const time_0, Enode * const time_t, Enode * const inv);
    forallt_constraint(Enode * const e, std::unordered_set<Enode*> const & var_set) : forallt_constraint(mk_forallt_constraint(e, var_set)) { }

    virtual std::ostream & display(std::ostream & out) const;
};


class ode_constraint : public constraint {
private:
    integral_constraint const m_int;
    std::vector<std::shared_ptr<forallt_constraint>> const m_invs;

public:
    explicit ode_constraint(integral_constraint const & integral, std::vector<std::shared_ptr<forallt_constraint>> const & invs = std::vector<std::shared_ptr<forallt_constraint>>());
    inline integral_constraint const & get_ic() const { return m_int; }
    inline std::vector<std::shared_ptr<forallt_constraint>> const & get_invs() const { return m_invs; }
    virtual std::ostream & display(std::ostream & out) const;
};

// This class is to support forall quantifier without a hack.
class generic_forall_constraint : public constraint {
private:
    std::unordered_set<Enode *> const m_forall_vars;
    Enode * const                     m_body;
    lbool const                       m_polarity;

    std::unordered_set<Enode *> extract_forall_vars(Enode const * elist);

public:
    generic_forall_constraint(Enode * const e, lbool const p);
    virtual std::ostream & display(std::ostream & out) const;
    std::unordered_set<Enode *> get_forall_vars() const;
    Enode * get_body() const;
    inline Enode * get_enode() const { return get_enodes()[0]; }
    inline lbool get_polarity() const { return m_polarity; }
};
}  // namespace dreal

namespace std {
template<>
struct hash<::dreal::nonlinear_constraint> {
public:
    size_t operator()(dreal::nonlinear_constraint const & ctr) const;
};
}  // namespace std
