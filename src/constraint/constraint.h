/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@mit.edu>

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
#include <cstddef>
#include <initializer_list>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "ibex/ibex.h"
#include "minisat/core/SolverTypes.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/flow.h"

namespace dreal {

enum class constraint_type { Nonlinear, ODE, Integral, ForallT, Exists, Forall };
std::ostream & operator<<(std::ostream & out, constraint_type const & ty);

/// Base constraint class.
class constraint {
public:
    /// (DELETED) Default constructor.
    constraint() = delete;
    /// Copy-constructs an constraint from an lvalue.
    constraint(constraint const & e) = default;
    /// Move-constructs an constraint from an rvalue.
    constraint(constraint && e) = default;
    /// Copy-assigns an constraint from an lvalue.
    constraint & operator=(const constraint & e) = delete;
    /// Move-assigns an constraint from an rvalue.
    constraint & operator=(constraint && e) = delete;
    /// Constructr a constraint class whose type is @p ty
    explicit constraint(constraint_type ty);

    /// Return whether it's simple nonlinear constraint or not
    bool is_simple_nonlinear() { return m_type == constraint_type::Nonlinear; }
    /// Return constraint_type
    constraint_type const & get_type() const { return m_type; }

    virtual std::vector<Enode *> get_enodes() const = 0;
    virtual std::unordered_set<Enode *> get_occured_vars() const = 0;

    /// Evaluate the current constraint over a given box @p b.
    ///
    /// Return occured variables in constraints (in a form of Enodes)
    ///
    /// @returns First part of a return value is to indicate whether
    /// the constraint is satisfied (true), rejected (false), or
    /// unknown (undef) due to interval approximation.
    virtual std::pair<lbool, ibex::Interval> eval(box const & b) const = 0;

    /// Return a max error of the function given an interval assignment, @p b.
    /// @note eval_error(b) >= 0.0
    virtual double eval_error(box const & b) const = 0;

    /// Return a gradient vector of the function at @p iv.
    virtual ibex::IntervalVector grad(ibex::IntervalVector const & iv) const = 0;
    virtual std::ostream & display(std::ostream & out) const = 0;
    virtual std::ostream & display_dr(std::ostream & out) const = 0;
    friend std::ostream & operator<<(std::ostream & out, constraint const & c);

private:
    /// Type of constraint
    constraint_type const m_type;
    /// Associated constraints (in the form of Enode *)
    std::vector<Enode *> m_enodes;
    /// Occured Variables
    std::unordered_set<Enode *> m_occured_vars;
};
std::ostream & operator<<(std::ostream & out, constraint const & c);

/// Nonlinear constraint class. It wraps ibex::NumConstraint class.
class nonlinear_constraint : public constraint {
public:
    /// Construct a nonlinear_constraint based on a given constraint
    /// @p e. A set of domain variables, @p domain_vars, is
    /// provided. An optional substitution map from a variable (Enode
    /// *) to an interval is also provided.
    nonlinear_constraint(Enode * const e, std::unordered_set<Enode *> const & domain_vars,
                         lbool const p, std::unordered_map<Enode *, ibex::Interval> const & subst =
                                            std::unordered_map<Enode *, ibex::Interval>());
    std::shared_ptr<ibex::NumConstraint> const & get_numctr() const;
    ibex::Array<ibex::ExprSymbol const> const & get_var_array() const;
    Enode * get_enode() const { return m_enode; }
    std::vector<Enode *> get_enodes() const override { return {m_enode}; }
    std::unordered_set<Enode *> get_occured_vars() const override { return m_enode->get_vars(); }

    std::ostream & display(std::ostream & out) const override;
    std::ostream & display_dr(std::ostream &) const override;
    std::pair<lbool, ibex::Interval> eval(box const & b) const override;
    ibex::IntervalVector grad(ibex::IntervalVector const & iv) const override {
        return get_numctr()->f.gradient(iv);
    }
    double eval_error(box const & b) const override;
    bool is_neq() const { return m_polarity == l_False && m_enode->isEq(); }
    bool operator==(nonlinear_constraint const & nc) const {
        return get_numctr() == nc.get_numctr();
    }

private:
    Enode * const m_enode;
    lbool const m_polarity;
    std::unordered_set<Enode *> const m_domain_vars;
    std::unordered_map<Enode *, ibex::Interval> const m_subst;

    mutable std::mutex m_map_lock;
    mutable std::unordered_map<std::thread::id, std::shared_ptr<ibex::NumConstraint>> m_numctr_map;
    mutable std::unordered_map<std::thread::id, ibex::Array<ibex::ExprSymbol const>>
        m_var_array_map;

    std::pair<lbool, ibex::Interval> eval(ibex::IntervalVector const & iv) const;
    double eval_error(ibex::IntervalVector const & iv) const;  // gevaluate error function
    void build_maps() const;
};

class integral_constraint : public constraint {
public:
    integral_constraint(Enode * const e, int const flow_id, Enode * const time_0,
                        Enode * const time_t, std::vector<Enode *> const & vars_0,
                        std::vector<Enode *> const & pars_0, std::vector<Enode *> const & vars_t,
                        std::vector<Enode *> const & pars_t,
                        std::vector<Enode *> const & par_lhs_names,
                        std::vector<std::pair<Enode *, Enode *>> const & odes);
    int get_flow_id() const { return m_flow_id; }
    Enode * get_time_0() const { return m_time_0; }
    Enode * get_time_t() const { return m_time_t; }
    std::vector<Enode *> const & get_vars_0() const { return m_vars_0; }
    std::vector<Enode *> const & get_vars_t() const { return m_vars_t; }
    std::vector<Enode *> const & get_pars_0() const { return m_pars_0; }
    std::vector<Enode *> const & get_pars_t() const { return m_pars_t; }
    std::vector<Enode *> const & get_par_lhs_names() const { return m_par_lhs_names; }
    std::vector<std::pair<Enode *, Enode *>> const & get_odes() const { return m_odes; }
    Enode * get_enode() const { return m_enode; }
    std::vector<Enode *> get_enodes() const override { return {m_enode}; }
    std::unordered_set<Enode *> get_occured_vars() const override { return m_enode->get_vars(); }

    std::pair<lbool, ibex::Interval> eval(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    double eval_error(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    ibex::IntervalVector grad(ibex::IntervalVector const & /* iv */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    std::ostream & display(std::ostream & out) const override;
    std::ostream & display_dr(std::ostream &) const override {
        throw std::runtime_error("not implemented yet.");
    }

private:
    Enode * const m_enode;
    int const m_flow_id;
    Enode * const m_time_0;
    Enode * const m_time_t;
    std::vector<Enode *> const m_vars_0;
    std::vector<Enode *> const m_pars_0;
    std::vector<Enode *> const m_vars_t;
    std::vector<Enode *> const m_pars_t;
    std::vector<Enode *> const m_par_lhs_names;
    std::vector<std::pair<Enode *, Enode *>> const m_odes;
};

class forallt_constraint;
forallt_constraint mk_forallt_constraint(Enode * const e,
                                         std::unordered_set<Enode *> const & var_set);

class forallt_constraint : public constraint {
public:
    forallt_constraint(Enode * const e, std::unordered_set<Enode *> const & var_set,
                       int const flow_id, Enode * const time_0, Enode * const time_t,
                       Enode * const inv);
    forallt_constraint(Enode * const e, std::unordered_set<Enode *> const & var_set)
        : forallt_constraint(mk_forallt_constraint(e, var_set)) {}
    std::vector<std::shared_ptr<nonlinear_constraint>> get_nl_ctrs() const { return m_nl_ctrs; }
    int get_flow_id() const { return m_flow_id; }
    Enode * get_time_0() const { return m_time_0; }
    Enode * get_time_t() const { return m_time_t; }
    Enode * get_inv() const { return m_inv; }
    Enode * get_enode() const { return m_enode; }
    std::vector<Enode *> get_enodes() const override { return {m_enode}; }
    std::unordered_set<Enode *> get_occured_vars() const override { return m_enode->get_vars(); }

    std::pair<lbool, ibex::Interval> eval(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    double eval_error(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    ibex::IntervalVector grad(ibex::IntervalVector const & /* iv */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    std::ostream & display(std::ostream & out) const override;
    std::ostream & display_dr(std::ostream &) const override {
        throw std::runtime_error("not implemented yet.");
    }

private:
    Enode * const m_enode;
    std::vector<std::shared_ptr<nonlinear_constraint>> m_nl_ctrs;
    int const m_flow_id;
    Enode * const m_time_0;
    Enode * const m_time_t;
    Enode * const m_inv;
};

class ode_constraint : public constraint {
public:
    explicit ode_constraint(integral_constraint const & integral,
                            std::vector<std::shared_ptr<forallt_constraint>> const & invs =
                                std::vector<std::shared_ptr<forallt_constraint>>());
    integral_constraint const & get_ic() const { return m_int; }
    std::vector<std::shared_ptr<forallt_constraint>> const & get_invs() const { return m_invs; }
    std::vector<Enode *> get_enodes() const override;
    std::unordered_set<Enode *> get_occured_vars() const override;

    std::pair<lbool, ibex::Interval> eval(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    double eval_error(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    ibex::IntervalVector grad(ibex::IntervalVector const & /* iv */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    std::ostream & display(std::ostream & out) const override;
    std::ostream & display_dr(std::ostream &) const override {
        throw std::runtime_error("not implemented yet.");
    }

private:
    integral_constraint const m_int;
    std::vector<std::shared_ptr<forallt_constraint>> const m_invs;
};

/// This class is to support forall quantifier without a hack.
class forall_constraint : public constraint {
public:
    forall_constraint(Enode * const e, lbool const p);
    std::ostream & display(std::ostream & out) const override;
    std::ostream & display_dr(std::ostream &) const override {
        throw std::runtime_error("not implemented yet.");
    }
    std::unordered_set<Enode *> get_forall_vars() const;
    Enode * get_body() const;
    Enode * get_enode() const { return m_enode; }
    std::vector<Enode *> get_enodes() const override { return {m_enode}; }
    std::unordered_set<Enode *> get_occured_vars() const override {
        return m_enode->get_exist_vars();
    }

    lbool get_polarity() const { return m_polarity; }
    std::pair<lbool, ibex::Interval> eval(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    double eval_error(box const & /* b */) const override {
        throw std::runtime_error("not implemented yet.");
    }
    ibex::IntervalVector grad(ibex::IntervalVector const & /* iv */) const override {
        throw std::runtime_error("not implemented yet.");
    }

private:
    Enode * const m_enode;
    std::unordered_set<Enode *> const m_forall_vars;
    Enode * const m_body;
    lbool const m_polarity;

    std::unordered_set<Enode *> extract_forall_vars(Enode const * elist);
};

integral_constraint mk_integral_constraint(Enode * const e,
                                           std::unordered_map<std::string, flow> const & flow_map);

}  // namespace dreal

namespace std {
template <>
struct hash<::dreal::nonlinear_constraint> {
public:
    size_t operator()(dreal::nonlinear_constraint const & ctr) const {
        return hash<uintptr_t>()(reinterpret_cast<uintptr_t>(ctr.get_numctr().get()));
    }
};
}  // namespace std
