/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <list>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "capd/capdlib.h"
#include "util/logging.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "realpaver/rp_box.h"

namespace dreal {
class ode_solver {
public:
    ode_solver(SMTConfig& c,
               Egraph & e,
               Enode * l_int,
               std::vector<Enode*> invs,
               std::unordered_map<Enode*, int>& enode_to_rp_id);
    ~ode_solver();

    enum class ODE_result {SAT, UNSAT, EXCEPTION, TIMEOUT};

    ODE_result          simple_ODE(rp_box b, bool forward);
    ODE_result          solve_forward(rp_box b);
    ODE_result          solve_backward(rp_box b);
    void                print_trajectory(ostream& out) const;
    double              logVolume_X0(rp_box b) const;
    double              logVolume_Xt(rp_box b) const;
    unsigned            get_Mode() const { return m_mode; }

private:
    std::vector<Enode*> get_X0() const { return m_0_vars; }
    std::vector<Enode*> get_Xt() const { return m_t_vars; }
    Enode *             get_Time() const { return m_time; }
    std::vector<double> extract_X0T(rp_box b) const;
    std::vector<double> extract_XtT(rp_box b) const;
    std::vector<double> extract_X0XtT(rp_box b) const;

    // Private Members
    SMTConfig& m_config;
    Egraph &                       m_egraph;
    Enode *                        m_int;
    std::vector<Enode*>            m_invs;
    rp_box m_b;
    std::unordered_map<Enode*, int>& m_enode_to_rp_id;
    std::list<std::pair<capd::interval, capd::IVector>> m_trajectory;
    double                         m_stepControl;
    std::vector<std::string>       m_ode_list;
    std::vector<std::string>       m_par_list;
    std::vector<std::string>       m_var_list;
    std::vector<Enode*>            m_0_vars;
    std::vector<Enode*>            m_t_vars;
    std::vector<Enode*>            m_0_pars;
    std::vector<Enode*>            m_t_pars;
    capd::IVector                  m_X_0;
    capd::IVector                  m_X_t;
    capd::IVector                  m_inv;
    Enode *                        m_time;
    capd::interval                 m_T;
    std::string                    m_diff_sys_forward;
    std::string                    m_diff_sys_backward;
    unsigned                       m_mode;
    unsigned                       m_step;
    std::vector<capd::IFunction>   m_funcs;

    // Private Methods
    ode_solver& operator=(const ode_solver& o);
    void update(rp_box b);
    void print_datapoint(ostream& out, const capd::interval& t, const capd::interval& v) const;
    void print_trace(ostream& out, string const & key, int const idx,
                     list<pair<capd::interval, capd::IVector>> const & trajectory) const;
    void prune_trajectory(capd::interval& t, capd::IVector& e);
    capd::IVector varlist_to_IVector(vector<Enode*> const & vars);
    capd::IVector extract_invariants();
    void IVector_to_varlist(capd::IVector const & v, vector<Enode*> & vars);

    bool check_invariant(capd::IVector & iv, capd::IVector const & inv);
    bool check_invariant(capd::C0Rect2Set & s, capd::IVector const & inv);
    bool contain_NaN(capd::IVector const & v);
    bool contain_NaN(capd::C0Rect2Set const & s);

    template<typename V>
    bool union_and_join(vector<V> const & bucket, V & result);
    bool inner_loop_forward(capd::ITaylor & solver,
                            capd::interval prevTime,
                            std::vector<std::pair<capd::interval, capd::IVector>> & bucket);
    bool inner_loop_backward(capd::ITaylor & solver,
                            capd::interval prevTime,
                            std::vector<std::pair<capd::interval, capd::IVector>> & bucket);
    ODE_result simple_ODE_forward(capd::IVector const & X_0,
                                  capd::IVector & X_t,
                                  capd::interval const & T,
                                  capd::IVector const & inv,
                                  vector<capd::IFunction> & funcs);
    ODE_result simple_ODE_backward(capd::IVector & X_0,
                                   capd::IVector const & X_t,
                                   capd::interval const & T,
                                   capd::IVector const & inv,
                                   vector<capd::IFunction> & funcs);
    bool updateValue(rp_box b, Enode * e, double lb, double ub);
    ODE_result compute_forward(std::vector<std::pair<capd::interval, capd::IVector>> & bucket);
    ODE_result prune_forward(std::vector<std::pair<capd::interval, capd::IVector>> & bucket);
    ODE_result compute_backward(std::vector<std::pair<capd::interval, capd::IVector>> & bucket);
    ODE_result prune_backward(std::vector<std::pair<capd::interval, capd::IVector>> & bucket);
    bool prune_params();

    template<typename T>
    void set_params(T & f) {
        for (Enode * const par : m_0_pars) {
            double const lb = get_lb(par);
            double const ub = get_ub(par);
            capd::interval const intv = capd::interval(lb, ub);
            string const & name = par->getCar()->getName();
            DREAL_LOG_DEBUG << "ode_solver::set_params " << name << "\t = " << intv;
            f.setParameter(name, intv);
        }
    }
    // Inline functions
    inline double get_lb(Enode* const e) const { return rp_binf(rp_box_elem(m_b, m_enode_to_rp_id[e])); }
    inline double get_ub(Enode* const e) const { return rp_bsup(rp_box_elem(m_b, m_enode_to_rp_id[e])); }
    inline void set_lb(Enode* const e, double v) { rp_binf(rp_box_elem(m_b, m_enode_to_rp_id[e])) = v; }
    inline void set_ub(Enode* const e, double v) { rp_bsup(rp_box_elem(m_b, m_enode_to_rp_id[e])) = v; }
    inline void set_empty_interval(Enode* const e) { rp_interval_set_empty(rp_box_elem(m_b, m_enode_to_rp_id[e])); }
};

ostream& operator<<(ostream& out, ode_solver::ODE_result ret);
}
