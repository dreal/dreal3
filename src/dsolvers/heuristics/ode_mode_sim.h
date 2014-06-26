/*********************************************************************
Author: Daniel Bryce <dbryce@sift.net>
        Soonho Kong <soonhok@cs.cmu.edu>
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
#include <unordered_map>
#include <string>
#include <vector>
#include "capd/capdlib.h"

#include "dsolvers/ode_solver.h"

using capd::C0Rect2Set;
using capd::IFunction;
using capd::IMap;
using capd::ITaylor;
using capd::ITimeMap;
using capd::IVector;
using capd::DVector;
using capd::interval;


namespace dreal {
class ode_mode_sim {
 public:
  ode_mode_sim(SMTConfig &, Egraph &, Enode* l_int, // vector<Enode*> invs,
                std::unordered_map<Enode*, int> & enode_to_rp_id);
  ~ode_mode_sim();
  ode_solver::ODE_result compute_forward(vector<pair<capd::interval, DVector>>  & bucket);
  void update(rp_box b);
  void update_box(rp_box b, DVector v, DVector prev, capd::interval time);
  Enode* getTime() const { return m_time; }
 private:
  bool check_invariant(capd::DVector & iv, capd::IVector const & inv);


  capd::IVector extract_invariants();
  bool inner_loop_forward(capd::DTaylor & solver,
                          capd::interval const & prevTime,
                          vector<pair<interval, DVector>>  & bucket);
  bool contain_NaN(capd::DVector const & s);
  capd::IVector varlist_to_IVector(vector<Enode*> const & vars);
  capd::DVector varlist_to_DVector(vector<Enode*> const & vars);
  vector<pair<int, double>> rp_id_value(DVector & values);
    SMTConfig& m_config;
    std::unordered_map<Enode *, int> & m_enode_to_rp_id;
    double                         m_stepControl;
    std::vector<Enode*>            m_invs;
    std::vector<std::string>       m_ode_list;
    std::vector<std::string>       m_par_list;
    std::vector<std::string>       m_var_list;
    std::vector<Enode*>            m_0_vars;
    std::vector<Enode*>            m_t_vars;
    std::vector<Enode*>            m_0_pars;
    std::vector<Enode*>            m_t_pars;
    capd::DVector                  m_X_0;
    capd::IVector                  m_X_t;
    capd::IVector                  m_inv;
    Enode *                        m_time;
    capd::interval                 m_T;
    std::string                    m_diff_sys_forward;
    std::string                    m_diff_sys_backward;
    unsigned                       m_mode;
    unsigned                       m_step;
    std::vector<capd::DFunction>   m_funcs;
    bool                           m_trivial;  // on if there is no ODE variables (possibly have params)
    rp_box m_b;
    inline double get_lb(Enode * const e) const { return rp_binf(rp_box_elem(m_b, m_enode_to_rp_id[e])); }
    inline double get_ub(Enode * const e) const { return rp_bsup(rp_box_elem(m_b, m_enode_to_rp_id[e])); }

    template<typename T>
    void set_params(T & f) {
        for (Enode * const par : m_0_pars) {
          double const lb = get_lb(par);
          // double const ub = get_ub(par);
          // capd::interval const intv = capd::interval(lb, ub);
          string const & name = par->getCar()->getName();
          DREAL_LOG_DEBUG << "ode_solver::set_params " << name << "\t = " << lb;
          f.setParameter(name, lb);
        }
    }
};
}
