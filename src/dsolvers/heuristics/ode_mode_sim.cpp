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

#include <algorithm>
#include <chrono>
#include <iomanip>
#include <limits>
#include <map>
#include <math.h>
#include <sstream>
#include <string>
#include <time.h>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include "util/logging.h"
#include "util/string.h"
#include "dsolvers/heuristics/ode_mode_sim.h"

using capd::C0Rect2Set;
using capd::DFunction;
using capd::DMap;
using capd::DTaylor;
using capd::DTimeMap;
using capd::DVector;
using capd::interval;
using std::chrono::duration_cast;
using std::chrono::high_resolution_clock;
using std::chrono::milliseconds;
using std::exception;
using std::find_if;
using std::get;
using std::map;
using std::max;
using std::min;
using std::numeric_limits;
using std::reverse;
using std::setw;
using std::stoi;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unordered_map;
using std::unordered_set;



namespace dreal{

  ode_mode_sim::ode_mode_sim(SMTConfig &config, Egraph &egraph, Enode* l_int, //  vector<Enode*> invs,
                             std::unordered_map<Enode*, int> & enode_to_rp_id) :
    m_config(config),
    m_enode_to_rp_id(enode_to_rp_id),
    m_stepControl(config.nra_ODE_step) {
    m_mode = l_int->getCdr()->getCar()->getValue();
    m_time = l_int->getCdr()->getCdr()->getCdr()->getCar();
    string time_str = m_time->getCar()->getName();                       //  i.e. "time_1"
    m_step = stoi(time_str.substr(time_str.find_last_of("_") + 1));      //  i.e. 1
    string flow_step = (egraph.stepped_flows ? to_string(m_step) + "_" : "");

    m_stepControl = 0.1; //  config.nra_precision;

    unordered_map<string, Enode *> & flow_map = egraph.flow_maps[string("flow_") + flow_step  + to_string(m_mode)];
    Enode * var_list = l_int->getCdr()->getCdr()->getCdr()->getCdr();

    //  Collect _0, _t variables from variable list in integral literal
    while (!var_list->isEnil()) {
        string name = var_list->getCar()->getCar()->getName();
        size_t second_ = name.find_last_of("_");
        size_t first_ = name.find_last_of("_", second_ - 1);
        string name_prefix, name_postfix;
        if (first_ == string::npos) {
            name_prefix = name.substr(0, second_);
            name_postfix = name.substr(second_);
        } else {
            name_prefix = name.substr(0, first_);
            name_postfix = name.substr(first_);
        }
        if (flow_map.find(name_prefix) == flow_map.end()) {
            cerr << name_prefix << " is not found in flow_map." << endl;
            assert(flow_map.find(name_prefix) != flow_map.end());
        }

        Enode * const rhs = flow_map[name_prefix];
        stringstream ss;
        rhs->print_infix(ss, true, name_postfix);
        Enode * const _0_var = var_list->getCar();
        Enode * const _t_var = var_list->getCdr()->getCar();
        if (rhs->isConstant() && rhs->getValue() == 0.0) {
            //  If RHS of ODE == 0.0, we treat it as a parameter in CAPD
            m_0_pars.push_back(_0_var);
            m_t_pars.push_back(_t_var);
            m_par_list.push_back(name);
        } else {
            //  Otherwise, we treat it as an ODE variable.
            m_0_vars.push_back(_0_var);
            m_t_vars.push_back(_t_var);
            m_var_list.push_back(name);
            m_ode_list.push_back(ss.str());
        }
        var_list = var_list->getCdr()->getCdr();
    }

    //  join var_list to make diff_var, ode_list to diff_fun_forward
    string diff_var = "";
    if (!m_var_list.empty()) {
        diff_var = "var:" + join(m_var_list, ", ") + ";";
        m_trivial = false;
    } else {
        m_trivial = true;
    }
    string diff_fun_forward = "";
    string diff_fun_backward = "";
    if (!m_ode_list.empty()) {
        diff_fun_forward = "fun:" + join(m_ode_list, ", ") + ";";
        diff_fun_backward = "fun: -" + join(m_ode_list, ", -") + ";";
    }
    //  construct diff_sys_forward (string to CAPD)
    string diff_par;
    if (m_par_list.size() > 0) {
        diff_par = "par:" + join(m_par_list, ", ") + ";";
        m_diff_sys_forward = diff_par;
        m_diff_sys_backward = diff_par;
    }
    m_diff_sys_forward  += diff_var + diff_fun_forward;
    m_diff_sys_backward += diff_var + diff_fun_backward;
    DREAL_LOG_INFO << "ode_mode_sim::ode_mode_sim: diff_par          : " << diff_par;
    DREAL_LOG_INFO << "ode_mode_sim::ode_mode_sim: diff_var          : " << diff_var;
    DREAL_LOG_INFO << "ode_mode_sim::ode_mode_sim: diff_fun_forward  : " << diff_fun_forward;
    DREAL_LOG_INFO << "ode_mode_sim::ode_mode_sim: diff_fun_backward : " << diff_fun_backward;
    DREAL_LOG_INFO << "ode_mode_sim::ode_mode_sim: diff_sys_forward  : " << m_diff_sys_forward;
    DREAL_LOG_INFO << "ode_mode_sim::ode_mode_sim: diff_sys_backward : " << m_diff_sys_backward;
    for (auto ode_str : m_ode_list) {
        string const func_str = diff_par + diff_var + "fun:" + ode_str + ";";
        DREAL_LOG_INFO << "ode_mode_sim::ode_mode_sim: func = " << func_str;
        m_funcs.push_back(DFunction(func_str));
    };
    m_inv = extract_invariants();
  }

  ode_mode_sim::~ode_mode_sim(){
  }

  IVector ode_mode_sim::extract_invariants() {
    map<Enode*, pair<double, double>> inv_map;
    for (auto inv : m_invs) {
        Enode * p = inv->getCdr()->getCdr()->getCdr()->getCdr()->getCar();
        Enode * op = p->getCar();
        bool pos = true;

        //  Handle Negation
        if (op->getId() == ENODE_ID_NOT) {
            p = p->getCdr()->getCar();
            op = p->getCar();
            pos = false;
        }
        switch (op->getId()) {
        case ENODE_ID_GEQ:
        case ENODE_ID_GT:
            //  Handle >= & >
            pos = !pos;
        case ENODE_ID_LEQ:
        case ENODE_ID_LT: {
            //  Handle <= & <
            Enode * lhs = pos ? p->getCdr()->getCar() : p->getCdr()->getCdr()->getCar();
            Enode * rhs = pos ? p->getCdr()->getCdr()->getCar() : p->getCdr()->getCar();
            if (lhs->isVar() && rhs->isConstant()) {
                if (inv_map.find(lhs) != inv_map.end()) {
                    inv_map[lhs].second = std::min(inv_map[lhs].second, rhs->getValue());
                } else {
                    inv_map.emplace(lhs, make_pair(lhs->getLowerBound(), rhs->getValue()));
                }
            } else if (lhs->isConstant() && rhs->isVar()) {
                if (inv_map.find(rhs) != inv_map.end()) {
                    inv_map[rhs].first = std::max(inv_map[rhs].first, lhs->getValue());
                } else {
                    inv_map.emplace(rhs, make_pair(lhs->getValue(), rhs->getUpperBound()));
                }
            } else {
                DREAL_LOG_ERROR << "ode_mode_sim::extract_invariant: "
                                << "The provided invariant (" << p << ") is not of the form that we support.";
            }
        }
            break;
        default:
            DREAL_LOG_ERROR << "ode_mode_sim::extract_invariant: "
                            << "The provided invariant (" << p << ") is not of the form that we support.";
        }
    }
    IVector ret (m_t_vars.size());
    unsigned i = 0;
    for (auto const & m_t_var : m_t_vars) {
        if (inv_map.find(m_t_var) != inv_map.end()) {
            auto inv = interval(inv_map[m_t_var].first, inv_map[m_t_var].second);
            DREAL_LOG_INFO << "ode_mode_sim::extract_invariant: Invariant extracted from  " << m_t_var << " = " << inv;
            ret[i++] = inv;
        } else {
            auto inv = interval(m_t_var->getLowerBound(), m_t_var->getUpperBound());
            DREAL_LOG_INFO << "ode_mode_sim::extract_invariant: Default Invariant set for " << m_t_var << " = " << inv;
            ret[i++] = inv;
        }
    }
    return ret;
}

void ode_mode_sim::update(rp_box b) {
    m_b = b;
    m_X_0 = varlist_to_DVector(m_0_vars);
    m_X_t = varlist_to_IVector(m_t_vars);
    m_T = interval(0.0, get_ub(m_time));

    DREAL_LOG_DEBUG << "Update: " << endl
                    << "m_X_0 = " << m_X_0 << endl
                    << "m_X_t = " << m_X_t << endl
                    << "m_T = " << m_T << endl;
}

  void ode_mode_sim::update_box(rp_box b, DVector v, DVector prev,   capd::interval time) {
    //   assume v includes elements in m_X_0
    //   assign m_X_t elements in box to values in v
    for (int i = 0; i < v.size(); i++){
      Enode* _0_var = m_0_vars[i];
      Enode* _t_var = m_t_vars[i];
      DREAL_LOG_DEBUG << "ode_mode_sim::update_box set "
                      << _t_var << " = "
                      << _0_var << " = ["
                      <<  min(prev[i], v[i]) << ", " <<  max(prev[i], v[i]) << "]";

      int const rp_id = m_enode_to_rp_id[_t_var];
      rp_binf(rp_box_elem(b, rp_id)) =  max(min(prev[i], v[i]), rp_binf(rp_box_elem(b, rp_id)));
      rp_bsup(rp_box_elem(b, rp_id)) =  min(max(prev[i], v[i]), rp_bsup(rp_box_elem(b, rp_id)));
    }

    //  assign parameters at time t equal to time 0
    for (int i = 0; i < static_cast<int>(m_0_pars.size()); i++){
      Enode* _0_var = m_0_pars[i];
      Enode* _t_var = m_t_pars[i];

      int const rp_id_0 = m_enode_to_rp_id[_0_var];
      int const rp_id_t = m_enode_to_rp_id[_t_var];
      rp_binf(rp_box_elem(b, rp_id_t)) =  max(rp_binf(rp_box_elem(b, rp_id_0)), rp_binf(rp_box_elem(b, rp_id_t)));
      rp_bsup(rp_box_elem(b, rp_id_t)) = min(rp_bsup(rp_box_elem(b, rp_id_0)), rp_bsup(rp_box_elem(b, rp_id_t)));

      DREAL_LOG_DEBUG << "ode_mode_sim::update_box set "
                      << _t_var << " = "
                      << _0_var << " = "
                      << "[" << rp_binf(rp_box_elem(b, rp_id_t))
                      << ", " << rp_bsup(rp_box_elem(b, rp_id_t))
                      << "]";
    }

    //  set time variable
     int const rp_id = m_enode_to_rp_id[m_time];
     rp_binf(rp_box_elem(b, rp_id)) = max(time.leftBound(),  rp_binf(rp_box_elem(b, rp_id)));
     rp_bsup(rp_box_elem(b, rp_id)) = min(time.rightBound(), rp_bsup(rp_box_elem(b, rp_id)));
     DREAL_LOG_DEBUG << "ode_mode_sim::update_box set "
                      << m_time << " = "
                      << "[" << rp_binf(rp_box_elem(b, rp_id))
                      << ", " << rp_bsup(rp_box_elem(b, rp_id))
                      << "]";
}

IVector ode_mode_sim::varlist_to_IVector(vector<Enode*> const & vars) {
    IVector intvs (vars.size());
    /* Assign current interval values */
    for (unsigned i = 0; i < vars.size(); i++) {
        Enode* const & var = vars[i];
        interval & intv = intvs[i];
        double lb = get_lb(var);
        double ub = get_ub(var);
        intv = interval(lb, ub);
        DREAL_LOG_INFO << "ode_solver::varlist_to_IVector: The interval on " << var->getCar()->getName() << ": " << intv;
    }
    return intvs;
}

DVector ode_mode_sim::varlist_to_DVector(vector<Enode*> const & vars) {
  DVector intvs (vars.size());
    /* Assign current interval values */
    for (unsigned i = 0; i < vars.size(); i++) {
        Enode* const & var = vars[i];
        double & val = intvs[i];
        int rp_id = m_enode_to_rp_id[var];
        double lb = rp_binf(rp_box_elem(m_b, rp_id));
          // get_lb(var);
        double ub = rp_bsup(rp_box_elem(m_b, rp_id));
    // get_ub(var);
        val = lb + ((ub-lb)/2.0);//  interval(lb, ub);

        intvs[i] = val;
        DREAL_LOG_INFO << "ode_mode_sim::varlist_to_DVector: The value of " << var->getCar()->getName() << ": " << intvs[i] << " [" << lb << ", " << ub << "]";
    }
    return intvs;
}

ode_solver::ODE_result ode_mode_sim::compute_forward(vector<pair<interval, DVector>>  & bucket) {
    DREAL_LOG_INFO << "ode_mode_sim::compute_forward";
    ode_solver::ODE_result ret = ode_solver::ODE_result::SAT;
    auto start = high_resolution_clock::now();
    bool invariantViolated = false;

    if (m_trivial) {
      DREAL_LOG_INFO << "ode_mode_sim::compute_forward  trivial sat";
        return ode_solver::ODE_result::SAT;
    }

    try {
        //   Set up VectorField
        DMap vectorField(m_diff_sys_forward);
        set_params(vectorField);
        DTaylor solver(vectorField, m_config.nra_ODE_taylor_order, .001);
        DTimeMap timeMap(solver);
        DVector s(m_X_0);
        timeMap.stopAfterStep(true);
        timeMap.turnOnStepControl();

        // TODO(soonhok): visualization
        if (m_config.nra_json) {
          //              m_trajectory.clear();
          //              m_trajectory.emplace_back(timeMap.getCurrentTime(), IVector(s));
        }

        interval prevTime(0.);
        do {
            //   Handle Timeout
            if (m_config.nra_ODE_timeout > 0.0) {
                auto end = high_resolution_clock::now();
                if (duration_cast<milliseconds>(end - start).count() >= m_config.nra_ODE_timeout) {
                    DREAL_LOG_INFO << "ode_mode_sim::compute_forward: timeout";
                    return ode_solver::ODE_result::TIMEOUT;
                }
            }

            //   Check Invariant
            invariantViolated =  false; // !check_invariant(s, m_inv);
            if (invariantViolated) {
                // TODO(soonhok): invariant
              DREAL_LOG_INFO << "ode_mode_sim::compute_forward  invariant violated";
                if (timeMap.getCurrentTime() < m_T) {
                    ret = ode_solver::ODE_result::UNSAT;
                } else {
                    ret = ode_solver::ODE_result::SAT;
                }
                break;
            }

            //   Control TimeStep
            timeMap.turnOnStepControl();
            if (true //
                // m_stepControl > 0 && solver.getStep() < m_stepControl
                ) {
              m_stepControl = (m_T.rightBound()-m_T.leftBound())/1000.0;
              DREAL_LOG_INFO << "ode_mode_sim::compute_forward  using step size: " << m_stepControl;

                timeMap.turnOffStepControl();
                solver.setStep(m_stepControl);
                timeMap.setStep(m_stepControl);
            }

            //   Move s toward m_T.rightBound()
            timeMap(m_T.rightBound(), s);
            if (contain_NaN(s)) {
                DREAL_LOG_INFO << "ode_mode_sim::compute_forward: contain NaN";
                return ode_solver::ODE_result::SAT;
            }
            DREAL_LOG_INFO << "ode_mode_sim::compute_forward: m_T = " << m_T
                           << " current = " << timeMap.getCurrentTime()
                           << " prev = " << prevTime;
            if (m_T.leftBound() <= timeMap.getCurrentTime()) {
                invariantViolated = inner_loop_forward(solver, prevTime, bucket);
                if (invariantViolated) {
                    // TODO(soonhok): invariant
                    DREAL_LOG_INFO << "ode_mode_sim::compute_forward: invariant violated";
                    ret = ode_solver::ODE_result::SAT;
                    break;
                }
            }
//   else {
//                   if (m_config.nra_json) {
//                       interval const stepMade = solver.getStep();
//                       const ITaylor::CurveType& curve = solver.getCurve();
//                       interval domain = interval(0, 1) * stepMade;
//                       list<interval> intvs;
//                       intvs = split(domain, m_config.nra_ODE_grid_size);
//                       for (interval subsetOfDomain : intvs) {
//                           interval dt = prevTime + subsetOfDomain;
//                           IVector v = curve(subsetOfDomain);
//                           //  m_trajectory.emplace_back(dt, v);
//                       }
//                   }
//                   DREAL_LOG_INFO << "ode_mode_sim::compute_forward:" << prevTime; //   << "\t" << v;
//               }
            prevTime = timeMap.getCurrentTime();
        } while (!invariantViolated && !timeMap.completed());
    } catch (exception& e) {
        DREAL_LOG_ERROR << "ode_mode_sim::compute_forward: exception: " << e.what();
        ret = ode_solver::ODE_result::EXCEPTION;
    }
    //   if (m_config.nra_json) {
    //       prune_trajectory(m_T, m_X_t);
    //   }
    return ret;
}

bool ode_mode_sim::contain_NaN(DVector const & s) {
    for (double const & i : s) {
        if (std::isnan(i)) {
            DREAL_LOG_INFO << "ode_solver::contain_Nan: NaN Found! : " << s;
            return true;
        }
    }
    return false;
}

//  Take an intersection of v and inv.
//  If there is no intersection, return false.
bool ode_mode_sim::check_invariant(DVector & v, IVector const & inv) {
  IVector iv(v);
    if (!intersection(iv, inv, iv)) {
        DREAL_LOG_INFO << "ode_solver::check_invariant: invariant violated!";
        for (auto i = 0; i < v.dimension(); i++) {
            if (iv[i].leftBound() < inv[i].leftBound() || iv[i].rightBound() > inv[i].rightBound()) {
                DREAL_LOG_INFO << "ode_solver::check_invariant: inv[" << i << "] = " << inv[i];
                DREAL_LOG_INFO << "ode_solver::check_invariant:   v[" << i << "] = [" <<   iv[i].leftBound() << "," << iv[i].rightBound() << "]";
            }
        }
        return false;
    }
    return true;
}



  extern list<interval> split(interval const & i, unsigned n);


//   Run inner loop
//   return true if it violates invariant otherwise return false.
  bool ode_mode_sim::inner_loop_forward(DTaylor & solver, interval const & prevTime,
                                        vector<pair<interval, DVector>>  & bucket) {
    DREAL_LOG_DEBUG << "ode_mode_sim::inner_loop_forward " << m_T << " prevTime = " << prevTime;
    interval const stepMade = solver.getStep();
    DREAL_LOG_DEBUG << "ode_mode_sim::inner_loop_forward stepMade: " << stepMade;
    //     const DTaylor::CurveType& curve = solver.getCurve();
    interval domain = (interval(0, 1) * stepMade) + prevTime;
    DREAL_LOG_DEBUG << "ode_mode_sim::inner_loop_forward domain: " << domain;
    list<interval> intvs;
    //     int split_size = 2;//  m_config.nra_ODE_grid_size
    if (prevTime.rightBound() < m_T.leftBound()) {
        interval pre_T = interval(0, m_T.leftBound() - prevTime.rightBound());
        // domain.setLeftBound(m_T.leftBound() - prevTime.rightBound());
        // intvs = split(domain,split_size);
        intvs.push_front(domain);
        intvs.push_front(pre_T);
    } else {
      DREAL_LOG_DEBUG << "ode_mode_sim::inner_loop_forward: splitting domain into  " << m_config.nra_ODE_grid_size;
      // intvs = split(domain,split_size);
      intvs.push_front(domain);
    }

    for (interval subsetOfDomain : intvs) {
      DREAL_LOG_DEBUG << "ode_mode_sim::inner_loop_forward: " << subsetOfDomain;
        interval dt = subsetOfDomain;
        DVector v = solver((bucket.size() > 0 ? bucket.back().second: m_X_0));//
          // curve(subsetOfDomain.rightBound());
        DREAL_LOG_INFO << "ode_mode_sim::inner_loop_forward:" << dt << "\t" << v;
        if (false // !check_invariant(v, m_inv)
            ) {
            // TODO(soonhok): invariant
            return true;
        }

        if (prevTime + subsetOfDomain.rightBound() > m_T.leftBound()) {
           bucket.emplace_back(dt, v);
        }
        //   // TODO(soonhok): visualization
        //   if (m_config.nra_json) {
        //       m_trajectory.emplace_back(prevTime + subsetOfDomain, v);
        //   }
    }
    return false;
}

}
