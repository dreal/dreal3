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
#include <exception>
#include <functional>
#include <initializer_list>
#include <memory>
#include <ratio>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "capd/capdlib.h"
#include "constraint/constraint.h"
#include "contractor/contractor_ibex.h"
#include "contractor/contractor_basic.h"
#include "contractor/contractor_capd4.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/flow.h"
#include "util/ibex_enode.h"
#include "util/interruptible_thread.h"
#include "util/logging.h"
#include "util/string.h"

using nlohmann::json;
using std::cerr;
using std::chrono::steady_clock;
using std::cout;
using std::endl;
using std::exception;
using std::fixed;
using std::function;
using std::initializer_list;
using std::left;
using std::list;
using std::logic_error;
using std::make_shared;
using std::milli;
using std::min;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::right;
using std::setprecision;
using std::setw;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {

using Rect2Set = capd::C0Rect2Set;

void split(capd::interval const & i, unsigned n, vector<capd::interval> & ret) {
    assert(i.leftBound() <= i.rightBound());
    ret.reserve(ret.size() + n);
    double lb = i.leftBound();
    double const rb = i.rightBound();
    if (lb < rb) {
        double const width = rb - lb;
        double const step = width / n;
        for (unsigned i = 0; (lb <= rb) && (i < n - 1); i++) {
            ret.emplace_back(lb, min(lb + step, rb));
            assert(lb <= min(lb + step, rb));
            lb += step;
        }
        if (lb < rb) {
            ret.emplace_back(lb, rb);
        }
    } else {
        // lb == rb
        ret.push_back(i);
    }
}

bool contain_nan(capd::IVector const & v) {
    for (capd::interval const & i : v) {
        if (std::isnan(i.leftBound()) || std::isnan(i.rightBound())) {
            DREAL_LOG_INFO << "NaN Found: " << v;
            return true;
        }
    }
    return false;
}

string subst(Enode const * const e, unordered_map<string, string> subst_map) {
    string ret;
    if (e->isSymb()) {
        if (e->isTerm() && e->getPolarity() == l_False) {
            switch (e->getId()) {
            case ENODE_ID_LEQ:
                return ">";
            case ENODE_ID_LT:
                return ">=";
            case ENODE_ID_GEQ:
                return "<";
            case ENODE_ID_GT:
                return "<=";
            }
        }
        string const & name = e->getName();
        auto it = subst_map.find(name);
        if (it == subst_map.end()) {
            return name;
        } else {
            DREAL_LOG_DEBUG << "Subst! " << name << " => " << it->second;
            return it->second;
        }
    } else if (e->isNumb()) {
        string name = e->getName();
        if (name.find('e') != string::npos || name.find('E') != string::npos) {
            // Scientific Notation
            ostringstream ss;
            double const r = stod(name);
            ss << setprecision(16) << fixed << r;
            name = ss.str();
        }
        if (starts_with(name, "-")) {
            name = "(" + name + ")";
        }
        return name;
    } else if (e->isTerm()) {
        // output "("
        if (!e->getCdr()->isEnil() && (e->isPlus() || e->isMinus() || e->isTimes() || e->isDiv() || e->isPow())) {
            ret = "(";
        }
        // !(X = Y) ==> (0 = 0)
        if (e->isEq() && e->getPolarity()  == l_False) {
            ret += "0 = 0";
        } else if (e->isPlus() || e->isMinus() || e->isTimes() || e->isDiv() || e->isEq() || e->isLeq() || e->isGeq() || e->isLt() || e->isGt()) {
            // assert(getArity() == 2);
            Enode * const op = e->getCar();
            Enode * p = e->getCdr();
            // Print 1st argument
            ret += subst(p->getCar(), subst_map);
            p = p->getCdr();
            while (!p->isEnil()) {
                // output operator
                ret += subst(op, subst_map);
                // output argument
                ret += subst(p->getCar(), subst_map);
                // move p
                p = p->getCdr();
            }
        } else if (e->isPow()) {
            Enode * const op = e->getCar();
            Enode * p = e->getCdr();
            // Print 1st argument
            ret += "(" + subst(p->getCar(), subst_map) + ")";
            p = p->getCdr();
            while (!p->isEnil()) {
                // output operator
                ret += subst(op, subst_map);
                // output argument
                ret += "(";
                ret += subst(p->getCar(), subst_map);
                ret += ")";
                // move p
                p = p->getCdr();
            }
        } else if (e->isAtan2()) {
            assert(e->getArity() == 2);
            // output operator
            ret += subst(e->getCar(), subst_map);
            ret += "(";
            // output 1st argument
            ret += subst(e->getCdr()->getCar(), subst_map);
            ret += ", ";
            // output 1st argument
            ret += subst(e->getCdr()->getCdr()->getCar(), subst_map);
            ret += ")";
        } else if (e->isTan()) {
            // CAPD does not support tan.
            // We use an identity -- tan(x) = sin(x) / cos(x)
            assert(e->getArity() == 1);
            string arg = subst(e->getCdr()->getCar(), subst_map);
            ret = "(sin(" + arg + ")/cos(" + arg + "))";
        } else if (e->isAcos() || e->isAsin() || e->isAtan() || e->isMatan() || e->isSafeSqrt() ||
                   e->isSin() || e->isCos() || e->isLog() || e->isExp() || e->isSqrt() ||
                   e->isSinh() || e->isCosh() || e->isTanh() || e->isAbs()) {
            assert(e->getArity() == 1);
            // output operator
            ret += subst(e->getCar(), subst_map);
            ret += "(";
            // output 1st argument
            ret += subst(e->getCdr()->getCar(), subst_map);
            ret += ")";
        } else {
            ret += subst(e->getCar(), subst_map);
            Enode * p = e->getCdr();
            while (!p->isEnil()) {
                ret += " ";
                // print Car
                ret += subst(p->getCar(), subst_map);
                p = p->getCdr();
            }
        }
        // output ")"
        if (!e->getCdr()->isEnil() && (e->isPlus() || e->isMinus() || e->isTimes() || e->isDiv() || e->isPow())) {
            ret += ")";
        }
    } else if (e->isList()) {
        if (e->isEnil()) {
            ret += "-";
        } else {
            ret += "[";
            ret += subst(e->getCar(), subst_map);
            Enode * p = e->getCdr();
            while (!p->isEnil()) {
                ret += ", ";
                ret += subst(p->getCar(), subst_map);
                p = p->getCdr();
            }
            ret += "]";
        }
    } else if (e->isDef()) {
        throw logic_error("unreachable");
    } else if (e->isEnil()) {
        throw logic_error("unreachable");
    } else {
        throw logic_error("unreachable");
    }
    return ret;
}

// Build CAPD string from integral constraint
// example : "var:v_2_0, x_2_0;fun:(-9.8000000000000007+(-0.450000*v_2_0)), v_2_0;"
string contractor_capd_full::build_capd_string(integral_constraint const & ic, ode_direction const dir) const {
    // Collect _0 variables
    vector<Enode *> const & pars_0 = ic.get_pars_0();
    vector<Enode *> const & par_lhs_names = ic.get_par_lhs_names();
    vector<pair<Enode *, Enode *>> const & odes = ic.get_odes();

    // Build Map
    unordered_map<string, string> subst_map;
    for (unsigned i = 0; i < m_vars_0.size(); i++) {
        string const & from = odes[i].first->getCar()->getName();
        string const & to   = m_vars_0[i]->getCar()->getName();
        subst_map.emplace(from, to);
        DREAL_LOG_INFO << "Subst Map (Var): " << from << " -> " << to;
    }
    for (unsigned i = 0; i < pars_0.size(); i++) {
        string const & from = par_lhs_names[i]->getCar()->getName();
        string const & to   = pars_0[i]->getCar()->getName();
        subst_map.emplace(from, to);
        DREAL_LOG_INFO << "Subst Map (Par): " << from << " -> " << to;
    }

    // Call Subst, and collect strings
    vector<string> ode_strs;
    ode_strs.reserve(m_vars_0.size());
    for (unsigned i = 0; i < m_vars_0.size(); i++) {
        Enode * const ode = odes[i].second;
        string ode_str = subst(ode, subst_map);
        if (dir == ode_direction::BWD) {
            ode_str = "-" + ode_str;
        }
        ode_strs.emplace_back(ode_str);
    }

    string diff_var   = "";
    string diff_par = "";
    string diff_fun   = "";
    if (m_vars_0.size() > 0) {
        vector<string> vars_0_strs;
        vars_0_strs.reserve(m_vars_0.size());
        for (auto const & var : m_vars_0) {
            vars_0_strs.emplace_back(var->getCar()->getName());
        }
        diff_var = "var:" + join(vars_0_strs, ", ") + ";";
    }
    if (pars_0.size() > 0) {
        vector<string> pars_0_strs;
        pars_0_strs.reserve(pars_0.size());
        for (auto const & par : pars_0) {
            pars_0_strs.emplace_back(par->getCar()->getName());
        }
        diff_par = "par:" + join(pars_0_strs, ", ") + ";";
    }
    if (ode_strs.size() > 0) {
        diff_fun = "fun:" + join(ode_strs, ", ") + ";";
    }
    DREAL_LOG_DEBUG << diff_var;
    DREAL_LOG_DEBUG << diff_par;
    DREAL_LOG_DEBUG << diff_fun;
    return diff_var + diff_par + diff_fun;
}

capd::IVector extract_ivector(box const & b, vector<Enode *> const & vars) {
    capd::IVector intvs(vars.size());
    for (unsigned i = 0; i < vars.size(); i++) {
        Enode * const var = vars[i];
        ibex::Interval const & intv = b[var];
        intvs[i] = capd::interval(intv.lb(), intv.ub());
    }
    return intvs;
}

void extract_ivector(box const & b, vector<Enode *> const & vars, capd::IVector & intvs) {
    for (unsigned i = 0; i < vars.size(); i++) {
        Enode * const var = vars[i];
        ibex::Interval const & intv = b[var];
        intvs[i] = capd::interval(intv.lb(), intv.ub());
    }
}

void update_box_with_ivector(box & b, vector<Enode *> const & vars, capd::IVector iv) {
    capd::IVector intvs(vars.size());
    for (unsigned i = 0; i < vars.size(); i++) {
        b[vars[i]] = ibex::Interval(iv[i].leftBound(), iv[i].rightBound());
    }
    return;
}

// Prune v using inv_ctc. box b is needed to use inv_ctc.
// Retrun false if invariant is violated.
bool contractor_capd_full::check_invariant(capd::IVector & v, box b, SMTConfig & config) {
    // 1. convert v into a box using b.
    update_box_with_ivector(b, m_vars_t, v);
    // 2. check the converted box b, with inv_ctc contractor
    m_inv_ctc.prune(b, config);
    // 3. extract v' from the pruned box b'
    //    if b' is empty, then it means invariant violation
    if (b.is_empty()) {
        return false;
    }
    extract_ivector(b, m_vars_t, v);
    return true;
}

bool contractor_capd_full::compute_enclosures(capd::interval const & prevTime,
                                              capd::interval const T,
                                              box const & b,
                                              vector<pair<capd::interval, capd::IVector>> & enclosures,
                                              SMTConfig & config,
                                              bool const add_all) {
    auto const stepMade = m_solver->getStep();
    auto const & curve = m_solver->getCurve();
    auto domain = capd::interval(0, 1) * stepMade;

    vector<capd::interval> intvs;
    if (!add_all) {
        double const new_domain_left = T.leftBound() - prevTime.rightBound();
        double const domain_right = domain.rightBound();
        if (new_domain_left > 0.0 && new_domain_left <= domain_right) {
            domain.setLeftBound(T.leftBound() - prevTime.rightBound());
        }
    }
    split(domain, m_grid_size, intvs);
    enclosures.reserve(enclosures.size() + intvs.size());
    for (capd::interval const & subsetOfDomain : intvs) {
        DREAL_LOG_INFO << "compute_enclosures: subsetOfDomain = " << subsetOfDomain;
        capd::interval const dt = prevTime + subsetOfDomain;
        if (add_all || (T.leftBound() <= dt.leftBound()) || (T.leftBound() <= dt.rightBound())) {
            //           [       T         ]
            // --------------------------------
            // 1.  [  O   ]
            // 2.         [   O   ]
            // 3.   [   O   ]
            // 4.  [  O  ]
            // 5. [  X ]
            capd::IVector v = curve(subsetOfDomain);
            DREAL_LOG_INFO << "compute_enclosures:" << dt << "\t" << v;
            if (!m_need_to_check_inv || check_invariant(v, b, config)) {
                enclosures.emplace_back(dt, v);
            } else {
                return false;
            }
        }
    }
    return true;
}

bool filter(vector<pair<capd::interval, capd::IVector>> & enclosures, capd::IVector & X_t, capd::interval & T) {
    // 1) Intersect each v in enclosure with X_t.
    DREAL_LOG_DEBUG << "filter : enclosure.size = " << enclosures.size();
    enclosures.erase(remove_if(enclosures.begin(), enclosures.end(),
                               [&X_t](pair<capd::interval, capd::IVector> & item) {
                                   capd::IVector & v = item.second;
                                   // v = v union X_t
                                   DREAL_LOG_DEBUG << "before filter: " << v << "\t" << X_t;
                                   if (!intersection(v, X_t, v)) {
                                       return true;
                                   }
                                   DREAL_LOG_DEBUG << "after filter: " << v;
                                   return false;
                               }),
                     enclosures.end());
    if (enclosures.empty()) {
        return false;
    }
    // 2) If there is no intersection in 1), set dt an empty interval [0, 0]
    capd::interval all_T = enclosures.begin()->first;
    capd::IVector all_X_t = enclosures.begin()->second;
    for (pair<capd::interval, capd::IVector> & item : enclosures) {
        capd::interval & dt = item.first;
        capd::IVector &  v  = item.second;
        all_X_t = intervalHull(all_X_t,  v);
        all_T = intervalHull(all_T, dt);
    }
    if (!intersection(T, all_T, T)) {
        return false;
    }
    if (!intersection(X_t, all_X_t, X_t)) {
        return false;
    }
    return true;
}

box intersect_params(box & b, integral_constraint const & ic) {
    vector<Enode*> const & pars_0 = ic.get_pars_0();
    vector<Enode*> const & pars_t = ic.get_pars_t();
    capd::IVector X_0 = extract_ivector(b, pars_0);
    capd::IVector const & X_t = extract_ivector(b, pars_t);
    if (!intersection(X_0, X_t, X_0)) {
        // intersection is empty
        b.set_empty();
    } else {
        // X_0 is the result of intersection of X_0 and X_t
        // So, use it to update pars_0 and pars_t
        update_box_with_ivector(b, ic.get_pars_0(), X_0);
        update_box_with_ivector(b, ic.get_pars_t(), X_0);
    }
    return b;
}

template<typename T>
void set_params(T & f, box const & b, integral_constraint const & ic) {
    vector<Enode*> const & pars_0 = ic.get_pars_0();
    capd::IVector X_0 = extract_ivector(b, pars_0);
    for (unsigned i = 0; i < pars_0.size(); i++) {
        string const & name = pars_0[i]->getCar()->getName();
        f.setParameter(name, X_0[i]);
        DREAL_LOG_DEBUG << "set_param: " << name << " ==> " << X_0[i];
    }
}

unsigned int extract_step(string const & name) {
    // We assume that the following convention holds for naming a ODE
    // variable.
    //
    //     <VAR_NAME>_<STEP>_{0,t}
    //
    // This function returns <STEP> part as an integer.
    size_t last_pos_of_underscore = name.rfind("_");
    assert(last_pos_of_underscore != string::npos);
    size_t second_to_last_pos_of_underscore = name.rfind("_", last_pos_of_underscore - 1);
    assert(second_to_last_pos_of_underscore != string::npos);
    size_t l = last_pos_of_underscore - second_to_last_pos_of_underscore - 1;
    string step_part = name.substr(second_to_last_pos_of_underscore + 1, l);
    return stoi(step_part, nullptr);
}

contractor_capd_simple::contractor_capd_simple(box const & /* box */, shared_ptr<ode_constraint> const ctr, ode_direction const dir)
    : contractor_cell(contractor_kind::CAPD_SIMPLE), m_dir(dir), m_ctr(ctr) {
    assert(m_ctr);
}

void contractor_capd_simple::prune(box &, SMTConfig &) {
    if (m_dir == ode_direction::FWD) {
        // TODO(soonhok): implement this
    } else {
        // TODO(soonhok): implement this
    }
    return;
}
// ode_solver::ODE_result ode_solver::simple_ODE_forward(IVector const & X_0, IVector & X_t, interval const & T,
//                                                       IVector const & inv, vector<IFunction> & funcs) {
//     bool prune_params_result = prune_params();
//     if (!prune_params_result) {
//         return ODE_result::UNSAT;
//     }

//     // X_t = X_t \cup (X_0 + (d/dt Inv) * T)
//     for (unsigned i = 0; i < X_0.dimension(); i++) {
//         interval const & x_0 = X_0[i];
//         interval & x_t = X_t[i];
//         IFunction & dxdt = funcs[i];
//         set_params(dxdt);
//         try {
//             interval new_x_t = x_0 + dxdt(inv) * T;
//             if (!intersection(new_x_t, x_t, x_t)) {
//                 DREAL_LOG_INFO << "ode_solver::simple_ODE_forward: no intersection for X_T => UNSAT";
//                 return ODE_result::UNSAT;
//             }
//         } catch (exception& e) {
//             DREAL_LOG_FATAL << "ode_solver::simple_ODE_forward: Exception in Simple_ODE: " << e.what();
//         }
//     }
//     // update
//     IVector_to_varlist(X_t, m_t_vars);
//     return ODE_result::SAT;
// }
ostream & contractor_capd_simple::display(ostream & out) const {
    out << "contractor_simple("
        << m_dir << ", "
        << *m_ctr << ")";
    return out;
}

contractor_capd_full::contractor_capd_full(box const & box, shared_ptr<ode_constraint> const ctr, ode_direction const dir, unsigned const taylor_order, unsigned const grid_size, double const timeout)
    : contractor_cell(contractor_kind::CAPD_FULL, box.size()), m_dir(dir), m_ctr(ctr), m_taylor_order(taylor_order), m_grid_size(grid_size), m_timeout(timeout) {
    DREAL_LOG_INFO << "contractor_capd_full::contractor_capd_full()";
    integral_constraint const & ic = m_ctr->get_ic();
    m_vars_0 = (m_dir == ode_direction::FWD) ? ic.get_vars_0() : ic.get_vars_t();
    m_vars_t = (m_dir == ode_direction::FWD) ? ic.get_vars_t() : ic.get_vars_0();
    string const capd_str = build_capd_string(ic, m_dir);

    if (capd_str.find("var:") != string::npos) {
        DREAL_LOG_INFO << "contractor_capd_full: diff sys = " << capd_str;
        m_vectorField.reset(new capd::IMap(capd_str));
        m_solver.reset(new capd::IOdeSolver(*m_vectorField, m_taylor_order));
        m_timeMap.reset(new capd::ITimeMap(*m_solver));

        // Turn on - Stop after step
        m_timeMap->stopAfterStep(true);

        // Precision
        m_solver->setAbsoluteTolerance(1e-10);
        m_solver->setRelativeTolerance(1e-10);
    } else {
        // Trivial Case with all params and no ODE variables
    }

    // Set up m_inv_ctc for invariant checking
    if (m_ctr->get_invs().size() > 0) {
        vector<contractor> inv_ctcs;
        for (forallt_constraint const & inv : m_ctr->get_invs()) {
            auto const & nl_ctrs = inv.get_nl_ctrs();
            for (auto const & nl_ctr : nl_ctrs) {
                inv_ctcs.push_back(mk_contractor_ibex_fwdbwd(nl_ctr));
            }
        }
        m_inv_ctc = mk_contractor_seq(inv_ctcs);
        m_need_to_check_inv = true;
    } else {
        m_need_to_check_inv = false;
    }

    // Input: X_0, X_T, and Time
    m_input  = ibex::BitSet::empty(box.size());
    for (Enode * e : ctr->get_ic().get_enode()->get_vars()) {
        m_input.add(box.get_index(e));
    }
    // Output: Empty
    m_output = ibex::BitSet::empty(box.size());
    m_used_constraints.insert(m_ctr);
}

void contractor_capd_full::prune(box & b, SMTConfig & config) {
    auto const start_time = steady_clock::now();
    thread_local static box old_box(b);
    old_box = b;
    DREAL_LOG_DEBUG << "contractor_capd_full::prune "
                    << m_dir;
    integral_constraint const & ic = m_ctr->get_ic();
    b = intersect_params(b, ic);
    if (b.is_empty()) {
        m_output  = ibex::BitSet::all(b.size());
        return;
    }
    m_output  = ibex::BitSet::empty(b.size());
    if (!m_solver) {
        // Trivial Case where there are only params and no real ODE vars.
        return;
    }
    set_params(*m_vectorField, b, ic);

    try {
        if (config.nra_ODE_step > 0) {
            m_solver->setStep(config.nra_ODE_step);
        }
        capd::IVector X_0 = extract_ivector(b, m_vars_0);
        capd::IVector X_t = extract_ivector(b, m_vars_t);
        ibex::Interval const & ibex_T = b[ic.get_time_t()];
        capd::interval T(ibex_T.lb(), ibex_T.ub());
        DREAL_LOG_INFO << "X_0 : " << X_0;
        DREAL_LOG_INFO << "X_t : " << X_t;
        DREAL_LOG_INFO << "T   : " << T;
        Rect2Set s(X_0);
        (*m_timeMap)(0.0, s);  // Rewind to 0.0
        capd::interval prevTime(0.);
        vector<pair<capd::interval, capd::IVector>> enclosures;
        do {
            // Handle Timeout
            if (m_timeout > 0.0 && b.max_diam() > config.nra_precision) {
                auto const end_time = steady_clock::now();
                auto const time_diff_in_msec = std::chrono::duration<double, milli>(end_time - start_time).count();
                DREAL_LOG_INFO << "ODE TIME: " << time_diff_in_msec << " / " << m_timeout;
                if (time_diff_in_msec > m_timeout) {
                    DREAL_LOG_FATAL << "ODE TIMEOUT!" << "\t"
                                    << time_diff_in_msec << "msec / "
                                    << m_timeout << "msec";
                    throw contractor_exception("ODE TIMEOUT");
                }
            }
            // Invariant Check
            if (m_need_to_check_inv && !check_invariant(s, b, config)) {
                break;
            }
            // Move s toward m_T.rightBound()
            interruption_point();
            (*m_timeMap)(T.rightBound(), s);
            if (contain_nan(s)) {
                DREAL_LOG_FATAL << "contractor_capd_full::prune - contains NaN";
            }
            if (T.leftBound() <= m_timeMap->getCurrentTime().rightBound()) {
                //                     [     T      ]
                // [     current Time     ]
                bool invariantSatisfied = compute_enclosures(prevTime, T,  b, enclosures, config);
                if (!invariantSatisfied) {
                    DREAL_LOG_INFO << "contractor_capd_full::prune - invariant violated";
                    break;
                }
            }
            prevTime = m_timeMap->getCurrentTime();
            if (config.nra_ODE_show_progress) {
                cout << "\r"
                     << "                                               "
                     << "                                               ";
                cout << "\r"
                     << "ODE Progress "
                     << "[" << m_dir << "]"
                     << ":  Time = " << setw(10) << fixed << setprecision(5) << right << prevTime.rightBound() << " / "
                     << setw(7) << fixed << setprecision(2) << left << T.rightBound() << " "
                     << setw(4) << right << int(prevTime.rightBound() / T.rightBound() * 100.0) << "%" << "  "
                     << "Box Width = " << setw(10) << fixed << setprecision(5) << b.max_diam() << "\t";
                cout.flush();
            }
        } while (!m_timeMap->completed());
        if (config.nra_ODE_show_progress) {
            cout << " [Done] " << endl;
        }
        if (enclosures.size() > 0 && filter(enclosures, X_t, T)) {
            // SAT
            update_box_with_ivector(b, m_vars_t, X_t);
            // TODO(soonhok): Here we still assume that time_0 = zero.
            b[ic.get_time_t()] = ibex::Interval(T.leftBound(), T.rightBound());
            DREAL_LOG_DEBUG << "contractor_capd_full::prune: get non-empty set after filtering";
        } else {
            // UNSAT
            DREAL_LOG_DEBUG << "contractor_capd_full::prune: get empty set after filtering";
            b.set_empty();
        }
    } catch (capd::intervals::IntervalError<double> & e) {
        if (config.nra_ODE_show_progress) {
            cout << " [IntervalError]" << endl;
        }
        throw contractor_exception(e.what());
    } catch (capd::ISolverException & e) {
        if (config.nra_ODE_show_progress) {
            cout << " [ISolverException]" << endl;
        }
        throw contractor_exception(e.what());
    }
    vector<bool> diff_dims = b.diff_dims(old_box);
    for (unsigned i = 0; i < diff_dims.size(); i++) {
        if (diff_dims[i]) {
            m_output.add(i);
        }
    }
    return;
}

json generate_trace_core(integral_constraint const & ic,
                         vector<Enode *> const & vars_0,
                         vector<Enode *> const & pars_0,
                         box const & b,
                         capd::interval const & T,
                         vector<pair<capd::interval, capd::IVector>> const & enclosures) {
    unsigned i = 0;
    json ret = {};
    for (auto const & var : vars_0) {
        json entry;
        string const name = var->getCar()->getName();
        entry["key"] = name;
        entry["mode"] = ic.get_flow_id();
        entry["step"] = extract_step(name);
        entry["values"] = {};
        for (auto const & p : enclosures) {
            json value;
            value["time"] = {p.first.leftBound(), p.first.rightBound()};
            value["enclosure"] = {p.second[i].leftBound(), p.second[i].rightBound()};
            entry["values"].push_back(value);
        }
        ret.push_back(entry);
        i++;
    }
    for (auto const & var : pars_0) {
        json entry;
        string const name = var->getCar()->getName();
        entry["key"] = name;
        entry["mode"] = ic.get_flow_id();
        entry["step"] = extract_step(name);
        entry["values"] = {};
        json value_begin, value_end;
        value_begin["time"] = {0.0, 0.0};
        value_begin["enclosure"] = {b[var].lb(), b[var].ub()};
        entry["values"].push_back(value_begin);
        value_end["time"] = {T.leftBound(), T.rightBound()};
        value_end["enclosure"] = {b[var].lb(), b[var].ub()};
        entry["values"].push_back(value_end);
        ret.push_back(entry);
    }
    return ret;
}

json contractor_capd_full::generate_trace(box b, SMTConfig & config) {
    integral_constraint const & ic = m_ctr->get_ic();
    b = intersect_params(b, ic);
    if (!m_solver) {
        // Trivial Case where there are only params and no real ODE vars.
        return {};
    }
    set_params(*m_vectorField, b, ic);
    try {
        if (config.nra_ODE_step > 0) {
            m_solver->setStep(config.nra_ODE_step);
        }
        vector<Enode *> const & vars_0 = (m_dir == ode_direction::FWD) ? ic.get_vars_0() : ic.get_vars_t();
        vector<Enode *> const & vars_t = (m_dir == ode_direction::FWD) ? ic.get_vars_t() : ic.get_vars_0();
        vector<Enode *> const & pars_0 = (m_dir == ode_direction::FWD) ? ic.get_pars_0() : ic.get_pars_t();
        capd::IVector X_0 = extract_ivector(b, vars_0);
        capd::IVector X_t = extract_ivector(b, vars_t);
        ibex::Interval const & ibex_T = b[ic.get_time_t()];
        capd::interval T(ibex_T.lb(), ibex_T.ub());
        Rect2Set s(X_0);
        (*m_timeMap)(0.0, s);  // Rewind to 0.0
        m_timeMap->stopAfterStep(true);
        capd::interval prevTime(0.0);
        // Convert enclosures to json
        vector<pair<capd::interval, capd::IVector>> enclosures;
        do {
            // Move s toward m_T.rightBound()
            (*m_timeMap)(T.rightBound(), s);
            if (contain_nan(s)) {
                DREAL_LOG_INFO << "contractor_capd_full::generate_trace - contain NaN";
            }
            bool invariantSatisfied = compute_enclosures(prevTime, T, b, enclosures, config, true);
            if (!invariantSatisfied) {
                DREAL_LOG_INFO << "contractor_capd_full::generate_trace - invariant violated";
                break;
            }
            prevTime = m_timeMap->getCurrentTime();
        } while (!m_timeMap->completed());
        return generate_trace_core(ic, vars_0, pars_0, b, T, enclosures);
    } catch (capd::intervals::IntervalError<double> & e) {
        throw contractor_exception(e.what());
    } catch (capd::ISolverException & e) {
        throw contractor_exception(e.what());
    } catch (exception & e) {
        throw contractor_exception(e.what());
    }
}

ostream & contractor_capd_full::display(ostream & out) const {
    out << "contractor_capd_full("
        << m_dir << ", "
        << *m_ctr << ")";
    return out;
}

contractor mk_contractor_capd_simple(box const & box, shared_ptr<ode_constraint> const ctr, ode_direction const dir) {
    return contractor(make_shared<contractor_capd_simple>(box, ctr, dir));
}

contractor mk_contractor_capd_full(box const & box, shared_ptr<ode_constraint> const ctr, ode_direction const dir, unsigned const taylor_order, unsigned const grid_size, bool const use_cache, double const timeout) {
    if (!use_cache) {
        return contractor(make_shared<contractor_capd_full>(box, ctr, dir, taylor_order, grid_size, timeout));
    }
    if (dir == ode_direction::FWD) {
        static unordered_map<shared_ptr<ode_constraint>, contractor> capd_full_fwd_ctc_cache;
        auto it = capd_full_fwd_ctc_cache.find(ctr);
        if (it == capd_full_fwd_ctc_cache.end()) {
            contractor ctc(make_shared<contractor_capd_full>(box, ctr, dir, taylor_order, grid_size, timeout));
            capd_full_fwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    } else {
        static unordered_map<shared_ptr<ode_constraint>, contractor> capd_full_bwd_ctc_cache;
        auto it = capd_full_bwd_ctc_cache.find(ctr);
        if (it == capd_full_bwd_ctc_cache.end()) {
            contractor ctc(make_shared<contractor_capd_full>(box, ctr, dir, taylor_order, grid_size, timeout));
            capd_full_bwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    }
}
}  // namespace dreal
