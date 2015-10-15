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
#include <cfenv>
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
#include "constraint/constraint.h"
#include "contractor/contractor_gsl.h"
#include "gsl/gsl_errno.h"
#include "gsl/gsl_matrix.h"
#include "gsl/gsl_odeiv2.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/flow.h"
#include "util/ibex_enode.h"
#include "util/logging.h"
#include "util/string.h"

using nlohmann::json;
using std::chrono::steady_clock;
using std::cerr;
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
using std::max;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::right;
using std::runtime_error;
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

static double eval(Enode * const e, double const values[], double const params[],
                   unordered_map<Enode *, unsigned> const & value_lookup,
                   unordered_map<Enode *, unsigned> const & param_lookup) {
    if (e->isNumb()) {
        return e->getNumb();
    } else if (e->isVar()) {
        auto it = value_lookup.find(e);
        if (it != value_lookup.end()) {
            return values[it->second];
        }
        it = param_lookup.find(e);
        if (it != param_lookup.end()) {
            return params[it->second];
        }
        DREAL_LOG_FATAL << "Can't find variable " << e;
        throw runtime_error("GSL eval: unmatched variable");
    } else if (e->isTerm()) {
        switch (e->getCar()->getId()) {
        case ENODE_ID_PLUS: {
            Enode * p = e->getCdr();
            double ret = eval(p->getCar(), values, params, value_lookup, param_lookup);
            p = p->getCdr();
            while (!p->isEnil()) {
                ret += eval(p->getCar(), values, params, value_lookup, param_lookup);
                p = p->getCdr();
            }
            return ret;
        }
        case ENODE_ID_MINUS: {
            Enode * p = e->getCdr();
            double ret = eval(p->getCar(), values, params, value_lookup, param_lookup);
            p = p->getCdr();
            while (!p->isEnil()) {
                ret -= eval(p->getCar(), values, params, value_lookup, param_lookup);
                p = p->getCdr();
            }
            return ret;
        }
        case ENODE_ID_TIMES: {
            Enode * p = e->getCdr();
            double ret = eval(p->getCar(), values, params, value_lookup, param_lookup);
            p = p->getCdr();
            while (!p->isEnil()) {
                ret *= eval(p->getCar(), values, params, value_lookup, param_lookup);
                p = p->getCdr();
            }
            return ret;
        }
        case ENODE_ID_DIV: {
            Enode * p = e->getCdr();
            double ret = eval(p->getCar(), values, params, value_lookup, param_lookup);
            p = p->getCdr();
            while (!p->isEnil()) {
                ret /= eval(p->getCar(), values, params, value_lookup, param_lookup);
                p = p->getCdr();
            }
            return ret;
        }
        case ENODE_ID_POW: {
            if (e->getArity() != 2) {
                throw runtime_error("GSL eval: pow not implemented");
            }
            double const arg1 = eval(e->get1st(), values, params, value_lookup, param_lookup);
            double const arg2 = eval(e->get2nd(), values, params, value_lookup, param_lookup);
            return pow(arg1, arg2);
        }
        case ENODE_ID_ATAN2: {
            double const arg1 = eval(e->get1st(), values, params, value_lookup, param_lookup);
            double const arg2 = eval(e->get2nd(), values, params, value_lookup, param_lookup);
            return atan2(arg1, arg2);
        }
        case ENODE_ID_UMINUS: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return -arg;
        }
        case ENODE_ID_SIN: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return sin(arg);
        }
        case ENODE_ID_COS: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return cos(arg);
        }
        case ENODE_ID_TAN: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return tan(arg);
        }
        case ENODE_ID_SQRT: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return sqrt(arg);
        }
        case ENODE_ID_SAFESQRT: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            assert(arg >= 0);
            return sqrt(arg);
        }
        case ENODE_ID_EXP: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return exp(arg);
        }
        case ENODE_ID_LOG: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return log(arg);
        }
        case ENODE_ID_ASIN: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return asin(arg);
        }
        case ENODE_ID_ACOS: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return acos(arg);
        }
        case ENODE_ID_ATAN: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return atan(arg);
        }
        case ENODE_ID_SINH: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return sinh(arg);
        }
        case ENODE_ID_COSH: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return cosh(arg);
        }
        case ENODE_ID_TANH: {
            assert(e->getArity() == 1);
            double const arg = eval(e->get1st(), values, params, value_lookup, param_lookup);
            return tanh(arg);
        }
        default:
            return eval(e->getCar(), values, params, value_lookup, param_lookup);
        }
    } else if (e->isList()) {
        throw runtime_error("GSL eval: list");
    } else if (e->isDef()) {
        throw runtime_error("GSL eval: def");
    } else if (e->isEnil()) {
        throw runtime_error("GSL eval: enil");
    }
    throw runtime_error("GSL eval: unknown");
}

void extract_sample_point(box const & b, vector<Enode *> const & vars, double values[]) {
    for (unsigned i = 0; i < vars.size(); i++) {
        Enode * const var = vars[i];
        ibex::Interval const & intv = b[var];
        values[i] = intv.mid();
    }
}

void print_values(double const t, double const values[], unsigned const sz) {
    printf("GSL -- Time = %.20g\t", t);
    for (unsigned i = 0; i < sz; i++) {
        printf("v[%d] = %.20g  ", i, values[i]);
    }
    printf("\n");
}

int contractor_gsl::rhs(double , const double[], double f[], void *params_ptr) {
    contractor_gsl * ctc_ptr = reinterpret_cast<contractor_gsl*>(params_ptr);
    /* evaluate the right-hand-side functions at t */
    for (unsigned i = 0; i < ctc_ptr->m_dim; i++) {
        f[i] = eval(ctc_ptr->m_odes[i].second, ctc_ptr->m_values, ctc_ptr->m_params,
                    ctc_ptr->m_value_lookup, ctc_ptr->m_param_lookup);
    }
    return GSL_SUCCESS;        /* GSL_SUCCESS defined in gsl/errno.h as 0 */
}

contractor_gsl::contractor_gsl(box const & box, shared_ptr<ode_constraint> const ctr, contractor const & eval_ctc, bool const forward, double const timeout)
    : contractor_cell(contractor_kind::GSL, box.size()), m_forward(forward),
      m_ctr(ctr), m_eval_ctc(eval_ctc), m_timeout(timeout),
      m_ic(m_ctr->get_ic()), m_vars_0(m_ic.get_vars_0()), m_pars_0(m_ic.get_pars_0()),
      m_vars_t(m_ic.get_vars_t()), m_time_t(m_ic.get_time_t()),
      m_par_lhs_names(m_ic.get_par_lhs_names()), m_odes(m_ic.get_odes()),
      m_dim(m_ic.get_vars_0().size()), m_system({rhs, nullptr, m_dim, this}) {
        // Build Map
    for (unsigned i = 0; i < m_vars_0.size(); i++) {
        Enode * from = m_odes[i].first;
        m_value_lookup.emplace(from, i);
    }
    for (unsigned i = 0; i < m_pars_0.size(); i++) {
        Enode * from = m_par_lhs_names[i];
        m_param_lookup.emplace(from, i);
    }

    double const eps_abs = 1e-10;       /* absolute error requested */
    double const eps_rel = 1e-10;       /* relative error requested */

    const gsl_odeiv2_step_type * T = gsl_odeiv2_step_rk8pd;
    m_step = gsl_odeiv2_step_alloc(T, m_dim);
    m_control = gsl_odeiv2_control_y_new(eps_abs, eps_rel);
    m_evolve = gsl_odeiv2_evolve_alloc(m_dim);

    m_old_values = new double[m_dim];
    m_values = new double[m_dim];
    m_params = new double[m_pars_0.size()];

    // Input: X_0, X_T, and Time
    m_input  = ibex::BitSet::empty(box.size());
    for (Enode * e : m_ic.get_enode()->get_vars()) {
        m_input.add(box.get_index(e));
    }
    // Output: Empty
    m_output = ibex::BitSet::empty(box.size());
    m_used_constraints.insert(m_ctr);
}

void contractor_gsl::prune(box & b, SMTConfig & config) const {
    // TODO(soonhok): add timeout
    fesetround(FE_TONEAREST);  // Without this, GSL might cause a segmentation fault due to problems in floating point lib
    gsl_odeiv2_step_reset(m_step);
    gsl_odeiv2_evolve_reset(m_evolve);

    double const T_lb = b[m_time_t].lb();
    double const T_ub = b[m_time_t].ub();
    double t = 0.0, old_t = 0.0;                  /* initialize t */
    double T_next = 0.0;
    double h = 1e-10;              /* starting step size for ode solver */
    DREAL_LOG_INFO << "GSL: prune begin "
                   << m_time_t << " = ["
                   << T_lb << ", " << T_ub << "]"
                   << "\t" << b.max_diam();
    DREAL_LOG_INFO << m_ctr->get_ic();

    if (b.max_diam() < config.nra_precision) {
        return;
    }
    bool need_to_run = false;
    for (Enode * e : m_vars_0) {
        if (b[e].diam() > config.nra_precision) {
            need_to_run = true;
            break;
        }
    }
    if (b[m_time_t].diam() > config.nra_precision) {
        need_to_run = true;
    }
    if (!need_to_run) { return; }

    extract_sample_point(b, m_vars_0, m_values);
    extract_sample_point(b, m_pars_0, m_params);
    for (unsigned i = 0; i < m_vars_0.size(); i++) {
        b[m_vars_0[i]] = m_values[i];
    }
    for (unsigned i = 0; i < m_pars_0.size(); i++) {
        b[m_pars_0[i]] = m_params[i];
    }

    // First move to T_lb without checking m_values
    while (t < T_lb) {
        T_next = T_lb;
        // T_next = min(t + config.nra_precision, T_lb);
        int status = gsl_odeiv2_evolve_apply(m_evolve, m_control, m_step,
                                             &m_system,
                                             &t, T_next,
                                             &h, m_values);
        if (status != GSL_SUCCESS) {
            DREAL_LOG_INFO << "GSL: error, return value " << status;
            throw contractor_exception("GSL FAILED");
        }
    }

    // Now we're in the range in [T_lb, T_ub], need to check m_values.
    while (t < T_ub) {
        T_next = min(t + config.nra_precision, T_ub);
        // T_next = T_ub;

        // Copy m_values to m_old_values, and t to old_t
        for (unsigned i = 0; i < m_dim; i++) {
            m_old_values[i] = m_values[i];
        }
        old_t = t;

        int status = gsl_odeiv2_evolve_apply(m_evolve, m_control, m_step,
                                             &m_system,
                                             &t, T_next,
                                             &h, m_values);
        if (status != GSL_SUCCESS) {
            DREAL_LOG_INFO << "GSL: error, return value " << status;
            throw contractor_exception("GSL FAILED");
        }

        // print_values(t, m_values, m_dim);         /* print at t */
        bool values_good = true;
        unsigned i = 0;
        for (Enode * e : m_vars_t) {
            double const old_v_i = m_old_values[i];
            double const v_i = m_values[i];
            auto iv = (old_v_i < v_i) ? ibex::Interval(old_v_i, v_i) : ibex::Interval(v_i, old_v_i);
            auto const & iv_X_t = b[e];
            iv &= iv_X_t;
            if (iv.is_empty()) {
                values_good = false;
                DREAL_LOG_INFO << "GSL Not in Range: " << e
                                << " : " << m_values[i] << " not in " << b[e] << " at t = " << t;
                break;
            }
            i++;
        }
        if (values_good) {
            static box old_box(b);
            old_box = b;
            // Update X_t with m_values
            i = 0;
            for (Enode * e : m_vars_t) {
                double const old_v_i = m_old_values[i];
                double const v_i = m_values[i];
                auto iv = (old_v_i < v_i) ? ibex::Interval(old_v_i, v_i) : ibex::Interval(v_i, old_v_i);
                auto const & iv_X_t = b[e];
                iv &= iv_X_t;
                DREAL_LOG_INFO << "GSL Update: " << e
                                << " : " << b[e] << " ==> " << iv;
                b[e] = iv;
                i++;
            }
            // Update Time with T
            double const new_t = t/2.0 + old_t/2.0;
            DREAL_LOG_INFO << "GSL Update: time: " << b[m_time_t] << " ==> " << new_t;
            b[m_time_t] = new_t;
            m_eval_ctc.prune(b, config);
            if (!b.is_empty()) {
                DREAL_LOG_INFO << "This box satisfies other non-linear constraints";
                return;
            } else {
                DREAL_LOG_INFO << "This box failed to satisfy other non-linear constraints";
                b = old_box;
            }
        }
    }
    DREAL_LOG_INFO << "GSL failed in the end";
    throw contractor_exception("GSL failed");
}

ostream & contractor_gsl::display(ostream & out) const {
    out << "contractor_gsl("
        << (m_forward ? "fwd" : "bwd") << ", "
        << *m_ctr << ")";
    return out;
}

contractor mk_contractor_gsl(box const & box, shared_ptr<ode_constraint> const ctr, contractor const & eval_ctc, bool const forward, double const timeout) {
    if (forward) {
        static unordered_map<shared_ptr<ode_constraint>, contractor> gsl_fwd_ctc_cache;
        auto it = gsl_fwd_ctc_cache.find(ctr);
        if (it == gsl_fwd_ctc_cache.end()) {
            contractor ctc(make_shared<contractor_gsl>(box, ctr, eval_ctc, forward, timeout));
            gsl_fwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    } else {
        static unordered_map<shared_ptr<ode_constraint>, contractor> gsl_bwd_ctc_cache;
        auto it = gsl_bwd_ctc_cache.find(ctr);
        if (it == gsl_bwd_ctc_cache.end()) {
            contractor ctc(make_shared<contractor_gsl>(box, ctr, eval_ctc, forward, timeout));
            gsl_bwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    }
}
}  // namespace dreal
