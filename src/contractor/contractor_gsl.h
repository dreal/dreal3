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

#pragma once
#include <initializer_list>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include "contractor/contractor_common.h"
#include "gsl/gsl_errno.h"
#include "gsl/gsl_matrix.h"
#include "gsl/gsl_odeiv2.h"
#include "json/json.hpp"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"

namespace dreal {
class contractor_gsl : public contractor_cell {
private:
    bool const m_forward;
    std::shared_ptr<ode_constraint> const m_ctr;
    contractor m_eval_ctc;
    double const m_timeout;  // unit: msec

    // ODE related member variables
    integral_constraint const & m_ic;
    std::vector<Enode *> const & m_vars_0;
    std::vector<Enode *> const & m_pars_0;
    std::vector<Enode *> const & m_vars_t;
    Enode * const m_time_t;
    std::vector<Enode *> const & m_par_lhs_names;
    std::vector<std::pair<Enode *, Enode *>> const & m_odes;
    unsigned m_dim;       // dimension

    // GSL-specific member variables
    gsl_odeiv2_system m_system;
    gsl_odeiv2_step * m_step;
    gsl_odeiv2_control * m_control;
    gsl_odeiv2_evolve * m_evolve;
    double * m_old_values;    // solution vector
    double * m_values;    // solution vector
    double * m_params;    // param    vector
    std::unordered_map<std::string, std::string> m_subst_map;
    std::unordered_map<Enode *, unsigned> m_value_lookup;   //  x |-> index
    std::unordered_map<Enode *, unsigned> m_param_lookup;   //  p |-> index

    // GSL-specific member function
    static int rhs(double t, const double y[], double f[], void *params_ptr);
    // static int jacobian (double t, const double y[], double *dfdy, double dfdt[], void *params_ptr);

public:
    contractor_gsl(box const & box, std::shared_ptr<ode_constraint> const ctr, contractor const & eval_ctc, bool const forward, double const timeout = 0.0);
    ~contractor_gsl() {
        delete[] m_old_values;
        delete[] m_values;
        delete[] m_params;
        gsl_odeiv2_evolve_free(m_evolve);
        gsl_odeiv2_control_free(m_control);
        gsl_odeiv2_step_free(m_step);
    }
    void prune(box & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

contractor mk_contractor_gsl(box const & box, std::shared_ptr<ode_constraint> const ctr, contractor const & eval_ctc, bool const forward, double const timeout = 0.0);
}  // namespace dreal
