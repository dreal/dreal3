/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <fstream>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "dsolvers/ode_solver.h"
#include "dsolvers/util/scoped_env.h"
#include "dsolvers/util/scoped_vec.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "realpaver/realpaver.h"

class icp_solver {
public:
    icp_solver(SMTConfig & c, scoped_vec const & stack, scoped_env & env,
               std::vector<Enode *> & exp, std::unordered_map<Enode *, std::unordered_set<Enode *>> & vars_in_lit,
               bool complete_check);
    ~icp_solver();
    bool prop(); // only propagate
    bool solve();
    void print_json(ostream& out);

private:
    // methods
    icp_solver(const icp_solver& s);
    icp_solver& operator=(const icp_solver& s);

    rp_problem* create_rp_problem();
    void        create_ode_solvers();

    rp_box      compute_next(); // computation of the next solution
    bool        prop_with_ODE(); // propagate with ODE (only in complete check)
    bool        callODESolver(int group, std::unordered_set<Enode *> const & ode_vars, bool forward);

    bool        is_atomic(std::unordered_set<Enode *> const & ode_vars, double const p);
    std::vector<pair<double, double>> measure_size(std::unordered_set<Enode *> const & ode_vars, double const p);

    void        output_problem() const;
    void        print_ODE_trajectory(ostream& out) const;
    void        display_box(ostream& out, rp_box b, int digits, int mode) const;
    void        display_interval(ostream & out, rp_interval i, int digits, int mode) const;
    void        pprint_vars(ostream & out, rp_problem p, rp_box b) const;

    // =================================================================================
    //   fields
    // =================================================================================
    SMTConfig &                    m_config;
    rp_problem *                   m_problem; /* problem to be solved */
    rp_propagator *                m_propag; /* reduction algorithm using propagation */
    rp_box_stack                   m_boxes; /* the set of boxes during search */
    rp_selector *                  m_vselect; /* selection of variable to be split */
    rp_splitter *                  m_dsplit; /* split function of variable domain */
    rp_existence_prover *          m_ep; /* existence prover */
    int                            m_sol; /* number of computed solutions */
    int                            m_nsplit; /* number of split steps */
    double                         m_improve; /* improvement factor of iterative methods */

    vector<Enode *> &              m_explanation;
    vector<rp_variable *>          m_rp_variables;
    vector<rp_constraint *>        m_rp_constraints;
    scoped_vec const &             m_stack;
    scoped_env &                   m_env;
    bool                           m_ODEresult;

    unsigned                       m_num_ode_sgroups;
    std::unordered_set<unsigned>                  m_ode_worklist;
    std::unordered_map<Enode *, std::unordered_set<Enode *>> &   m_odevars_in_lit;
    std::unordered_map<Enode *, int>              m_enode_to_rp_id;
    std::unordered_map<int, Enode *>              m_rp_id_to_enode;
    std::vector<std::unordered_set<Enode *>> m_diff_vec;        // ODE_Group -> set of ODE variables
    std::vector<ode_solver *>      m_ode_solvers;
    bool                           m_complete_check;
};
