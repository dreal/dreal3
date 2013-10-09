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

#ifndef ODESOLVER_H
#define ODESOLVER_H
#include "rp_box.h"
#include "Enode.h"
#include "capd/capdlib.h"
#include "SMTConfig.h"

class ode_solver
{
public:
    ode_solver(int group,
               SMTConfig& c,
               set < Enode* > & ode_vars,
               rp_box b,
               std::map<Enode*, int>& enode_to_rp_id,
               bool& ODEresult
        );
    ~ode_solver();

    string create_diffsys_string(set < Enode* > & ode_vars,
                                 vector<Enode*> & _0_vars,
                                 vector<Enode*> & _t_vars);

    capd::IVector varlist_to_IVector(vector<Enode*> vars);
    capd::IVector extract_invariants(vector<Enode*> vars);
    void IVector_to_varlist(capd::IVector & v, vector<Enode*> & vars);

    void prune(vector<Enode*>& _t_vars,
               capd::IVector v,
               capd::interval dt,
               vector<capd::IVector> & out_v_list,
               vector<capd::interval> & out_time_list,
               capd::interval time);

    bool simple_ODE();
    bool solve_forward();
    bool solve_backward();

    double get_lb(Enode* const e) const {
        return rp_binf(rp_box_elem(_b, _enode_to_rp_id[e]));
    }
    double get_ub(Enode* const e) const {
        return rp_bsup(rp_box_elem(_b, _enode_to_rp_id[e]));
    }
    void set_lb(Enode* const e, const double v) {
        rp_binf(rp_box_elem(_b, _enode_to_rp_id[e])) = v;
    }
    void set_ub(Enode* const e, const double v) {
        rp_bsup(rp_box_elem(_b, _enode_to_rp_id[e])) = v;
    }
    void set_empty_interval(Enode* const e) {
        rp_interval_set_empty(rp_box_elem(_b, _enode_to_rp_id[e]));
    }

    void print_trajectory(ostream& out) const;

private:
    int _group;
    SMTConfig& _config;
    set< Enode* > & _ode_vars;
    rp_box _b;
    map<Enode*, int>& _enode_to_rp_id;
    ode_solver& operator=(const ode_solver& o);
    list<pair<capd::interval, capd::IVector> > trajectory;
    bool& ODEresult;
    vector<string> var_list;

    double stepControl;

    void print_datapoint(ostream& out, const capd::interval& t, const capd::interval& v) const;

    void print_trace(ostream& out,
                     const string key,
                     const int idx,
                     const list<pair<capd::interval, capd::IVector> > & trajectory) const;

    void prune_trajectory(capd::interval& t, capd::IVector& e);
};
#endif
