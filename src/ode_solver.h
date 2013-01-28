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
#include "variable.h"

class ode_solver
{
public:
    ode_solver( set < variable* > & ode_vars );
    ~ode_solver();

    string create_diffsys_string(set < variable* > & ode_vars,
                                 vector<variable*> & _0_vars,
                                 vector<variable*> & _t_vars);

    capd::IVector varlist_to_IVector(vector<variable*> vars);
    void IVector_to_varlist(capd::IVector & v, vector<variable*> & vars);
    void prune(vector<variable*>& _t_vars,
               capd::IVector v,
               capd::intervals::Interval<double, capd::rounding::DoubleRounding> time,
               vector<capd::IVector> & out_v_list,
               vector<capd::intervals::Interval<double, capd::rounding::DoubleRounding> > & out_time_list
        );

    bool solve(); //computation of the next solution

private:
    set< variable* > & _ode_vars;
    ode_solver& operator=(const ode_solver& o);
};
#endif
