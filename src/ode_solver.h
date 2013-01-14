//solver for differential equations
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
