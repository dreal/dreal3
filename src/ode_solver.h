//solver for differential equations
#ifndef ODESOLVER_H
#define ODESOLVER_H
#include "rp_box.h"
#include "Enode.h"

#include "variable.h"

class ode_solver
{
public:
    ode_solver(set < string > & odes,
               set < variable* > & ode_vars
        );
    ~ode_solver();
    bool solve(rp_box box); //computation of the next solution

private:
    set< string > & _odes;
    set< variable* > & _ode_vars;
    ode_solver& operator=(const ode_solver& o);
};

#endif
