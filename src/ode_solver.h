//solver for differential equations
#ifndef ODESOLVER_H
#define ODESOLVER_H
#include "rp_box.h"
#include "Enode.h"

#include "variable.h"

class ode_solver
{
public:
    ode_solver( set < variable* > & ode_vars );
    ~ode_solver();
    bool solve(); //computation of the next solution

private:
    set< variable* > & _ode_vars;
    ode_solver& operator=(const ode_solver& o);
};
#endif
