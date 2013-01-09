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
    ode_solver();
    ~ode_solver();
    bool solve(rp_box box); //computation of the next solution

private:
    ode_solver& operator=(const ode_solver& o);
};

#endif
