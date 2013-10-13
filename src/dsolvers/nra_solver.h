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

#ifndef NRA_SOLVER_H
#define NRA_SOLVER_H
#include <utility>
#include "TSolver.h"
#include "Egraph.h"
#include "dsolvers/util/scoped_map.h"

class NRASolver : public OrdinaryTSolver {
public:
    NRASolver(const int, const char *, SMTConfig &, Egraph &, SStore &, vector<Enode *> &,
              vector<Enode *> &, vector<Enode *> &);
    ~NRASolver();
    lbool inform(Enode *e);
    bool assertLit(Enode *e, bool = false);
    void pushBacktrackPoint ();
    void popBacktrackPoint ();
    bool check(bool c);
    bool belongsToT(Enode *e);
    void computeModel();

private:
    set<Enode *> get_variables(Enode *e);
    scoped_map<Enode*, std::pair<double, double>> env;
    vector <Enode*> stack; // stack of asserted literals.
    vector <unsigned> undo_stack_size;
    map <Enode*, set <Enode*>> _enode_to_vars;
};
#endif
