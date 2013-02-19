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

#include "TSolver.h"
#include "Egraph.h"

using std::map;
using std::pair;

class NRASolver : public OrdinaryTSolver
{
public:

    NRASolver( const int,
               const char *,
               SMTConfig &,
               Egraph &,
               SStore &,
               vector< Enode * > &,
               vector< Enode * > &,
               vector< Enode * > &,
               bool
        );
    ~NRASolver ( );

    lbool  	    inform              	( Enode * );
    bool            assertLit           	( Enode *, bool = false );
    void            pushBacktrackPoint  	( );
    void            popBacktrackPoint   	( );
    bool            check               	( bool );
    bool            belongsToT          	( Enode * );
    void            computeModel        	( );

    set<Enode *>    get_variables (Enode * e );

private:
    map<Enode*, pair<double, double> >            env;
    vector <Enode*>                               stack;  // stack of asserted literals.
    vector < vector<Enode*>::size_type >          undo_stack_size;
    vector < map<Enode*, pair<double, double> > > env_stack;
    double                                        precision;
    bool                                          contain_ode;
    map < Enode*, set < Enode* > > _enode_to_vars;
};
#endif
