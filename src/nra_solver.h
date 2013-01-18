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
               vector< Enode * > &);
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
    map<Enode*, pair<double, double> >     env;
    vector <Enode*>                          stack;  // stack of asserted literals.
    vector < vector<Enode*>::size_type >     undo_stack_size;
    vector < map<Enode*, pair<double, double> > > env_stack;

};
#endif
