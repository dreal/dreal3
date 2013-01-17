#ifndef NRA_SOLVER_H
#define NRA_SOLVER_H

#include "TSolver.h"
#include "Egraph.h"
#include "icp_solver.h"
#include "variable.h"

class NRASolver : public OrdinaryTSolver
{
public:

    NRASolver( const int, const char *, SMTConfig &, Egraph &, SStore &
               , vector< Enode * > &
               , vector< Enode * > &
               , vector< Enode * > &);

    ~NRASolver ( );

    bool            icp_solve		        ( set<variable*> );
    bool            icp_prop                    ( set<variable*> );

    lbool  	    inform              	( Enode * );
    bool            assertLit           	( Enode *, bool = false );
    void            pushBacktrackPoint  	( );
    void            popBacktrackPoint   	( );
    bool            check               	( bool );
    bool            belongsToT          	( Enode * );
    void            computeModel        	( );

    set<variable *> get_variables       (Enode * e);
    variable *	    create_variable	( Enode * );

    void	    add_literal	        ( Enode * );
    void	    pop_literal	        ( vector<literal*>::size_type );

private:
    vector < variable * >	              v_set;
    vector < literal *  >	              asserted_lits;
    vector < vector< pair<double, double> > > history;
};
#endif
