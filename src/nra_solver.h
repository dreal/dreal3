#ifndef NRA_SOLVER_H
#define NRA_SOLVER_H

#include "TSolver.h"
#include "Egraph.h"

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

private:

};
#endif
