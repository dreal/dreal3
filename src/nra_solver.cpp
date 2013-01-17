#include "nra_solver.h"
#include <boost/algorithm/string/predicate.hpp>

NRASolver::NRASolver( const int           i
                      , const char *        n
                      , SMTConfig &         c
                      , Egraph &            e
                      , SStore &            t
                      , vector< Enode * > & x
                      , vector< Enode * > & d
                      , vector< Enode * > & s
    )
    : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
{
//initialize icp solver first

}

NRASolver::~NRASolver( )
{
    // Here Deallocate External Solver
}

// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is
// called before the actual solving starts.
//
lbool NRASolver::inform( Enode * e )
{
    return l_True;
}

//
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
bool NRASolver::assertLit ( Enode * e, bool reason )
{
    return true;
}

//
// Saves a backtrack point
// You are supposed to keep track of the
// operations, for instance in a vector
// called "undo_stack_term", as happens
// in EgraphSolver
//
void NRASolver::pushBacktrackPoint ( )
{

}

//
// Restore a previous state. You can now retrieve
// the size of the stack when you pushed the last
// backtrack point. You have to implement the
// necessary backtrack operations
// (see for instance backtrackToStackSize( )
// in EgraphSolver)
// Also make sure you clean the deductions you
// did not communicate
//
void NRASolver::popBacktrackPoint ( )
{

}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool NRASolver::check( bool complete )
{
    return !complete;
}

//
// Return true if the enode belongs
// to this theory. You should examine
// the structure of the node to see
// if it matches the theory operators
//
bool NRASolver::belongsToT( Enode * e )
{
    (void)e;
    assert( e );
    return true;
}

//
// Copy the model into enode's data
//
void NRASolver::computeModel( )
{
    cerr << "computeModel" << endl;
}

#ifdef PRODUCE_PROOF
Enode * NRASolver::getInterpolants( )
{
    return NULL;
}
#endif
