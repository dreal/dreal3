
#include "theory_solver.h"

NLRSolver::NLRSolver( const int           i
                        , const char *        n
	                , SMTConfig &         c
	                , Egraph &            e
			, SStore &            t
	                , vector< Enode * > & x
	                , vector< Enode * > & d
                        , vector< Enode * > & s)
  : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
{ 
//initialize icp solver first
	rp_init_library();

	rp_problem problem;
	_problem = &problem; 	

	rp_selector * select;
	rp_new( select, rp_selector_roundrobin, (_problem) );

	rp_splitter * split;
	rp_new( split, rp_splitter_mixed, (_problem) );

	icp_solver solver( (_problem), 10, select, split);
	_solver = &solver;	//solver created

}

NLRSolver::~NLRSolver( )
{
  // Here Deallocate External Solver

}

//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is 
// called before the actual solving starts.
// 
lbool NLRSolver::inform( Enode * e )  
{ 
  (void)e;
  assert( e -> isAtom() );


  assert( belongsToT( e ) );
  return l_Undef;
}

// 
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
bool NLRSolver::assertLit ( Enode * e, bool reason )
{
  (void)e;
  (void)reason;
  assert( e );
  assert( belongsToT( e ) );
  return true;
}

//
// Saves a backtrack point
// You are supposed to keep track of the
// operations, for instance in a vector
// called "undo_stack_term", as happens
// in EgraphSolver
//
void NLRSolver::pushBacktrackPoint ( )
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
void NLRSolver::popBacktrackPoint ( )
{
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool NLRSolver::check( bool complete )    
{ 
  (void)complete;
  // Here check for consistency
  return true;
}

//
// Return true if the enode belongs
// to this theory. You should examine
// the structure of the node to see
// if it matches the theory operators
//
bool NLRSolver::belongsToT( Enode * e )
{
  (void)e;
  assert( e );
  return true;
}

//
// Copy the model into enode's data
//
void NLRSolver::computeModel( )
{
}

#ifdef PRODUCE_PROOF
Enode * NLRSolver::getInterpolants( )
{
  return NULL;
}
#endif
