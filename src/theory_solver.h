#ifndef THEORY_SOLVER_H
#define THEORY_SOLVER_H

#include "TSolver.h"
#include "icp_solver.h"

class NLRSolver : public OrdinaryTSolver
{
public:

  	NLRSolver( const int, const char *, SMTConfig &, Egraph &, SStore &
		, vector< Enode * > &
	     	, vector< Enode * > &
             	, vector< Enode * > & );

  	~NLRSolver ( );

	bool		icp_solve		( rp_problem * );


  	lbool  		inform              	( Enode * );
  	bool           	assertLit           	( Enode *, bool = false );
  	void            pushBacktrackPoint  	( );
  	void            popBacktrackPoint   	( );
  	bool            check               	( bool );
  	bool            belongsToT          	( Enode * );

  	void            computeModel        	( );

	void	 	get_variables	( Enode * , vector< variable * > & );
	variable *	add_variable	( Enode * );

	void		add_literal	( Enode * , vector< literal * > & );


private:

	vector< variable * >	v_list;
	vector< literal * >	l_list;
	vector< literal * >	temp_l_list;

	icp_solver * 		_solver;

	rp_table_symbol *	_ts;
	rp_box *		_b;

	rp_problem * 		_problem;

};

#endif
