#ifndef THEORY_SOLVER_H
#define THEORY_SOLVER_H

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
             	, vector< Enode * > &
                , bool);

  	~NRASolver ( );

	bool		icp_solve		( rp_problem * );
        bool            icp_prop                (rp_problem * );

  	lbool  		inform              	( Enode * );
  	bool           	assertLit           	( Enode *, bool = false );
  	void            pushBacktrackPoint  	( );
  	void            popBacktrackPoint   	( );
  	bool            check               	( bool );
  	bool            belongsToT          	( Enode * );

  	void            computeModel        	( );

//	void	 	get_variables	( Enode * , vector< variable *> & );
        set<variable *> get_variables   (Enode * e, vector<variable *> & vl);

	variable *	add_variable	( Enode * );

	void		add_literal	( Enode * );
	void		pop_literal	( );
        bool            contain_ode     ( );

private:

	vector< variable * >	v_list;
//	vector< literal * >	l_list;
	vector< literal * >	assigned_lits;
        rp_box_stack *          history_boxes;

	icp_solver * 		_solver;

	rp_table_symbol *	_ts;
	rp_box *		_b;

	rp_problem * 		_problem;
        bool                    _contain_ode;

        // set of ODE variables assigned so far
        set < variable* >       _ode_vars;
        map < Enode*, set < variable* > > _enode_to_vars;
};
#endif
