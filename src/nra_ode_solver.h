#ifndef NRAODE_SOLVER_H
#define NRAODE_SOLVER_H

#include "TSolver.h"
#include "Egraph.h"
#include "icp_solver.h"
#include "variable.h"

class NRAODESolver : public OrdinaryTSolver
{
public:

  	NRAODESolver( const int, const char *, SMTConfig &, Egraph &, SStore &
		, vector< Enode * > &
	     	, vector< Enode * > &
             	, vector< Enode * > &
                , bool);

  	~NRAODESolver ( );

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
        set<variable *> get_variables   (Enode * e);

        variable *	create_variable	( Enode * );
//	variable *	add_variable	( Enode * );

	void		add_literal	( Enode * );
	void		pop_literal	( vector<literal*>::size_type );
        bool            contain_ode     ( );


private:

	set< variable * >	v_set;
//	vector< literal * >	l_list;
	vector< literal * >	assigned_lits;

        rp_box_stack *          history_boxes;
        vector< vector<literal*>::size_type >        history_num_lits;


	icp_solver * 		_solver;

	rp_table_symbol *	_ts;
	rp_box *		_b;

	rp_problem * 		_problem;
        bool                    _contain_ode;

        // set of ODE variables assigned so far
        set < variable* >       _ode_vars;
        map < Enode*, set < variable* > > _enode_to_vars;

        vector< variable* >                    stack_ode_vars;
        vector< vector<variable*>::size_type >   history_num_odes;

};
#endif
