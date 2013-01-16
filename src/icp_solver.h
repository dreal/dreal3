//wrapper for realpaver
#ifndef ICPSOLVER_H
#define ICPSOLVER_H

#include "literal.h"
#include "ode_solver.h"

class icp_solver
{
public:

  	icp_solver( rp_problem * p,
                    set < variable* > ode_vars,
                    double improve, rp_selector * vs,
                    rp_splitter * ds, rp_existence_prover * ep = 0);

  	~icp_solver();

        bool            propagation_with_ode (rp_box , bool );
  	rp_box 		compute_next(bool hasDiff); //computation of the next solution
        rp_box          prop();          //only propagate

  	int 		solution();	//number of solutions
  	int 		nboxes();	//number of boxes
  	int 		nsplit();	//number of branching

        void           	prune                   ( rp_box *, literal * );
        void            prune                   ( rp_box *, rp_problem * );
        void            branch                  ( rp_box * );

private:

  	rp_problem * _problem;     /* problem to be solved                    */
  	rp_propagator _propag;     /* reduction algorithm using propagation   */
  	rp_box_stack _boxes;       /* the set of boxes during search          */
  	rp_selector * _vselect;    /* selection of variable to be split       */
  	rp_splitter * _dsplit;     /* split function of variable domain       */
  	rp_existence_prover * _ep; /* existence prover                        */
        set < variable* > _ode_vars;
  	int _sol;                  /* number of computed solutions            */
  	int _nsplit;               /* number of split steps                   */
  	double _improve;           /* improvement factor of iterative methods */

        icp_solver& operator=(const icp_solver& s);
};

#endif
