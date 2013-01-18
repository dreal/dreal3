//wrapper for realpaver
#ifndef ICPSOLVER_H
#define ICPSOLVER_H

#include "realpaver.h"
#include "Enode.h"

class icp_solver
{
public:
    icp_solver(const vector<Enode*> & stack,
               map<Enode*, pair<double, double> > & env,
               vector<Enode*> & exp,
               double improve
              );

    ~icp_solver();

    rp_problem*   create_rp_problem(const vector<Enode*> & stack,
                                    map<Enode*, pair<double, double> > & env);

    rp_box        compute_next(bool hasDiff); //computation of the next solution
    rp_box        prop();         //only propagate

    int           solution();     //number of solutions
    int           nboxes();       //number of boxes
    int           nsplit();       //number of branching

    bool          solve();

    /* void          prune                   ( rp_box *, literal * ); */
    /* void          prune                   ( rp_box *, rp_problem * ); */
    /* void          branch                  ( rp_box * ); */

private:

    rp_problem * _problem;     /* problem to be solved                    */
    rp_propagator * _propag;     /* reduction algorithm using propagation   */
    rp_box_stack _boxes;       /* the set of boxes during search          */
    rp_selector * _vselect;    /* selection of variable to be split       */
    rp_splitter * _dsplit;     /* split function of variable domain       */
    rp_existence_prover * _ep; /* existence prover                        */
    int _sol;                  /* number of computed solutions            */
    int _nsplit;               /* number of split steps                   */
    double _improve;           /* improvement factor of iterative methods */

    map<Enode*, int> enode_to_rp_id;
    rp_bpsolver * solver;

    vector<Enode*> & _explanation;
    const vector<Enode*> & _stack;
    map<Enode*, pair<double, double> > & _env;

    icp_solver& operator=(const icp_solver& s);
};

#endif
