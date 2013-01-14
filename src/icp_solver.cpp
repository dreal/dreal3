//icp solver

#include "icp_solver.h"
using namespace std;

icp_solver::icp_solver(rp_problem * p,
                       set < variable* > & ode_vars,
                       double improve,
                       rp_selector * vs,
                       rp_splitter * ds,
                       rp_existence_prover * ep
    ):
        _problem(p),
        _ode_vars(ode_vars),
        _propag(p),
        _boxes(rp_problem_nvar(*p)), //number of variables
        _vselect(vs),
        _dsplit(ds),
        _ep(ep),
        _sol(0),
        _nsplit(0)
{
        // Check once the satisfiability of all the constraints
        // Necessary for variable-free constraints
        int i = 0, sat = 1;

        while ((i<rp_problem_nctr(*p)) && (sat))
        {
                if (rp_constraint_unfeasible(rp_problem_ctr(*p,i),rp_problem_box(*p)))
                {
                        sat = 0;
                }
                else ++i;
        }

        if (sat)
        {
                // Insertion of the initial box in the search structure
                _boxes.insert(rp_problem_box(*p));

                // Management of improvement factor
                if ((improve>=0.0) && (improve<=100.0))
                {
                        _improve = 1.0-improve/100.0;
                }
                else
                {
                        _improve = 0.875;  /* 12.5% */
                }
                _propag.set_improve(_improve);

                // Creation of the operators and insertion in the propagator
                rp_hybrid_factory hfact(_improve);
                hfact.apply(p,_propag);

                rp_domain_factory dfact;
                dfact.apply(p,_propag);

                rp_newton_factory nfact(_improve);
                nfact.apply(p,_propag);

                //rp_3b_factory bfact(_improve);
                //bfact.apply(p,_propag);

                // Used for round-robin strategy: last variable split
                rp_box_set_split(_boxes.get(),-1);//-1?: length - this number
        }
        else
        {
                rp_box_set_empty(rp_problem_box(*p));
        }
}


icp_solver::~icp_solver()
{
	rp_delete(_vselect);
	rp_delete(_dsplit);
	if (_ep) rp_delete(_ep);
}

rp_box icp_solver::prop()
{
  cerr << "icp_solver::prop" << endl;
  assert(_boxes.size() == 1);

  _propag.apply(_boxes.get());
  return( _boxes.get() );
}

rp_box icp_solver::compute_next(bool hasDiff)
{

    cout<<"------------------"<<endl;
    cout<<"The interval pruning and branching trace is:";

    if (_sol>0) //if you already have a solution, discard this obtained solution box and backtrack
    {
        _boxes.remove();
    }
    while (!_boxes.empty()) //if there's no more box on the stack, you are done with compute_next
    {

    /*moved the following lines to rp_prop
      cout<<endl<<"[before pruning] "<<endl;
      rp_box_cout(_boxes.get(), 5, RP_INTERVAL_MODE_BOUND );
    */
        if (_propag.apply(_boxes.get()))
        {
            if (hasDiff) {

                rp_box current_box = _boxes.get();

                for(set<variable*>::iterator ite = _ode_vars.begin();
                    ite != _ode_vars.end();
                    ite++)
                {
                    (*ite)->set_lb(
                        rp_binf(
                            rp_box_elem(current_box, (*ite)->get_rpid())
                            )
                        );
                    (*ite)->set_ub(
                        rp_bsup(
                            rp_box_elem(current_box, (*ite)->get_rpid())
                            )
                        );
                }

                ode_solver odeSolver(_ode_vars);

                if (odeSolver.solve())
                {
                    int i;
                    if ((i=_vselect->apply(_boxes.get()))>=0)
                    {
                        ++_nsplit;
                        _dsplit->apply(_boxes,i);

                        //monitoring
                        cout<<endl<<"[branched on x"<<i<<"]"<<endl;
                        //rp_box_cout(_boxes.get(), 5, RP_INTERVAL_MODE_BOUND );

                    }
                    else
                    {
                        ++_sol;
                        if (_ep) _ep->prove(_boxes.get());
                        return( _boxes.get() );
                    }
                }
            }
        }
        else
        {
            cout<<"[conflict detected]"<<endl;
            _boxes.remove();
        }
    }
    return( NULL );
}

int icp_solver::solution()
{
        return _sol;
}

int icp_solver::nboxes()
{
        return( _boxes.length() );
}

int icp_solver::nsplit()
{
        return( _nsplit );
}

icp_solver& icp_solver::operator=(const icp_solver& s)
{
  	return( *this );
}

