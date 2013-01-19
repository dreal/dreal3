/****************************************************************************
 * RealPaver v. 1.0                                                         *
 *--------------------------------------------------------------------------*
 * Author: Laurent Granvilliers                                             *
 * Copyright (c) 1999-2003 Institut de Recherche en Informatique de Nantes  *
 * Copyright (c) 2004-2006 Laboratoire d'Informatique de Nantes Atlantique  *
 *--------------------------------------------------------------------------*
 * RealPaver is distributed WITHOUT ANY WARRANTY. Read the associated       *
 * COPYRIGHT file for more details.                                         *
 *--------------------------------------------------------------------------*
 * rp_solver.cpp                                                            *
 ****************************************************************************/

#include "rp_solver.h"

// ---------------------------------------------------------
// Branch-and-prune algorithm for solving constraint systems
// ---------------------------------------------------------
rp_bpsolver::rp_bpsolver(rp_problem * p,
			 double improve,
			 rp_selector * vs,
			 rp_splitter * ds,
			 rp_existence_prover * ep):
  _problem(p),
  _propag(p),
  _boxes(rp_problem_nvar(*p)),//sean:number of variables
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
    rp_box_set_split(_boxes.get(),-1);//sean: why is the last variable -1? oh, must be length - this number
  }
  else
  {
    rp_box_set_empty(rp_problem_box(*p));
  }
}

rp_bpsolver::~rp_bpsolver()
{
  rp_delete(_vselect);
  rp_delete(_dsplit);
  if (_ep) rp_delete(_ep);
}

void interval_cout_local(rp_interval i, int digits, int mode)
{
  char tmp[255];
  rp_interval_print(tmp,i,digits,mode);
  std::cout<< tmp;
}

void pprint_vars(FILE* out, rp_problem p, rp_box b)
{
    for(int i = 0; i < rp_problem_nvar(p); i++)
    {
        fprintf(out, "%s", rp_variable_name(rp_problem_var(p, i)));
        fprintf(out, " is in: ");
        interval_cout_local(rp_box_elem(b,i), 6, RP_INTERVAL_MODE_BOUND);
        if (i != rp_problem_nvar(p) - 1)
            fprintf(out, ";");
        fprintf(out, "\n");
    }
}


rp_box rp_bpsolver::compute_next()
{
  if (_sol>0)
  {
    _boxes.remove();
  }
  while (!_boxes.empty())
  {
    if (_propag.apply(_boxes.get()))//sean: here it is! propagation before split!!!
    {
      int i;
      if ((i=_vselect->apply(_boxes.get()))>=0)
      {
	++_nsplit;
	_dsplit->apply(_boxes,i);

           std::cout<<std::endl<<"[branched on x"<<i<<"]"<<std::endl;
           pprint_vars(stdout, *_problem, _boxes.get());
      }
      else
      {
	++_sol;
	if (_ep) _ep->prove(_boxes.get());
	return( _boxes.get() );
      }
    }
    else
    {
      /* Added for dReal2 */
      printf("[conflict detected]\n");
      _boxes.remove();
    }
  }
  return( NULL );
}

int rp_bpsolver::solution()
{
  return _sol;
}

int rp_bpsolver::nboxes()
{
  return( _boxes.length() );
}

int rp_bpsolver::nsplit()
{
  return( _nsplit );
}


rp_bpsolver::rp_bpsolver(const rp_bpsolver& s):
  _problem(s._problem),
  _propag(0),
  _boxes(rp_problem_nvar(*_problem)),
  _vselect(NULL),
  _ep(NULL)
{}

rp_bpsolver& rp_bpsolver::operator=(const rp_bpsolver& s)
{
  return( *this );
}
