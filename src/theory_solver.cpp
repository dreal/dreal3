#include "theory_solver.h"
#include <limits>

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

	_problem = new rp_problem;
	rp_problem_create( _problem, "icp_holder" );

	_ts = &rp_problem_symb (*_problem);
	_b  = &rp_problem_box (*_problem);

}

NLRSolver::~NLRSolver( )
{
  // Here Deallocate External Solver
  rp_problem_destroy(_problem);
  rp_reset_library();
}

bool NLRSolver::icp_prop(rp_problem * p)
{
  rp_selector * select;
  rp_new( select, rp_selector_roundrobin, (p) );
  bool result = false;

  rp_splitter * split;
  rp_new( split, rp_splitter_mixed, (p) );

  icp_solver solver( (p), 10, select, split);
  _solver = &solver;	//solver created

  if (!rp_box_empty(rp_problem_box(*p)))
    {
      int clock_solve = rp_clock_create();
      rp_clock_start(clock_solve);
      rp_box b = solver.prop();
      if (!rp_box_empty(b))
        {
          char tmp[100];
          sprintf(tmp,"[%ld ms]",rp_clock_elapsed_time(clock_solve));
          cout<<endl<<"------------------"<<endl;
          cout<<"PROP: It's possible to have the solution in the following box:"<<endl;
          rp_box_cout(b, 5, RP_INTERVAL_MODE_BOUND);
          cout<<"------------------"<<endl;
          result = true;
        }
      rp_clock_stop(clock_solve);
      // if (solver.solution() )
      //   {
      //     //	rp_problem_destroy(p);
      //     result = true;
      //   }
    }
  // rp_problem_destroy(p);
  cerr << "NLRSolver::icp_prop: " << (result ? "sat" : "unsat") << endl;
  return result;
}

bool NLRSolver::icp_solve(rp_problem * p)
{
	rp_selector * select;
	rp_new( select, rp_selector_roundrobin, (p) );

	rp_splitter * split;
	rp_new( split, rp_splitter_mixed, (p) );

	icp_solver solver( (p), 10, select, split);
	_solver = &solver;	//solver created

	if (rp_box_empty(rp_problem_box(*p)))
	{
//		cout<<"The selected set of theory atoms is unsatisfiable.\n";
	}
	else
	{
   		int clock_solve = rp_clock_create();
      		rp_clock_start(clock_solve);

      		rp_box b;
		int nb_isafe = 0;

   		if ((b=solver.compute_next())!=NULL)
		//was a while statement
      		{
			char tmp[100];
			sprintf(tmp,"[%ld ms]",rp_clock_elapsed_time(clock_solve));

			if (rp_box_interval_safe(b))
			{
				++nb_isafe;
			}


			cout<<endl<<"------------------"<<endl;
			cout<<"The formula is satisfiable under perturbations, which can be witnessed by ANY point in the following box:"<<endl;
			rp_box_cout(b, 5, RP_INTERVAL_MODE_BOUND);
			cout<<"------------------"<<endl;

      		}
      		rp_clock_stop(clock_solve);

		cout << "Solved in "<< rp_clock_get(clock_solve) << "ms"<<endl;
//			   << std::endl << solver.solution() << " solution(s)"
//			   << std::endl << solver.nsplit() << " split(s)"
//			   << std::endl << solver.nboxes() << " box(es) created in memory"
//			   << std::endl;

	       	if (solver.solution() )
		{
                  //	rp_problem_destroy(p);
			return true;
		}
	}

       	// rp_problem_destroy(p);
	return false;
}

variable * NLRSolver::add_variable( Enode * e )
{
  	for (vector<variable *>::iterator it = v_list.begin() ; it != v_list.end(); it++)
	{
		if ( e == (*it) -> get_enode() )
		{
			return NULL;
		}
	}
	variable * var = new variable(e, _b, _ts);
        const string tmp_str = e->getCar() -> getName();
        const char* name = tmp_str.c_str();
        const double lb = e->hasValue() ? e->getLowerBound() : -std::numeric_limits<double>::infinity();
        const double ub = e->hasValue() ? e->getUpperBound() : std::numeric_limits<double>::infinity();
	var -> mk_rp_variable(name, lb, ub);
        // cerr << "Name: " << name << "\t"
        //      << "LB: " << lb << "\t"
        //      << "UB: " << ub << endl;

	return var;
}


void NLRSolver::get_variables(Enode * e, vector<variable *> & vl)
{

  Enode * p = NULL;

  if ( e -> isTerm( ) )
  {
	if ( e -> isVar() )
	{
		variable * var = add_variable( e );
		if (var != NULL ) vl.push_back(var);
	    	get_variables( e->getCar(), vl );
    	}

	p = e -> getCdr();

	while ( !p->isEnil( ) )
    	{
		get_variables( p->getCar(), vl );
      		p = p -> getCdr() ;
    	}
  }
}

void NLRSolver::pop_literal (vector<literal *> & ll)
{
  literal * lit = ll.back();
  ll.pop_back();
  rp_vector_pop(rp_problem_ctrs(*_problem),*(lit->_c));
}

void NLRSolver::add_literal ( Enode * e, vector< literal *> & ll )
{
  // If `e` is already added, then skip
  for (vector<literal *>::iterator it = ll.begin() ; it != ll.end(); it++)
    {
      if ( e == (*it) -> get_enode() )
        {
          return;
        }
    }

  literal * lit = new literal( e , _ts );
  // cerr << "Org Str: |" << e << "|" << endl;
  const string infix_str = infix(e, e->getPolarity());
  const char* infix_cstr = infix_str.c_str();
  // cerr << "Infix Str: |" << infix_cstr << "|" << endl;
  lit->mk_constraint( infix_cstr );

  ll.push_back(lit);
  rp_vector_insert(rp_problem_ctrs(*_problem),*(lit->_c));

  /* creation of relation var -> number of constraints containing var */
  for (int i=0; i<rp_constraint_arity(*(lit->_c)); ++i)
    {
      ++rp_variable_constrained(rp_problem_var(*_problem,rp_constraint_var(*(lit->_c),i)));
    }
  // rp_problem_display(stdout, *_problem);
}


//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is
// called before the actual solving starts.
//

lbool NLRSolver::inform( Enode * e )
{
  cerr << "inform: " << e << endl;
	assert( e -> isAtom() );

  	get_variables( e, v_list );
	add_literal ( e, l_list );

	cout << " has polarity " << toInt(e->getPolarity()) << " "<<endl;

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
  cerr << "asserLit: (" << e << ", " << reason << ")" << endl;
  (void)e;
  (void)reason;

  // cerr << "AssertLit with " << reason << " " << e << endl;

  add_literal (e, assigned_lits);
  // cerr << " has polarity " << toInt(e->getPolarity()) << endl;

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
  cerr << "pushBacktrackPoint:" << endl;
  // Save the current box into the history_boxes (stack of boxes)
  rp_box* new_box;
  rp_box_clone(new_box, rp_problem_box(*_problem));
  cerr << "box cloned:" << endl;
  history_boxes.push_back(new_box);
  cerr << "box added:" << endl;
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
  cerr << "popBacktrackPoint" << endl;

  // Pop a box from the history stack and restore
  rp_box* old_box = history_boxes.back();
  history_boxes.pop_back();
  rp_box_copy(rp_problem_box(*_problem), *old_box);
  rp_box_destroy(old_box);

  // pop literal from assigned_lits
  pop_literal(assigned_lits);
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool NLRSolver::check( bool complete )
{
  bool result = true;
  cerr << "check: "<< (complete ? "complete" : "incomplete") << endl;
  if (complete)
    {
      // Complete Check
      explanation.clear();
      result = icp_solve(_problem);
      if(!result) {
        cout<<"#explanation provided: ";
        for (vector<literal *>::iterator it = assigned_lits.begin(); it!= assigned_lits.end(); it++)
          {
            explanation.push_back( (*it) -> get_enode() );
            cout << (*it)->get_enode() <<" with polarity "
                 << toInt((*it)->get_enode()->getPolarity()) << " ";
          }
        cout<< endl;
      }
    }
  else {
    // incomplete check
    // 1. run prop
    // 2. check emptyness
    // 2.1. empty? => UNSAT
    // 2.2. non-empty? => SAT (possibly)
    result = icp_prop(_problem);
  }
  return result;

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
    cerr << "computeModel" << endl;
}

#ifdef PRODUCE_PROOF
Enode * NLRSolver::getInterpolants( )
{
  return NULL;
}
#endif
