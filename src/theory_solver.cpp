#include "theory_solver.h"
#include <boost/algorithm/string/predicate.hpp>

NRASolver::NRASolver( const int           i
                        , const char *        n
	                , SMTConfig &         c
	                , Egraph &            e
			, SStore &            t
	                , vector< Enode * > & x
	                , vector< Enode * > & d
                        , vector< Enode * > & s
                        , bool ode
    )
  : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
{
//initialize icp solver first
	rp_init_library();

	_problem = new rp_problem;
	rp_problem_create( _problem, "icp_holder" );

	_ts = &rp_problem_symb (*_problem);
	_b  = &rp_problem_box (*_problem);
        _contain_ode = ode;
}

NRASolver::~NRASolver( )
{
  // Here Deallocate External Solver
  rp_problem_destroy(_problem);
  rp_reset_library();
}

bool NRASolver::icp_prop(rp_problem * p)
{
    rp_selector * select;
    rp_new( select, rp_selector_roundrobin, (p) );
    bool result = false;

    rp_splitter * split;
    rp_new( split, rp_splitter_mixed, (p) );

    icp_solver solver( (p), _ode_vars, 10, select, split);
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
        // update the current box with `b`
        rp_box_copy(*_b, b);

        rp_clock_stop(clock_solve);
        // if (solver.solution() )
        //   {
        //     //	rp_problem_destroy(p);
        //     result = true;
        //   }
    }

    // rp_problem_destroy(p);
    cerr << "NRASolver::icp_prop: " << (result ? "sat" : "unsat") << endl;

    if (!result) {
        explanation.clear();
        cout<<"#explanation provided: ";
        for (vector<literal *>::iterator it = assigned_lits.begin(); it!= assigned_lits.end(); it++)
        {
            explanation.push_back( (*it) -> get_enode() );
            cout << (*it)->get_enode() <<" with polarity "
                 << toInt((*it)->get_enode()->getPolarity()) << " ";
        }
        cout<< endl;
    }
    return result;
}

bool NRASolver::icp_solve(rp_problem * p)
{
	rp_selector * select;
	rp_new( select, rp_selector_roundrobin, (p) );

	rp_splitter * split;
	rp_new( split, rp_splitter_mixed, (p) );

	icp_solver solver( (p), _ode_vars, 10, select, split);
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

   		if ((b=solver.compute_next(_contain_ode))!=NULL)
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

variable * NRASolver::create_variable( Enode * e )
{
    // Check whether we already have it or not.
    for (set<variable *>::iterator it = v_set.begin() ; it != v_set.end(); it++)
    {
        if ( e == (*it) -> get_enode() )
        {
            return *it;
        }
    }

    variable * var = new variable(e, _b, _ts);

    var->name = e->getCar()->getName();
    const char* name = var->name.c_str();
    const double lb = e->getLowerBound();
    const double ub = e->getUpperBound();

    var -> mk_rp_variable(name, lb, ub);
    cerr << "NRASolver::create_variable" << endl;
    cerr << "Name: " << name << "\t"
         << "LB: " << lb << "\t"
         << "UB: " << ub << endl;
    return var;
}

// variable * NRASolver::add_variable( Enode * e )
// {
//         cerr << "add_variable " << e << endl;

//   	for (set<variable *>::iterator it = v_set.begin() ; it != v_set.end(); it++)
// 	{
// 		if ( e == (*it) -> get_enode() )
// 		{
// 			return NULL;
// 		}
// 	}
// 	variable * var = new variable(e, _b, _ts);
//         const string tmp_str = e->getCar()->getName();
//         const char* name = tmp_str.c_str();
//         const double lb = e->getLowerBound();
//         const double ub = e->getUpperBound();
// 	var -> mk_rp_variable(name, lb, ub);
//         cerr << "NRASolver::add_variable" << endl;
//         cerr << "Name: " << name << "\t"
//              << "LB: " << lb << "\t"
//              << "UB: " << ub << endl;
// 	return var;
// }

set<variable *> NRASolver::get_variables (Enode * e )
{
    set<variable *> result;
    Enode * p = NULL;

    if( e->isSymb( ) ) {
        // do nothing
    }
    else if ( e->isNumb( ) )
    {
        // do nothing
    }
    else if ( e->isTerm( ) )
    {
        if ( e -> isVar() ) {
            variable * var = create_variable( e );
            v_set.insert(var);

            // Add it to result set if `var` is a ODE variable.
            if (var->get_enode()->getODEvartype() != l_Undef) {
                result.insert(var);
            }
        }

        set <variable*> tmp_set = get_variables(e->getCar());
        result.insert(tmp_set.begin(), tmp_set.end());
        p = e->getCdr();
        while ( !p->isEnil( ) )
        {
            tmp_set = get_variables(p->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    }
    else if ( e->isList( ) )
    {
        if ( !e->isEnil( ) )
        {
            set <variable*> tmp_set = get_variables(e->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());

            p = e->getCdr();
            while ( !p->isEnil( ) )
            {
                tmp_set = get_variables(p->getCar());
                result.insert(tmp_set.begin(), tmp_set.end());
                p = p->getCdr();
            }
        }
    }
    else if ( e->isDef( ) )
    {
        // do nothing
    }
    else if ( e->isEnil( ) )
    {
        // do nothing
    }
    else
        opensmt_error( "unknown case value" );
    return result;
}

void NRASolver::pop_literal (vector<literal*>::size_type prev_size )
{
    while(assigned_lits.size() > prev_size) {
        cerr << "Pop_literal" << endl << endl;
        literal * lit = assigned_lits.back();

        rp_constraint_destroy(lit->_c);

//        rp_vector_pop(rp_problem_ctrs(*_problem),*(lit->_c));
        delete lit;
        assigned_lits.pop_back();
    }
}

void NRASolver::add_literal ( Enode * e )
{
    // If `e` is already added, then skip
    for (vector<literal *>::iterator it = assigned_lits.begin() ; it != assigned_lits.end(); it++)
    {
        if ( e == (*it) -> get_enode() )
        {
            return;
        }
    }

    literal * lit = new literal( e , _ts );

    lit->infix_ctr_string = infix(e, e->getPolarity());
    const char* infix_cstr = lit->infix_ctr_string.c_str();
    lit->mk_constraint( infix_cstr );

    if(_contain_ode) {
        cerr << "NRASolver::add_literal _enode_to_vars[" << e << "]" << endl;

        // add corresponding ODE variables to _odes_vars
        const set<variable*> ode_vars_in_lit = _enode_to_vars[e];

        for(set<variable*>::iterator ite = ode_vars_in_lit.begin();
            ite != ode_vars_in_lit.end();
            ite++)
        {
            cerr << "ODE Vars in Lit " << endl
                 << "Name: " << (*ite)->get_enode() << endl
                 << "ODE: " << (*ite)->get_enode()->getODE() << endl;
        }

        _ode_vars.insert(ode_vars_in_lit.begin(), ode_vars_in_lit.end());

        /* copy _odes to stack_ode_vars */
        std::back_insert_iterator< vector<variable*> > back_it (stack_ode_vars);
        copy (ode_vars_in_lit.begin(), ode_vars_in_lit.end(), back_it);
    }

    assigned_lits.push_back(lit);
    rp_vector_insert(rp_problem_ctrs(*_problem),*(lit->_c));

    /* creation of relation var -> number of constraints containing var */
    for (int i=0; i<rp_constraint_arity(*(lit->_c)); ++i)
    {
        ++rp_variable_constrained(rp_problem_var(*_problem,rp_constraint_var(*(lit->_c),i)));
    }
}

set<string> retrieve_ode_set(map <string, string> & m, Enode * e)
{
    set<string> result;
    Enode * p = NULL;
    if( e->isSymb( ) ) {
        // Check it ends with "_t" or "_0".
        string name = e->getName();
        if (boost::algorithm::ends_with(name, "_0") ||
            boost::algorithm::ends_with(name, "_t")) {
            string prefix = name.substr(0, name.size() - 2);
            result.insert(m[prefix]);
        }
    }
    else if ( e->isNumb( ) )
    {
        // do nothing
    }
    else if ( e->isTerm( ) )
    {
        set <string> tmp_set = retrieve_ode_set(m, e->getCar());
        result.insert(tmp_set.begin(), tmp_set.end());
        p = e->getCdr();
        while ( !p->isEnil( ) )
        {
            tmp_set = retrieve_ode_set(m, p->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    }
    else if ( e->isList( ) )
    {
        if ( !e->isEnil( ) )
        {
            set <string> tmp_set = retrieve_ode_set(m, e->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());

            p = e->getCdr();
            while ( !p->isEnil( ) )
            {
                tmp_set = retrieve_ode_set(m, p->getCar());
                result.insert(tmp_set.begin(), tmp_set.end());

                p = p->getCdr();
            }
        }
    }
    else if ( e->isDef( ) )
    {
        // do nothing
    }
    else if ( e->isEnil( ) )
    {
        // do nothing
    }
    else
        opensmt_error( "unknown case value" );
    return result;
}

//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is
// called before the actual solving starts.
//
lbool NRASolver::inform( Enode * e )
{
    cerr << "inform: " << e << endl;
    assert( e -> isAtom() );

    // 1. get_variables collects all the variables and push them to v_list
    // 2. get_variables collects all the `ode` variables in `e` and return
    set<variable *> ode_vars = get_variables( e );
//    add_literal ( e );
    if (contain_ode()) {
        /* Add ODE time variable into v_list */
        for(set<variable*>::iterator ite = ode_vars.begin();
            ite != ode_vars.end();
            ite++)
        {
            Enode * time = (*ite)->get_enode()->getODEtimevar();
            variable * time_var = create_variable(time);
            v_set.insert(time_var);
            (*ite)->setODEtimevar(time_var);
        }
        // update ODE set of e
        // e->setODEs(retrieve_ode_set(egraph.var_to_ode, e));
        // update a mapping from `e` to the corresponding ODE vars.
        _enode_to_vars.insert( std::pair<Enode*, set<variable*> >(e, ode_vars ) );
    }

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
bool NRASolver::assertLit ( Enode * e, bool reason )
{
  cerr << endl << "assertLit: (" << e << ", " << reason << ")" << endl;

  // cerr << "AssertLit with " << reason << " " << e << endl;

  add_literal (e);
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
void NRASolver::pushBacktrackPoint ( )
{
  static bool history_inited = false;
  if(!history_inited) {
    history_boxes = new rp_box_stack(rp_box_size(*_b), rp_box_size(*_b));
    history_inited = true;
  }

  cerr << endl << "pushBacktrackPoint:" << endl;
  // Save the current box into the history_boxes (stack of boxes)
  cerr << "Current Box:" << endl;
  rp_box_display_simple(*_b);
  cerr << endl;

  history_boxes->insert(*_b);
  history_num_lits.push_back(assigned_lits.size());
  history_num_odes.push_back(stack_ode_vars.size());

  cerr << "box added: history_boxes->size() = " << history_boxes->size() << endl;

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
  cerr << endl << "popBacktrackPoint" << endl;
  cerr << "Current Box (before pop):" << endl;
  rp_box_display_simple(*_b);
  cerr << endl;

  // Pop a box from the history stack and restore
  rp_box old_box = history_boxes->get();
  rp_box_copy(*_b, old_box);
//  rp_box_destroy(&old_box);
  history_boxes->remove();

  // Pop a num_lits from the history
  vector<literal*>::size_type prev_size = history_num_lits.back();
  history_num_lits.pop_back();

  cerr << "box popped: history_boxes->size() = " << history_boxes->size() << endl;
  cerr << "Current Box (after pop):" << endl;
  rp_box_display_simple(*_b);
  cerr << endl;

  // pop literal
  pop_literal(prev_size);

  // Pop a num_odes from the history
  vector<literal*>::size_type prev_ode_size = history_num_odes.back();
  history_num_lits.pop_back();

  while(stack_ode_vars.size() > prev_ode_size)
      stack_ode_vars.pop_back();

  _ode_vars.clear();
  _ode_vars.insert(stack_ode_vars.begin(), stack_ode_vars.end());
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool NRASolver::check( bool complete )
{
    bool result = true;
    cerr << endl << "check: "<< (complete ? "complete" : "incomplete") << endl;
    if (complete)
    {
        // Complete Check
        cerr << "We start complete check with the following literals. " << endl;
        cerr << "=======================================================" << endl;
        for (vector<literal *>::iterator it = assigned_lits.begin(); it!= assigned_lits.end(); it++)
        {
            cout << (*it)->get_enode() <<" with polarity "
                 << toInt((*it)->get_enode()->getPolarity()) << endl;
        }
        cerr << "=======================================================" << endl;

        cerr << "with the following ODE literals. " << endl;
        cerr << "=======================================================" << endl;
        for (set<variable*>::iterator it = _ode_vars.begin(); it!= _ode_vars.end(); it++)
        {
            cout << (*it)->get_enode() << "\t:";
            cout << (*it)->get_enode()->getODE() << endl;
        }
        cerr << "=======================================================" << endl;

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

bool NRASolver::contain_ode( )
{
    return _contain_ode;
}


#ifdef PRODUCE_PROOF
Enode * NRASolver::getInterpolants( )
{
  return NULL;
}
#endif
