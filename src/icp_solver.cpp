//icp solver

#include "icp_solver.h"
using namespace std;

icp_solver::icp_solver(const vector<Enode*> & stack,
                       map<Enode*, pair<double, double> > & env,
                       vector<Enode*> & exp,
                       double improve
    )
    :
    _stack(stack),
    _env(env),
    _boxes(env.size()), //number of variables
    _propag(NULL),
    _ep(NULL),
    _sol(0),
    _nsplit(0),
    _explanation(exp)
{
    rp_init_library();
    _problem = create_rp_problem(stack, env);

    rp_problem_display(stdout, *_problem);

    // _propag = new rp_propagator(_problem);

    rp_selector * _vselect;
    rp_new( _vselect, rp_selector_roundrobin, (_problem) );

    rp_splitter * _dsplit;
    rp_new( _dsplit, rp_splitter_mixed, (_problem) );

    solver = new rp_bpsolver(_problem,improve,_vselect,_dsplit); //,prover);

    // // Check once the satisfiability of all the constraints
    // // Necessary for variable-free constraints
    // int i = 0, sat = 1;

    // while ((i<rp_problem_nctr(*_problem)) && (sat))
    // {
    //     if (rp_constraint_unfeasible(rp_problem_ctr(*_problem,i),rp_problem_box(*_problem)))
    //     {
    //         sat = 0;
    //     }
    //     else ++i;
    // }

    // if (sat)
    // {
    //     // Insertion of the initial box in the search structure
    //     _boxes.insert(rp_problem_box(*_problem));

    //     // Management of improvement factor
    //     if ((improve>=0.0) && (improve<=100.0))
    //     {
    //         _improve = 1.0-improve/100.0;
    //     }
    //     else
    //     {
    //         _improve = 0.875;  /* 12.5% */
    //     }
    //     _propag->set_improve(_improve);

    //     // Creation of the operators and insertion in the propagator
    //     rp_hybrid_factory hfact(_improve);
    //     hfact.apply(_problem,*_propag);

    //     rp_domain_factory dfact;
    //     dfact.apply(_problem,*_propag);

    //     cerr << "icp_solver::icp_solver" << endl;
    //     cerr << rp_problem_nctr(*_problem) << endl;
    //     rp_problem_display(stdout, *_problem);


    //     rp_newton_factory nfact(_improve);
    //     nfact.apply(_problem,*_propag);

    //     //rp_3b_factory bfact(_improve);
    //     //bfact.apply(_problem,_propag);

    //     // Used for round-robin strategy: last variable split
    //     rp_box_set_split(_boxes.get(),-1);//-1?: length - this number
    // }
    // else
    // {
    //     rp_box_set_empty(rp_problem_box(*_problem));
    // }

    cerr << "icp_solver::icp_solver() End." << endl;
}

rp_problem* icp_solver::create_rp_problem(const vector<Enode*> & stack,
                                          map<Enode*, pair<double, double> > & env)
{
    cerr << "icp_solver::create_rp_problem" << endl;

    rp_problem* result = new rp_problem;
    rp_problem_create( result, "icp_holder" );

    // ======================================
    // Create rp_variable for each var in env
    // ======================================
    for(map<Enode*, pair<double, double> >::const_iterator ite = env.begin();
        ite != env.end();
        ite++)
    {
        Enode* key = (*ite).first;
        double lb =  (*ite).second.first;
        double ub =  (*ite).second.second;

        rp_variable * _v = new rp_variable;
        string name = key->getCar()->getName();
        rp_variable_create( _v, name.c_str());

        int rp_id = rp_vector_insert(rp_table_symbol_vars(rp_problem_symb(*result)),
                                     (*_v));

        rp_box_enlarge_size(&rp_problem_box (*result), 1);

        rp_bsup(rp_box_elem(rp_problem_box(*result), rp_id)) = ub;
        rp_binf(rp_box_elem(rp_problem_box(*result), rp_id)) = lb ;

        cerr << "["
             << rp_bsup(rp_box_elem(rp_problem_box(*result), rp_id))
             << ","
             << rp_binf(rp_box_elem(rp_problem_box(*result), rp_id))
             << "]" << endl;

        rp_union_interval u;
        rp_union_create(&u);
        rp_union_insert(u,
                        rp_box_elem(rp_problem_box(*result),
                                       rp_id));
        rp_union_copy(rp_variable_domain(*_v),u);
        rp_union_destroy(&u);

        enode_to_rp_id[key] = rp_id;

        cerr << "Key: " << name << "\t"
             << "value : [" << lb << ", " << ub << "] \t"
             << "rp_id: " << rp_id << endl;
    }

    // ===============================================
    // Create rp_constraints for each literal in stack
    // ===============================================
    for(vector<Enode*>::const_iterator ite = stack.begin();
        ite != stack.end();
        ite++)
    {
        Enode* l = *ite;
        stringstream buf;
        rp_constraint * _c = new rp_constraint;
        l->print_infix(buf, l->getPolarity());
        string temp_string = buf.str();

        if(temp_string.compare("0 = 0") != 0) {
            // Parse the string (infix form) to create the constraint _c
            rp_parse_constraint_string ( _c ,
                                         temp_string.c_str(),
                                         rp_problem_symb(*result) );

            // Add to the problem
            rp_vector_insert(rp_problem_ctrs(*result),
                             *_c);

            // Update Counter
            for (int i=0; i < rp_constraint_arity(*_c); ++i)
            {
                ++rp_variable_constrained(rp_problem_var(*result,rp_constraint_var(*_c,i)));
            }

            cerr << "Constraint: "
                 << (l->getPolarity() == l_True ? " " : "Not")
                 << l << endl;
            cerr << "          : " << temp_string << endl;
        }
    }
    return result;
}

icp_solver::~icp_solver()
{
//    rp_delete(_vselect);
//    rp_delete(_dsplit);
//    if (_ep) rp_delete(_ep);
    rp_problem_destroy(_problem);
    rp_reset_library();
//    delete _propag;
    delete solver;
}

rp_box icp_solver::prop()
{
  cerr << "icp_solver::prop" << endl;
  assert(_boxes.size() == 1);

  _propag->apply(_boxes.get());
  return( _boxes.get() );
}


bool icp_solver::solve()
{
    //rp_problem_display(stdout,problem);

    if (rp_box_empty(rp_problem_box(*_problem)))
    {
        cerr << "Unfeasibility detected before solving";

        /* TODO: what about explanation? */
        copy(_stack.begin(),
             _stack.end(),
             std::back_inserter(_explanation));

        return false;
    }
    else
    {
        // rp_ofilter_text oft(&problem,&cout,-1);
        // rp_ofilter_pstricks oft(&problem,&cout);
        // oft.apply_box(rp_problem_box(problem),"[initial]");
        // int clock_solve = rp_clock_create();
        // rp_clock_start(clock_solve);

        rp_box b;
//        int nb_isafe = 0;
        if ((b=solver->compute_next())!=NULL)
        {
            /* SAT */
            // cerr << rp_clock_elapsed_time(clock_solve) << "ms" << endl;
//            if (rp_box_interval_safe(b)) ++nb_isafe;
            cerr << "SAT with the following box:" << endl;
            rp_box_display_simple(b);

            // Update the value in the env
            cerr << "Update ENV!!!!!!!!!" << endl;
            for(map<Enode*, pair<double, double> >::const_iterator ite = _env.begin();
                ite != _env.end();
                ite++)
            {
                Enode* key = (*ite).first;
                int rp_id = enode_to_rp_id[key];
                double ub = rp_bsup(rp_box_elem(rp_problem_box(*_problem), rp_id));
                double lb = rp_binf(rp_box_elem(rp_problem_box(*_problem), rp_id));
                _env[key] = make_pair(lb, ub);
                cout << "Key: " << key << "\t Value: [" << lb << ", " << ub << "]" << endl;
            }


            return true;
        }
        else {
            /* UNSAT */

            /* TODO: what about explanation? */
            cerr << "UNSAT!" << endl;
            copy(_stack.begin(),
                 _stack.end(),
                 std::back_inserter(_explanation));

            return false;
        }
        // rp_clock_stop(clock_solve);
        // cout << std::endl
        //      << "Solving in "
        //      << rp_clock_get(clock_solve) << "ms"
        //      << std::endl
        //      << solver.solution()
        //      << " solution(s)"
        //      << std::endl
        //      << solver.nsplit()
        //      << " split(s)"
        //      << std::endl
        //      << solver.nboxes()
        //      << " box(es) created in memory"
        //      << std::endl;
    }
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
        if (_propag->apply(_boxes.get()))
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
