/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "icp_solver.h"
#include <iomanip>
using namespace std;

icp_solver::icp_solver(SMTConfig& c,
                       const vector<Enode*> & stack,
                       map<Enode*, pair<double, double> > & env,
                       vector<Enode*> & exp,
                       map < Enode*, set < Enode* > > & enode_to_vars
    )
    :
    _config(c),
    _propag(NULL),
    _boxes(env.size()), //number of variables
    _ep(NULL),
    _sol(0),
    _nsplit(0),
    _enode_to_vars(enode_to_vars),
    _explanation(exp),
    _stack(stack),
    _env(env)
{
    rp_init_library();
    _problem = create_rp_problem(stack, env);
    _propag = new rp_propagator(_problem, 10.0, c.nra_proof_out);
    rp_new( _vselect, rp_selector_roundrobin, (_problem) );
    rp_new( _dsplit, rp_splitter_mixed, (_problem) );

    // Check once the satisfiability of all the constraints
    // Necessary for variable-free constraints
    int i = 0, sat = 1;
    while ((i<rp_problem_nctr(*_problem)) && (sat))
    {
        if (rp_constraint_unfeasible(rp_problem_ctr(*_problem,i),rp_problem_box(*_problem)))
        {
            sat = 0;
        }
        else ++i;
    }

    if (sat)
    {
        // Insertion of the initial box in the search structure
        _boxes.insert(rp_problem_box(*_problem));

        // Management of improvement factor
        if ((c.nra_icp_improve>=0.0) && (c.nra_icp_improve<=100.0))
        {
            _improve = 1.0 - c.nra_icp_improve / 100.0;
        }
        else
        {
            _improve = 0.875;  /* 12.5% */
        }
        _propag->set_improve(_improve);

        // Creation of the operators and insertion in the propagator
        rp_hybrid_factory hfact(_improve);
        hfact.apply(_problem, *_propag);

        rp_domain_factory dfact;
        dfact.apply(_problem, *_propag);

        rp_newton_factory nfact(_improve);
        nfact.apply(_problem, *_propag);

        //rp_3b_factory bfact(_improve);
        //bfact.apply(p,_propag);

        // Used for round-robin strategy: last variable split
        rp_box_set_split(_boxes.get(),-1);//sean: why is the last variable -1? oh, must be length - this number
    }
    else
    {
        rp_box_set_empty(rp_problem_box(*_problem));
    }
}

rp_problem* icp_solver::create_rp_problem(const vector<Enode*> & stack,
                                          map<Enode*, pair<double, double> > & env)
{
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

        rp_union_interval u;
        rp_union_create(&u);
        rp_union_insert(u,
                        rp_box_elem(rp_problem_box(*result),
                                    rp_id));
        rp_union_copy(rp_variable_domain(*_v),u);
        rp_union_destroy(&u);

        rp_variable_set_real(*_v);
        rp_variable_precision(*_v) = _config.nra_precision;

        _enode_to_rp_id[key] = rp_id;

        if(_config.nra_verbose) {
            cerr << "Key: " << name << "\t"
                 << "value : [" << lb << ", " << ub << "] \t"
                 << "precision : " << _config.nra_precision << "\t"
                 << "rp_id: " << rp_id << endl;
        }
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
            if(_config.nra_verbose) {
                cerr << "Constraint: "
                     << (l->getPolarity() == l_True ? " " : "Not")
                     << l << endl;
                cerr << "          : " << temp_string << endl;
            }

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
        }
    }
    return result;
}

icp_solver::~icp_solver()
{
    rp_delete(_vselect);
    rp_delete(_dsplit);
    rp_reset_library();
    rp_problem_destroy(_problem);
}

bool icp_solver::prop_with_ODE()
{
    if (_propag->apply(_boxes.get())) {
        if(_config.nra_contain_ODE) {
            rp_box current_box = _boxes.get();

            int max = 1;
            vector< set< Enode* > > diff_vec(max);

            // 1. Collect All the ODE Vars
            // For each enode in the stack
            for(vector<Enode*>::const_iterator stack_ite = _stack.begin();
                stack_ite != _stack.end();
                stack_ite++)
            {
                set < Enode* > ode_vars = _enode_to_vars[*stack_ite];
                for(set<Enode*>::iterator ite = ode_vars.begin();
                    ite != ode_vars.end();
                    ite++)
                {
                    int diff_group = (*ite)->getODEgroup();
                    if(_config.nra_verbose) {
                        cerr << "ode_var: " << *ite << endl;
                        cerr << "diff_group: " << diff_group << ", max: " << max << endl;
                    }
                    if(diff_group >= max) {
                        if(_config.nra_verbose) {
                            cerr << "diff_group: " << diff_group << " we do resize" << endl;
                        }
                        diff_vec.resize(diff_group + 1);
                        max = diff_group;
                        if(_config.nra_verbose) {
                            cerr << "max: " << max << endl;
                        }
                    }
                    if(diff_vec[diff_group].empty()) {
                        if(_config.nra_verbose) {
                            cerr << "diff_vec[" << diff_group << "] is empty!!" << endl;
                        }
                    }
                    diff_vec[diff_group].insert(*ite);

                    if(_config.nra_verbose) {
                        cerr << "diff_group inserted: " << diff_group << endl;
                    }
                }
            }

            for(int i = 1; i <= max; i++)
            {
                if(_config.nra_verbose) {
                    cerr << "solve ode group: " << i << endl;
                }
                set<Enode*> current_ode_vars = diff_vec[i];

                /* The size of ODE_Vars should be even */
                if (current_ode_vars.size() % 2 == 1) {
                    return false;
                }

                for(set<Enode*>::iterator ite = current_ode_vars.begin();
                    ite != current_ode_vars.end();
                    ite++)
                {
                    if(current_ode_vars.find((*ite)->getODEopposite()) == current_ode_vars.end())
                    {
                        return false;
                    }
                }

                if(!current_ode_vars.empty()) {
                    if(_config.nra_verbose) {
                        cerr << "Inside of current ODEs" << endl;
                    }
                    for(set<Enode*>::iterator ite = current_ode_vars.begin();
                        ite != current_ode_vars.end();
                        ite++)
                    {
                        if(_config.nra_verbose) {
                            cerr << "Name: " << (*ite)->getCar()->getName() << endl;
                        }
                    }
                    ode_solver odeSolver(i, _config, current_ode_vars, current_box, _enode_to_rp_id);

                    if(_config.nra_verbose) {
                        cerr << "Before_Backward" << endl;
                        pprint_vars(cerr, *_problem, _boxes.get());
                        cerr << "!!!!!!!!!!Solving ODE (Backward)" << endl;
                    }

                    if (!odeSolver.solve_backward())
                        return false;

                    if(_config.nra_verbose) {
                        cerr << "After_Backward" << endl;
                        pprint_vars(cerr, *_problem, _boxes.get());
                        cerr << "!!!!!!!!!!Solving ODE (Forward)" << endl;
                    }

                    if (!odeSolver.solve_forward())
                        return false;

                    if(_config.nra_verbose) {
                        cerr << "After_FORWARD" << endl;
                        pprint_vars(cerr, *_problem, _boxes.get());
                    }


                }
            }
            return true;
        }
        else {
            return true;
        }
    }
    return false;
}

rp_box icp_solver::compute_next()
{
    if (_sol>0)
    {
        _boxes.remove();
    }
    while (!_boxes.empty())
    {
        if (prop_with_ODE())//sean: here it is! propagation before split!!!
        {
            int i;
            if ((i=_vselect->apply(_boxes.get()))>=0)
            {
                ++_nsplit;
                _dsplit->apply(_boxes,i);

                _config.nra_proof_out << endl
                           << "[branched on x" << i << "]"
                           << endl;
                pprint_vars(_config.nra_proof_out, *_problem, _boxes.get());
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
            _config.nra_proof_out << "[conflict detected]" << endl;
            _boxes.remove();
        }
    }
    return( NULL );
}

bool icp_solver::solve()
{
    bool ret = false;

    if(_config.nra_contain_ODE && _config.nra_json) {
        _config.nra_json_out << "[" << endl;
        _config.nra_json_out << "[]" << endl;
    }

    if(_config.nra_proof) {
        output_problem();
    }

    if (rp_box_empty(rp_problem_box(*_problem)))
    {
        if(_config.nra_verbose) {
            cerr << "Unfeasibility detected before solving";
        }

        /* TODO: what about explanation? */
        _explanation.clear();
        copy(_stack.begin(),
             _stack.end(),
             back_inserter(_explanation));
        ret = false;
    }
    else
    {
        rp_box b;
        if ((b=compute_next())!=NULL)
        {
            /* SAT */
            if(_config.nra_verbose) {
                cerr << "SAT with the following box:" << endl;
                pprint_vars(cerr, *_problem, b);
                cerr << endl;
            }
            if(_config.nra_proof) {
                _config.nra_proof_out << "SAT with the following box:" << endl;
                pprint_vars(_config.nra_proof_out, *_problem, b);
                _config.nra_proof_out << endl;
            }
            ret = true;
        }
        else {
            /* UNSAT */
            /* TODO: what about explanation? */
            // _proof_out << "[conflict detected]" << endl;
            if(_config.nra_verbose) {
                cerr << "UNSAT!" << endl;
            }

            _explanation.clear();
            copy(_stack.begin(),
                 _stack.end(),
                 back_inserter(_explanation));
            ret = false;
        }
    }

    if(_config.nra_contain_ODE && _config.nra_json) {
        _config.nra_json_out << "]" << endl;
    }

    return ret;
}

icp_solver& icp_solver::operator=(const icp_solver& s)
{
    return( *this );
}

void icp_solver::display_box(ostream& out, rp_box b, int digits, int mode) const
{
    if (rp_box_empty(b))
    {
        out << "empty";
    }
    else
    {
        int i;
        out << "(";
        for (i=0; i<rp_box_size(b); ++i)
        {
            //rp_interval_display(out,rp_box_elem(b,i),digits,mode);
            display_interval (out,rp_box_elem(b,i),digits,mode);
            if (i<(rp_box_size(b)-1))
            {
                out << ",";
            }
        }
        out << ")";
    }
}

void icp_solver::display_interval(ostream & out, rp_interval i, int digits, int mode) const
{
    if( rp_interval_empty(i) )
    {
        out << "empty";
        return;
    }
    if( rp_interval_point(i) )
    {
        if( rp_binf(i)>=0 )
        {
//            sprintf(out,"%.*g",digits,rp_binf(i));
            out.precision(digits);
            out << rp_binf(i);
        }
        else
        {
//            sprintf(out,"%+.*g",digits,rp_binf(i));
            out.precision(digits);
            out << rp_binf(i);
        }
    }
    else
    {
        if( mode==RP_INTERVAL_MODE_BOUND )
        {
            if( rp_binf(i)>=0 )
            {
                if (rp_binf(i)==0)
                {
                    // sprintf(out,"[0%s",RP_INTERVAL_SEPARATOR);
                    out << "[0" << RP_INTERVAL_SEPARATOR;
                }
                else
                {
                    RP_ROUND_DOWNWARD();
                    // sprintf(out,"[%.*g%s",digits,rp_binf(i),RP_INTERVAL_SEPARATOR);
                    out.precision(digits);
                    out << "[" << rp_binf(i) << RP_INTERVAL_SEPARATOR;
                }
                RP_ROUND_UPWARD();
                if( rp_bsup(i)==RP_INFINITY )
                {
                    //strcat(out,"+oo)");
                    out << "+oo";
                }
                else
                {
                    // char tmp[255];
                    //sprintf(tmp,"%.*g]",digits,rp_bsup(i));
                    //strcat(out,tmp);
                    out.precision(digits);
                    out << rp_bsup(i) << "]";
                }
            }
            else
            {
                RP_ROUND_DOWNWARD();
                if( rp_binf(i)==(-RP_INFINITY) )
                {
                    //sprintf(out,"(-oo%s",RP_INTERVAL_SEPARATOR);
                    out << "(-oo" << RP_INTERVAL_SEPARATOR;
                }
                else
                {
                    //sprintf(out,"[%+.*g%s",digits,rp_binf(i),RP_INTERVAL_SEPARATOR);
                    out.precision(digits);
                    out << "[" << rp_binf(i) << RP_INTERVAL_SEPARATOR;
                }
                RP_ROUND_UPWARD();
                if( rp_bsup(i)==RP_INFINITY )
                {
                    //strcat(out,"+oo)");
                    out << "+oo";
                }
                else
                {
                    if (rp_bsup(i)==0)
                    {
                        //strcat(out,"0]");
                        out << "0]";
                    }
                    else
                    {
                        //char tmp[255];
                        //sprintf(tmp,"%+.*g]",digits,rp_bsup(i));
                        //strcat(out,tmp);
                        out.precision(digits);
                        out << rp_bsup(i) << "]";
                    }
                }
            }
        }
    }
}

void icp_solver::pprint_vars(ostream & out, rp_problem p, rp_box b) const
{
    for(int i = 0; i < rp_problem_nvar(p); i++)
    {
        out << setw(15);
        out << rp_variable_name(rp_problem_var(p, i));
        out << " : ";
        display_interval(out, rp_box_elem(b,i), 16, RP_INTERVAL_MODE_BOUND);
        if (i != rp_problem_nvar(p) - 1)
            out << ";";
        out << endl;
    }
}

void icp_solver::output_problem() const
{
    _config.nra_proof_out.precision(16);
    _config.nra_proof_out << "Precision:" << _config.nra_precision << endl;

    // Print out all the Enode in stack
    for(vector<Enode*>::const_iterator ite = _stack.begin();
        ite != _stack.end();
        ite++)
    {
        if((*ite)->getPolarity() == l_True)
            _config.nra_proof_out << *ite << endl;
        else if ((*ite)->getPolarity() == l_False) {
            if((*ite)->isEq()) {
                /* PRINT NOTHING */
            } else {
                _config.nra_proof_out << "(not " << *ite << ")" << endl;
            }
        }
        else
            assert(0);
    }

    // Print out the initial values
    for(map<Enode*, pair<double, double> >::const_iterator ite = _env.begin();
        ite != _env.end();
        ite++)
    {
        Enode* key = (*ite).first;
        double lb =  (*ite).second.first;
        double ub =  (*ite).second.second;

        _config.nra_proof_out << key << " is in: ";
        if(lb == -numeric_limits<double>::infinity())
            _config.nra_proof_out << "(-oo";
        else {
            _config.nra_proof_out.precision(16);
            _config.nra_proof_out << "[" << lb;
        }
        _config.nra_proof_out << ", ";
        if(ub == numeric_limits<double>::infinity())
            _config.nra_proof_out << "+oo)";
        else {
            _config.nra_proof_out.precision(16);
            _config.nra_proof_out << ub << "]";
        }
        _config.nra_proof_out << ";" << endl;
    }
}


// return true  if the box is non-empty after propagation
//        false if the box is *empty* after propagation
bool icp_solver::prop()
{
    bool result = false;

    if(_config.nra_proof) {
        output_problem();
    }

    if (_sol>0)
    {
        _boxes.remove();
    }
    if(!_boxes.empty())
    {
        result = _propag->apply(_boxes.get());
    }

    if(!result) {
        // UNSAT
        // Added for dReal2
        _config.nra_proof_out << "[conflict detected]" << endl;

        // TODO: better explanation
        _explanation.clear();
        copy(_stack.begin(),
             _stack.end(),
             back_inserter(_explanation));
    } else {
        // SAT
        // Update Env
        // ======================================
        // Create rp_variable for each var in env
        // ======================================
        for(map<Enode*, pair<double, double> >::const_iterator ite = _env.begin();
            ite != _env.end();
            ite++)
        {
            Enode* key = (*ite).first;
            //double lb =  (*ite).second.first;
            //double ub =  (*ite).second.second;
            int rp_id = _enode_to_rp_id[key];
            _env[key] = make_pair(rp_binf(rp_box_elem(_boxes.get(), rp_id)),
                                  rp_bsup(rp_box_elem(_boxes.get(), rp_id)));
        }
//        cerr << "Incomplete Check: SAT" << endl;
        _config.nra_proof_out << "HOLE" << endl;

    }
    return result;
}
