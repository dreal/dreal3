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
using namespace std;

icp_solver::icp_solver(SMTConfig& c,
                       const vector<Enode*> & stack,
                       map<Enode*, pair<double, double> > & env,
                       vector<Enode*> & exp,
                       double improve,
                       double p
    )
    :
    _proof_out(c.proof_out),
    _verbose(c.nra_verbose),
    _proof(c.nra_proof),
    _stack(stack),
    _env(env),
    _boxes(env.size()), //number of variables
    _propag(NULL),
    _ep(NULL),
    _sol(0),
    _nsplit(0),
    _explanation(exp),
    _precision(p)
{
    rp_init_library();
    _problem = create_rp_problem(stack, env);

    rp_selector * _vselect;
    rp_new( _vselect, rp_selector_roundrobin, (_problem) );
    rp_splitter * _dsplit;
    rp_new( _dsplit, rp_splitter_mixed, (_problem) );

    _propag = new rp_propagator(_problem);

//    solver = new rp_bpsolver(_problem,improve,_vselect,_dsplit); //,prover);

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
        if ((improve>=0.0) && (improve<=100.0))
        {
            _improve = 1.0-improve/100.0;
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

        rp_variable_precision(*_v) = _precision;

        enode_to_rp_id[key] = rp_id;

        if(_verbose) {
            cerr << "Key: " << name << "\t"
                 << "value : [" << lb << ", " << ub << "] \t"
                 << "precision : " << _precision << "\t"
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

            if(_verbose) {
                cerr << "Constraint: "
                     << (l->getPolarity() == l_True ? " " : "Not")
                     << l << endl;
                cerr << "          : " << temp_string << endl;
            }
        }
    }
    return result;
}

icp_solver::~icp_solver()
{
    rp_problem_destroy(_problem);
    rp_delete(_vselect);
    rp_delete(_dsplit);
    rp_reset_library();
//    delete solver;
}


rp_box icp_solver::compute_next()
{
    if (_sol>0)
    {
        _boxes.remove();
    }
    while (!_boxes.empty())
    {
        if (_propag->apply(_boxes.get()))//sean: here it is! propagation before split!!!
        {
            int i;
            if ((i=_vselect->apply(_boxes.get()))>=0)
            {
                ++_nsplit;
                _dsplit->apply(_boxes,i);

                _proof_out << endl
                           << "[branched on x" << i << "]"
                           << endl;
                pprint_vars(_proof_out, *_problem, _boxes.get());
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
            _proof_out << "[conflict detected]" << endl;
            _boxes.remove();
        }
    }
    return( NULL );
}

bool icp_solver::solve()
{
    if(_proof) {
        _proof_out << "Precision:" << _precision << endl;

        // Print out all the Enode in stack
        for(vector<Enode*>::const_iterator ite = _stack.begin();
            ite != _stack.end();
            ite++)
        {
            if((*ite)->getPolarity() == l_True)
                _proof_out << *ite << endl;
            else if ((*ite)->getPolarity() == l_False) {
                if((*ite)->isEq()) {
                    /* PRINT NOTHING */
                } else {
                    _proof_out << "(not " << *ite << ")" << endl;
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

            _proof_out << key << " is in: ";
            if(lb == -numeric_limits<double>::infinity())
                _proof_out << "(-oo";
            else
                _proof_out << "[" << lb;
            _proof_out << ", ";
            if(ub == numeric_limits<double>::infinity())
                _proof_out << "+oo)";
            else
                _proof_out << ub << "]";
            _proof_out << ";" << endl;
        }
    }

    if (rp_box_empty(rp_problem_box(*_problem)))
    {
        if(_verbose) {
            cerr << "Unfeasibility detected before solving";
        }

        /* TODO: what about explanation? */
        copy(_stack.begin(),
             _stack.end(),
             back_inserter(_explanation));

        return false;
    }
    else
    {
        rp_box b;
        if ((b=compute_next())!=NULL)
        {
            /* SAT */
            if(_verbose) {
                cerr << "SAT with the following box:" << endl;
            }
            if(_proof) {
                display_box(_proof_out, b, 8, RP_INTERVAL_MODE_BOUND);
                _proof_out << endl;
            }
            return true;
        }
        else {
            /* UNSAT */
            /* TODO: what about explanation? */
            // _proof_out << "[conflict detected]" << endl;
            if(_verbose) {
                cerr << "UNSAT!" << endl;
            }
            copy(_stack.begin(),
                 _stack.end(),
                 back_inserter(_explanation));
            return false;
        }
    }
}

icp_solver& icp_solver::operator=(const icp_solver& s)
{
    return( *this );
}

void icp_solver::display_box(ostream& out, rp_box b, int digits, int mode)
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

void icp_solver::display_interval(ostream & out, rp_interval i, int digits, int mode)
{
    double mid, minerror, maxerror;
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
                    out << "[" << RP_INTERVAL_SEPARATOR;
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
                    char tmp[255];
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
        else
        {
            if( (rp_binf(i)==(-RP_INFINITY)) && (rp_bsup(i)==RP_INFINITY) )
            {
                //sprintf(out,"0.0+(-oo%s+oo)",RP_INTERVAL_SEPARATOR);
                out << "0.0+(-oo" << RP_INTERVAL_SEPARATOR << "+oo";
                return;
            }
            if( rp_binf(i)==(-RP_INFINITY) )
            {
                RP_ROUND_DOWNWARD();
                mid = rp_split_center(RP_MIN_DOUBLE,rp_bsup(i));
                minerror = -RP_INFINITY;
                RP_ROUND_UPWARD();
                maxerror = rp_bsup(i) - mid;
            }
            else if( rp_bsup(i)==RP_INFINITY )
            {
                RP_ROUND_DOWNWARD();
                mid = rp_split_center(rp_binf(i),RP_MAX_DOUBLE);
                minerror = rp_binf(i) - mid;
                RP_ROUND_UPWARD();
                maxerror = RP_INFINITY;
            }
            else
            {
                RP_ROUND_DOWNWARD();
                mid = rp_interval_midpoint(i);
                minerror = rp_binf(i) - mid;
                RP_ROUND_UPWARD();
                maxerror = rp_bsup(i) - mid;
            }

            if( mid>=0 )
            {
                //sprintf(out,"%.*g+",digits,mid);
                out.precision(digits);
                out << mid;
            }
            else
            {
                //sprintf(out,"%+.*g+",digits,mid);
                out.precision(digits);
                out << mid;
            }
            if( minerror==(-RP_INFINITY) )
            {
                //char tmp[255];
                //sprintf(tmp,"(-oo%s%+.4g]",RP_INTERVAL_SEPARATOR,maxerror);
                //strcat(out,tmp);
                out << "(-oo" << RP_INTERVAL_SEPARATOR << maxerror;
            }
            else if( maxerror==RP_INFINITY )
            {
                //char tmp[255];
                RP_ROUND_DOWNWARD();
                //sprintf(tmp,"[%+.4g%s+oo)",minerror,RP_INTERVAL_SEPARATOR);
                //strcat(out,tmp);
                out << "[" << minerror << RP_INTERVAL_SEPARATOR << "+oo)";
            }
            else
            {
                //char tmp[255];
                RP_ROUND_DOWNWARD();
                //sprintf(tmp,"[%+.4g%s",minerror,RP_INTERVAL_SEPARATOR);
                //strcat(out,tmp);
                out << "[" << minerror << RP_INTERVAL_SEPARATOR;
                RP_ROUND_UPWARD();
                //sprintf(tmp,"%+.4g]",maxerror);
                //strcat(out,tmp);
                out << maxerror << "]";
            }
        }
    }
}

void icp_solver::pprint_vars(ostream & out, rp_problem p, rp_box b)
{
    for(int i = 0; i < rp_problem_nvar(p); i++)
    {
        out << rp_variable_name(rp_problem_var(p, i));
        out << " is in: ";
        display_interval(_proof_out, rp_box_elem(b,i), 6, RP_INTERVAL_MODE_BOUND);
        if (i != rp_problem_nvar(p) - 1)
            out << ";";
        out << endl;
    }
}
