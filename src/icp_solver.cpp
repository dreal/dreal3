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
    solver = new rp_bpsolver(_problem,improve,_vselect,_dsplit); //,prover);
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
    rp_reset_library();
    delete solver;
}

rp_box icp_solver::prop()
{
    if(_verbose) {
        cerr << "icp_solver::prop" << endl;
    }
    assert(_boxes.size() == 1);

    _propag->apply(_boxes.get());
    return( _boxes.get() );
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
             std::back_inserter(_explanation));

        return false;
    }
    else
    {
        rp_box b;
        if ((b=solver->compute_next())!=NULL)
        {
            /* SAT */
            if(_verbose) {
                cerr << "SAT with the following box:" << endl;
            }
            if(_proof) {
                rp_box_display_simple(b);
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
                 std::back_inserter(_explanation));
            return false;
        }
    }
}

rp_box icp_solver::compute_next(bool hasDiff)
{
    if(_proof) {
        _proof_out<<"------------------"<<endl;
        _proof_out<<"The interval pruning and branching trace is:";
    }

    if (_sol>0) //if you already have a solution, discard this obtained solution box and backtrack
    {
        _boxes.remove();
    }
    while (!_boxes.empty()) //if there's no more box on the stack, you are done with compute_next
    {
        if (_propag->apply(_boxes.get()))
        {
            int i;
            if ((i=_vselect->apply(_boxes.get()))>=0)
            {
                ++_nsplit;
                _dsplit->apply(_boxes,i);
                //monitoring
                if(_proof) {
                    _proof_out << endl
                               << "[branched on x" << i << "]"
                               <<endl;
                }
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
            if(_proof) {
                _proof_out<<"[conflict detected]"<<endl;
            }
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
