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

#include <utility>
#include <boost/algorithm/string/predicate.hpp>
#include "dsolvers/nra_solver.h"
#include "dsolvers/icp_solver.h"

using std::pair;
using boost::starts_with;

nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                     vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver (i, n, c, e, t, x, d, s) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
}

nra_solver::~nra_solver() { }

// Collect all the variables appeared in a literal e
set<Enode *> nra_solver::get_variables (Enode * const e) {
    set<Enode *> result;
    Enode * p = nullptr;
    if ( e->isSymb()) { /* do nothing */ }
    else if (e->isNumb()) { /* do nothing */ }
    else if (e->isTerm()) {
        if (e -> isVar()) { result.insert(e); }
        p = e;
        while(!p->isEnil()) {
            set<Enode *> const & tmp_set = get_variables(p->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    } else if (e->isList()) {
        p = e;
        while (!p->isEnil()) {
            set<Enode *> const & tmp_set = get_variables(p->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    } else if (e->isDef()) { /* do nothing */ }
    else if (e->isEnil()) { /* do nothing */ }
    else opensmt_error("unknown case value");
    return result;
}

// The solver is informed of the existence of atom e. It might be
// useful for initializing the solver's data structures. This function
// is called before the actual solving starts.
//
// `inform` does two operations:
// 1. set up env (mapping from enode to its [lb, ub])
// 2. set up _enode_to_vars (mapping from an expr to all the
//    variables in it)
lbool nra_solver::inform(Enode * e) {
    if (config.nra_verbose) {
        cerr << "================================================================" << endl
             << "nra_solver::inform: " << e
             << " with polarity " << e->getPolarity().toInt() << endl
             << "================================================================" << endl;
    }
    set<Enode *> const & vars_in_lit = get_variables(e);
    set<Enode *> ode_vars_in_lit;
    for (auto const & var : vars_in_lit) {
        if (config.nra_verbose) { cerr << var << endl; }
        double const lb = var->getLowerBound();
        double const ub = var->getUpperBound();
        m_env.insert(var, make_pair(lb, ub));

        // Collect ODE Vars in e
        if (config.nra_contain_ODE && var->getODEtimevar() != nullptr && var->getODEgroup() > 0) {
            if (config.nra_verbose) {
                cerr << "Add " << var << " in the bag!!!! " << endl;
                cerr << "\t Group: " << var->getODEgroup() << endl;
            }
            ode_vars_in_lit.insert(var);
        }
    }
    if (config.nra_contain_ODE) {
        m_vars_in_lit.insert(make_pair(e, ode_vars_in_lit));
    }
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check"
//
// assertLit adds a literal(e) to stack of asserted literals.
bool nra_solver::assertLit (Enode * e, bool reason) {
    if (config.nra_verbose) {
        cerr << "================================================================" << endl
             << "nra_solver::assertLit: " << e
             << ", reason: " << (reason ? "true" : "false")
             << ", polarity: " << e->getPolarity().toInt() << endl
             << "================================================================" << endl;
    }
    (void)reason;
    assert(e);
    assert(belongsToT(e));
    assert(e->hasPolarity());
    assert(e->getPolarity() == l_False || e->getPolarity() == l_True);
    if (e->isDeduced() && e->getPolarity() == e->getDeduced() && e->getDedIndex() == id) {
        if (config.nra_verbose) {
            cerr << "nra_solver::assertLit: DEDUCED" << e << endl;
        }
        return true;
    }
    m_stack.push_back(e);
    return true;
}

// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint () {
    if (config.nra_verbose) {
        cerr << "================================================================" << endl
             << "nra_solver::pushBacktrackPoint " << m_stack.size() << endl;
    }
    m_env.push();
    m_stack.push();
    if (config.nra_verbose) {
        cerr << "================================================================" << endl;
    }
}

// Restore a previous state. You can now retrieve the size of the
// stack when you pushed the last backtrack point. You have to
// implement the necessary backtrack operations (see for instance
// backtrackToStackSize() in EgraphSolver) Also make sure you clean
// the deductions you did not communicate
void nra_solver::popBacktrackPoint () {
    if (config.nra_verbose) {
        cerr << "================================================================" << endl
             << "nra_solver::popBacktrackPoint" << endl;
    }
    m_stack.pop();
    m_env.pop();
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool nra_solver::check(bool complete) {
    if (config.nra_verbose) {
        cerr << "================================================================" << endl;
        cerr << "nra_solver::check " << (complete ? "complete" : "incomplete") << endl;
        for (auto ite = m_env.begin(); ite != m_env.end(); ite++) {
            Enode * key = (*ite).first;
            double lb =  (*ite).second.first;
            double ub =  (*ite).second.second;
            if (starts_with(key->getCar()->getName(), "mode_")) {
                cerr << "Key: " << key << "\t Value: [" << lb << ", " << ub << "]" << endl;
            }
        }
        cerr << "================================================================" << endl;
    }
    bool result = true;
    if (config.nra_verbose) {
        std::cerr << m_stack << std::endl;
        std::cerr << m_env << std::endl;
    }
    icp_solver solver(config, m_stack, m_env, explanation, m_vars_in_lit);
    if (!complete) {
        // Incomplete Check
        if (config.nra_verbose) {
            cerr << "Incomplete Check" << endl;
            cerr << "Before Prop" << endl;
            std::cerr << m_env << std::endl;
        }
        result = solver.prop();
        if (config.nra_verbose) {
            cerr << "After Prop" << endl;
            std::cerr << m_env << std::endl;
        }
    } else {
        result = solver.solve();
    }

    if (config.nra_verbose && !result) {
        cerr << "#explanation provided: ";
        for (Enode * const e : explanation) {
            cerr << e <<" with polarity " << toInt((e)->getPolarity()) << " ";
        }
        cerr << endl;
    }
    // Print out JSON
    if (complete && result && config.nra_contain_ODE && config.nra_json) {
        solver.print_json(config.nra_json_out);
    }
    return result;
}

// Return true if the enode belongs to this theory. You should examine
// the structure of the node to see if it matches the theory operators
bool nra_solver::belongsToT(Enode * e) {
    (void)e;
    assert(e);
    return true;
}

// Copy the model into enode's data
void nra_solver::computeModel() {
    if (config.nra_verbose) {
        cerr << "computeModel" << endl;
    }
}

#ifdef PRODUCE_PROOF
Enode * nra_solver::getInterpolants() {
    return nullptr;
}
#endif
