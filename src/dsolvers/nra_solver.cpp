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
#include <boost/log/core.hpp>
#include <boost/log/trivial.hpp>
#include "dsolvers/icp_solver.h"
#include "dsolvers/nra_solver.h"

using std::pair;
namespace logging = boost::log;

nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                       vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver (i, n, c, e, t, x, d, s) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
}

nra_solver::~nra_solver() { }

// Collect all the variables appeared in a literal e
unordered_set<Enode *> nra_solver::get_vars (Enode * const e) {
    unordered_set<Enode *> result;
    Enode * p = nullptr;
    if ( e->isSymb()) { /* do nothing */ }
    else if (e->isNumb()) { /* do nothing */ }
    else if (e->isTerm()) {
        if (e -> isVar()) { result.insert(e); }
        p = e;
        while (!p->isEnil()) {
            unordered_set<Enode *> const & tmp_set = get_vars(p->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    } else if (e->isList()) {
        p = e;
        while (!p->isEnil()) {
            unordered_set<Enode *> const & tmp_set = get_vars(p->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    } else if (e->isDef()) { /* do nothing */ }
    else if (e->isEnil()) { /* do nothing */ }
    else opensmt_error("unknown case value");
    return result;
}

// `inform` does two operations:
// 1. set up env (mapping from enode to its [lb, ub])
// 2. set up _enode_to_vars (mapping from an expr to all the
//    variables in it)
lbool nra_solver::inform(Enode * e) {
    BOOST_LOG_TRIVIAL(debug) << "===============";
    BOOST_LOG_TRIVIAL(debug) << "nra_solver::inform: " << e << " with polarity " << e->getPolarity().toInt();
    BOOST_LOG_TRIVIAL(debug) << "===============";
    unordered_set<Enode *> const & vars = get_vars(e);
    unordered_set<Enode *> ode_vars;
    for (auto const & v : vars) {
        BOOST_LOG_TRIVIAL(debug) << v;
        double const lb = v->getLowerBound();
        double const ub = v->getUpperBound();
        m_env.insert(v, make_pair(lb, ub));

        // Collect ODE Vars in e
        if (config.nra_contain_ODE && v->getODEtimevar() != nullptr && v->getODEgroup() > 0) {
            BOOST_LOG_TRIVIAL(debug) << "Add " << v << " to " << "group: " << v->getODEgroup();
            ode_vars.insert(v);
        }
    }
    if (config.nra_contain_ODE) {
        m_odevars_in_lit.insert(make_pair(e, ode_vars));
    }
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check"
//
// assertLit adds a literal(e) to stack of asserted literals.
bool nra_solver::assertLit (Enode * e, bool reason) {
    BOOST_LOG_TRIVIAL(debug) << "===============";
    BOOST_LOG_TRIVIAL(debug) << "nra_solver::assertLit: " << e
                             << ", reason: " << (reason ? "true" : "false")
                             << ", polarity: " << e->getPolarity().toInt();
    BOOST_LOG_TRIVIAL(debug) << "===============";
    (void)reason;
    assert(e);
    assert(belongsToT(e));
    assert(e->hasPolarity());
    assert(e->getPolarity() == l_False || e->getPolarity() == l_True);
    if (e->isDeduced() && e->getPolarity() == e->getDeduced() && e->getDedIndex() == id) {
        BOOST_LOG_TRIVIAL(debug) << "nra_solver::assertLit: DEDUCED" << e;
        return true;
    }
    m_stack.push_back(e);
    return true;
}

// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint () {
    BOOST_LOG_TRIVIAL(debug) << "===============";
    BOOST_LOG_TRIVIAL(debug) << "nra_solver::pushBacktrackPoint " << m_stack.size();
    BOOST_LOG_TRIVIAL(debug) << "===============";
    m_env.push();
    m_stack.push();
}

// Restore a previous state. You can now retrieve the size of the
// stack when you pushed the last backtrack point. You have to
// implement the necessary backtrack operations (see for instance
// backtrackToStackSize() in EgraphSolver) Also make sure you clean
// the deductions you did not communicate
void nra_solver::popBacktrackPoint () {
    BOOST_LOG_TRIVIAL(debug) << "================";
    BOOST_LOG_TRIVIAL(debug) << "nra_solver::popBacktrackPoint";
    BOOST_LOG_TRIVIAL(debug) << "================";
    m_stack.pop();
    m_env.pop();
}

// Check for consistency.
// If flag is set make sure you run a complete check
bool nra_solver::check(bool complete) {
    BOOST_LOG_TRIVIAL(debug) << "================";
    BOOST_LOG_TRIVIAL(debug) << "nra_solver::check " << (complete ? "complete" : "incomplete");
    BOOST_LOG_TRIVIAL(debug) << m_env;
    BOOST_LOG_TRIVIAL(debug) << m_stack;
    BOOST_LOG_TRIVIAL(debug) << "================";
    BOOST_LOG_TRIVIAL(info) << "nra_solver::check " << (complete ? "complete" : "incomplete");
    bool result = true;
    icp_solver solver(config, m_stack, m_env, explanation, m_odevars_in_lit, complete);
    if (!complete) {
        // Incomplete Check
        BOOST_LOG_TRIVIAL(debug) << "Before Prop" << endl
                                 << m_env;

        result = solver.prop();

        BOOST_LOG_TRIVIAL(debug) << "After Prop" << endl
                                 << m_env;
    } else {
        result = solver.solve();
    }
    if (!result) {
        BOOST_LOG_TRIVIAL(debug) << "#explanation provided: ";
        for (Enode * const e : explanation) {
            BOOST_LOG_TRIVIAL(debug) << e <<" with polarity " << toInt((e)->getPolarity()) << " ";
        }
    }
    // Print out JSON
    if (complete && result && config.nra_contain_ODE && config.nra_json) {
        BOOST_LOG_TRIVIAL(info) << "nra_solver:: print json";
        solver.print_json(config.nra_json_out);
    }
    BOOST_LOG_TRIVIAL(info) << "nra_solver::check " << (complete ? "complete" : "incomplete")
                            << "\t result = " << result;
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
    BOOST_LOG_TRIVIAL(debug) << "computeModel" << endl;
}

#ifdef PRODUCE_PROOF
Enode * nra_solver::getInterpolants() {
    return nullptr;
}
#endif
