/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <sstream>
#include <string>
#include <unordered_set>
#include "util/logging.h"
#include "util/interval.h"
#include "util/string.h"
#include "dsolvers/icp_solver.h"
#include "dsolvers/nra_solver.h"
#include "dsolvers/heuristics/heuristic.h"

using std::pair;
using std::boolalpha;
using std::unordered_set;

namespace dreal {
nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                       vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver (i, n, c, e, t, x, d, s), m_decisions(0) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
    m_heuristic.initialize(c);
}

nra_solver::~nra_solver() { }

// `inform` sets up env (mapping from variables(enode) in literals to their [lb, ub])
lbool nra_solver::inform(Enode * e) {
    unordered_set<Enode *> const & vars = e->get_vars();
    static stringstream ss;
    for (auto const & v : vars) {
        double const lb = v->getLowerBound();
        double const ub = v->getUpperBound();
        m_env.insert(v, interval(lb, ub));
        if (DREAL_LOG_DEBUG_IS_ON) {
            ss << v << " ";
        }
    }
    if (config.nra_bmc_heuristic.compare("") != 0)
        m_heuristic.inform(e);
    if (DREAL_LOG_DEBUG_IS_ON) {
        DREAL_LOG_DEBUG << "nra_solver::inform: " << e << " with polarity " << e->getPolarity().toInt()
                        << " vars = { " << ss.str() << "}";
        ss.str(string());
    }
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check"
//
// assertLit adds a literal(e) to stack of asserted literals.
bool nra_solver::assertLit (Enode * e, bool reason) {
    DREAL_LOG_DEBUG << "nra_solver::assertLit: " << e
                    << ", reason: " << boolalpha << reason
                    << ", polarity: " << e->getPolarity().toInt();
    (void)reason;
    assert(e);
    assert(belongsToT(e));
    assert(e->hasPolarity());
    assert(e->getPolarity() == l_False || e->getPolarity() == l_True);
    if (e->isDeduced() && e->getPolarity() == e->getDeduced() && e->getDedIndex() == id) {
        DREAL_LOG_DEBUG << "nra_solver::assertLit: " << e << " is deduced" << e;
        return true;
    }
    m_stack.push_back(e);

    if  (config.nra_bmc_heuristic.compare("") != 0 && m_heuristic.is_initialized()) {
        suggestions.clear();
        m_heuristic.getSuggestions(suggestions, m_stack);
    }

    return true;
}

// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint () {
    DREAL_LOG_DEBUG << "nra_solver::pushBacktrackPoint " << m_stack.size();
    m_env.push();
    m_stack.push();
}

// Restore a previous state. You can now retrieve the size of the
// stack when you pushed the last backtrack point. You have to
// implement the necessary backtrack operations (see for instance
// backtrackToStackSize() in EgraphSolver) Also make sure you clean
// the deductions you did not communicate
void nra_solver::popBacktrackPoint () {
    DREAL_LOG_DEBUG << "nra_solver::popBacktrackPoint";
    m_stack.pop();
    m_env.pop();
    m_heuristic.resetSuggestions();
}

// Check for consistency.
// If flag is set make sure you run a complete check
bool nra_solver::check(bool complete) {
    DREAL_LOG_INFO << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ")";
    DREAL_LOG_DEBUG << "nra_solver::check: env = ";
    DREAL_LOG_DEBUG << m_env;
    DREAL_LOG_DEBUG << "nra_solver::check: stack = ";
    DREAL_LOG_DEBUG << m_stack;
    bool result = true;
    icp_solver solver(config, egraph, sstore, m_stack, m_env, explanation, complete);
    if (!complete) {
        // Incomplete Check
        result = solver.prop();
    } else {
        // Complete Check
        result = solver.solve();
    }
    DREAL_LOG_INFO << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ")"
                   << " result = " << boolalpha << result;
    if (!result) {
        if (DREAL_LOG_INFO_IS_ON) {
            DREAL_LOG_INFO << "nra_solver::check: explanation provided:";
            for (Enode * const e : explanation) {
                DREAL_LOG_INFO << "\t" << (e->getPolarity() == l_False ? "!" : "") << e;
            }
        }
    }
    // Only compute the heuristic after first check.  The first check is after
    // all level 0 literals have been asserted and the initial and goal modes
    // will be known
    if (config.nra_bmc_heuristic.compare("") != 0 && !m_heuristic.is_initialized()) {
        suggestions.clear();
        m_heuristic.getSuggestions(suggestions, m_stack);
    }

    // Print out JSON
#ifdef ODE_ENABLED
    if (complete && result && config.nra_ODE_contain && config.nra_json) {
        solver.print_json(config.nra_json_out);
    }
#endif
    DREAL_LOG_INFO << "============================";
    m_decisions += solver.nsplit();
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
    DREAL_LOG_DEBUG << "nra_solver::computeModel" << endl;
}

#ifdef PRODUCE_PROOF
Enode * nra_solver::getInterpolants() {
    return nullptr;
}
#endif
}
