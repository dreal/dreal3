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

#include <iomanip>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <utility>
#include "util/logging.h"
#include "util/interval.h"
#include "util/string.h"
#include "dsolvers/nra_solver.h"
#include <gflags/gflags.h>

DEFINE_bool(new_exp,             true,      "new_exp");
DEFINE_bool(show_model,          false,     "show model");
DEFINE_bool(stat,                false,     "show stat");
DEFINE_bool(hmodel,              false,     "human_readable model");
DEFINE_string(split_heuristic,  "existence", "split heuristic");

using std::setw;
using std::pair;
using std::boolalpha;
using std::unordered_set;
using std::unique_ptr;

namespace dreal {
nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                       vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver (i, n, c, e, t, x, d, s), _stat_check_incomplete(0), _stat_check_complete(0) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
    rp_init_library();
    rp_problem_create(&_rp_problem, "icp_holder");
}

nra_solver::~nra_solver() {
    rp_reset_library();
    rp_problem_destroy(&_rp_problem);
    if (FLAGS_stat) {
        DREAL_LOG_FATAL << "# Incomplete Check " << _stat_check_incomplete;
        DREAL_LOG_FATAL << "# Complete Check "   << _stat_check_complete;
    }
}

void nra_solver::create_rp_var(Enode * const v) {
    rp_variable rp_var;
    string const & name = v->getCar()->getName();
    rp_variable_create(&rp_var, name.c_str());
    int const rp_id = rp_vector_insert(rp_table_symbol_vars(rp_problem_symb(_rp_problem)), rp_var);
    // Domain
    rp_interval i;
    rp_bsup(i) = v->getUpperBound();
    rp_binf(i) = v->getLowerBound();
    rp_union_insert(rp_variable_domain(rp_var), i);
    // Type & Precision
    if (v->hasSortInt()) {
        rp_variable_set_integer(rp_var);
    } else if (v->hasSortReal()) {
        rp_variable_set_real(rp_var);
        rp_variable_precision(rp_var) = config.nra_precision;
    }
    // Update map
    _enode_to_rp_id[v] = rp_id;
    _rp_id_to_enode[rp_id] = v;
    _enode_to_rp_var[v] = rp_var;
    DREAL_LOG_INFO << "nra_solver::create_rp_var " << v << " = " << interval(i) << "\t"
                   << "rp_id = " << rp_id;
}

void nra_solver::create_rp_ctr(Enode * const l) {
    //=================== Constraint ====================
    if (l->isForallT() || l->isIntegral()) return;
    thread_local static stringstream buf_pos;
    thread_local static stringstream buf_neg;
    buf_pos.str(""); buf_pos.clear();
    buf_neg.str(""); buf_neg.clear();
    l->print_infix(buf_pos, l_True);
    l->print_infix(buf_neg, l_False);
    string const ctr_str_pos = buf_pos.str();
    string const ctr_str_neg = buf_neg.str();
    rp_constraint c_pos, c_neg;
    DREAL_LOG_INFO << "nra_solver::create_rp_ctr: constraint+: " << l;
    DREAL_LOG_INFO << "nra_solver::create_rp_ctr: constraint+: " << ctr_str_pos;
    DREAL_LOG_INFO << "nra_solver::create_rp_ctr: constraint-: " << "not" << l;
    DREAL_LOG_INFO << "nra_solver::create_rp_ctr: constraint-: " << ctr_str_neg;
    rp_parse_constraint_string(&c_pos, ctr_str_pos.c_str(), rp_problem_symb(_rp_problem));
    rp_parse_constraint_string(&c_neg, ctr_str_neg.c_str(), rp_problem_symb(_rp_problem));
    rp_ctr_set_delta(&c_pos, (l->hasPrecision() ? l->getPrecision() : config.nra_precision));
    rp_ctr_set_delta(&c_neg, (l->hasPrecision() ? l->getPrecision() : config.nra_precision));
    _enode_to_rp_ctr_pos[l] = c_pos;
    _enode_to_rp_ctr_neg[l] = c_neg;
}

vector<bool> nra_solver::get_used_constraints() {
    DREAL_LOG_DEBUG << "get_used_constraints _stack.size() = " << _stack.size();
    vector<bool> v(_stack.size());
    for (vector<bool>::size_type i = 0; i < _stack.size(); i++) {
        Enode * const l = _stack[i];
        rp_constraint const c_pos = _enode_to_rp_ctr_pos[l];
        rp_constraint const c_neg = _enode_to_rp_ctr_neg[l];
        rp_ctr_num const cnum_pos = rp_constraint_num(c_pos);
        rp_ctr_num const cnum_neg = rp_constraint_num(c_neg);
        if ((l->getPolarity() == l_True && rp_ctr_num_used(cnum_pos)) ||
            (l->getPolarity() == l_False && rp_ctr_num_used(cnum_neg))) {
            v[i] = true;
        } else {
            v[i] = false;
        }
    }
    DREAL_LOG_DEBUG << "get_used_constraints      v.size() = " << v.size();
    assert(_stack.size() == v.size());
    return v;
}
void nra_solver::set_used_constraints(vector<bool> const & v) {
    DREAL_LOG_DEBUG << "set_used_constraints _stack.size() = " << _stack.size();
    DREAL_LOG_DEBUG << "set_used_constraints      v.size() = " << v.size();
    assert(_stack.size() >= v.size());
    for (vector<bool>::size_type i = 0; i < v.size(); i++) {
        Enode * const l = _stack[i];
        if (l->getPolarity() == l_True) {
            rp_constraint const c_pos = _enode_to_rp_ctr_pos[l];
            rp_ctr_num const cnum_pos = rp_constraint_num(c_pos);
            rp_ctr_num_used(cnum_pos) = v[i];
        } else {
            rp_constraint const c_neg = _enode_to_rp_ctr_neg[l];
            rp_ctr_num const cnum_neg = rp_constraint_num(c_neg);
            rp_ctr_num_used(cnum_neg) = v[i];
        }
    }
}

void nra_solver::get_explanation() {
    assert(explanation.empty());
    if (FLAGS_new_exp) {
        DREAL_LOG_DEBUG << "nra_solver::build_explanation\t explanation.size() = "
                        << explanation.size();
        for (Enode * const l : _stack) {
            bool added = false;
            if (l->getPolarity() == l_True) {
                rp_constraint const c_pos = _enode_to_rp_ctr_pos[l];
                rp_ctr_num const cnum_pos = rp_constraint_num(c_pos);
                if (rp_ctr_num_used(cnum_pos)) {
                    explanation.push_back(l); added = true;
                }
            } else {
                rp_constraint const c_neg = _enode_to_rp_ctr_neg[l];
                rp_ctr_num const cnum_neg = rp_constraint_num(c_neg);
                if (rp_ctr_num_used(cnum_neg)) {
                    explanation.push_back(l); added = true;
                }
            }
            if (added) {
                DREAL_LOG_DEBUG << "nra_solver::build_explanation: " << l << " [ADDED]";
            } else {
                DREAL_LOG_DEBUG << "nra_solver::build_explanation: " << l << " [SKIPPED]";
            }
        }
    } else {
        explanation.assign(_stack.begin(), _stack.end());
    }
}

void nra_solver::get_deductions() {
    for (Enode * const l : _lits) {
        if (l->getPolarity() == l_Undef && !l->isDeduced()) {
            if (rp_constraint_unfeasible(_enode_to_rp_ctr_pos[l], rp_problem_box(_rp_problem))) {
                l->setDeduced(l_False, id);
                deductions.push_back(l);
                DREAL_LOG_DEBUG << "nra_solver::get_deductions: added (-) " << l;
            } else if (rp_constraint_unfeasible(_enode_to_rp_ctr_neg[l], rp_problem_box(_rp_problem))) {
                l->setDeduced(l_True, id);
                deductions.push_back(l);
                DREAL_LOG_DEBUG << "nra_solver::get_deductions: added (+)" << l;
            }
        }
    }
}

void display_interval(ostream & out, rp_interval i, int digits, bool exact) {
    static interval tmp;
    tmp.lb = rp_binf(i);
    tmp.ub = rp_bsup(i);
    tmp.print(out, digits, exact);
}

void pprint_vars(ostream & out, rp_problem p, rp_box b, bool exact) {
    for (int i = 0; i <rp_problem_nvar(p); i++) {
        out << setw(15);
        out << rp_variable_name(rp_problem_var(p, i));
        out << " : ";
        display_interval(out, rp_box_elem(b, i), 16, exact);
        out << ";" << endl;
    }
}

bool nra_solver::prop() {
    rp_propagator _propag(&_rp_problem, 10.0, config.nra_verbose, config.nra_proof_out);
    double improve = 0.875; /* 12.5% */
    if ((config.nra_icp_improve >= 0.0) && (config.nra_icp_improve <= 100.0)) {
        improve = 1.0 - config.nra_icp_improve / 100.0;
    }
    _propag.set_improve(improve);
    rp_hybrid_factory hfact(improve);
    hfact.apply(&_rp_problem, _propag);
    rp_domain_factory dfact;
    dfact.apply(&_rp_problem, _propag);
    rp_newton_factory nfact(improve);
    nfact.apply(&_rp_problem, _propag);
    bool result = _propag.apply(rp_problem_box(_rp_problem));
    if (!result) { get_explanation(); }
    return result;
}

bool nra_solver::solve() {
    rp_propagator _propag(&_rp_problem, 10.0, config.nra_verbose, config.nra_proof_out);
    double improve = 0.875; /* 12.5% */
    if ((config.nra_icp_improve >= 0.0) && (config.nra_icp_improve <= 100.0)) {
        improve = 1.0 - config.nra_icp_improve / 100.0;
    }
    _propag.set_improve(improve);
    rp_hybrid_factory hfact(improve); hfact.apply(&_rp_problem, _propag);
    rp_domain_factory dfact;          dfact.apply(&_rp_problem, _propag);
    rp_newton_factory nfact(improve); nfact.apply(&_rp_problem, _propag);
    rp_box_stack boxes(rp_box_size(rp_problem_box(_rp_problem))); /* the set of boxes during search */
    boxes.insert(rp_problem_box(_rp_problem));
    unique_ptr<rp_selector> vselect; /* selection of variable to be split */
    if (FLAGS_split_heuristic == "existence") {
        vselect = std::move(unique_ptr<rp_selector>(new rp_selector_existence(&_rp_problem)));
    } else if (FLAGS_split_heuristic == "ircmax") {
        vselect = std::move(unique_ptr<rp_selector>(new rp_selector_ircmax(&_rp_problem)));
    } else if (FLAGS_split_heuristic == "roundrobin") {
        vselect = std::move(unique_ptr<rp_selector>(new rp_selector_roundrobin(&_rp_problem)));
    } else { // By default: existence
        vselect = std::move(unique_ptr<rp_selector>(new rp_selector_existence(&_rp_problem)));
    }
    unique_ptr<rp_splitter> dsplit(new rp_splitter_bisection(&_rp_problem)); /* split function of variable domain */
    while (!boxes.empty()) {
        if (_propag.apply(boxes.get())) {
            // SAT => Split
            rp_box b = boxes.get();
            int i = vselect->apply(b);
            DREAL_LOG_DEBUG << "nra_solver::solve: split on " << i << "\t" << "box width = " << rp_box_width(b);
            if (i >= 0 && rp_interval_width(rp_box_elem(b, i)) >= config.nra_precision) {
                dsplit->apply(boxes, i);
            } else {
                if (b != nullptr) {
                    DREAL_LOG_FATAL << "precision = " << config.nra_precision;
                    DREAL_LOG_FATAL << "Last split i = " << i;
                    if (i >= 0) {
                        DREAL_LOG_FATAL << "i-th width = " << rp_interval_width(rp_box_elem(b, i));
                    }
                    if (FLAGS_show_model) {
                        pprint_vars(cout, _rp_problem, b, false);
                    }
                    if (config.nra_model) {
                        /* Open file stream */
                        config.nra_model_out.open (config.nra_model_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
                        if (config.nra_model_out.fail()) {
                            cout << "Cannot create a file: " << config.nra_model_out_name << endl;
                            exit(1);
                        } else {
                            pprint_vars(config.nra_model_out, _rp_problem, b, !FLAGS_hmodel);
                        }
                    }
                    for (Enode * const l : _stack) {
                        if (l->getPolarity() == l_True) {
                            cerr << "Assigned Literal (+):" << l << endl;
                        }
                    }
                    return true;
                }
                get_explanation();
                return false;
            }
        } else {
            // UNSAT => Remove box
            boxes.remove();
        }
    }
    get_explanation();
    return false;
}

// `inform` sets up env (mapping from variables(enode) in literals to their [lb, ub])
lbool nra_solver::inform(Enode * e) {
    _lits.push_back(e);
    unordered_set<Enode *> const vars = e->get_vars();
    for (Enode * const v : vars) {
        if (find(_vars.begin(), _vars.end(), v) == _vars.end()) {
            _vars.push_back(v);
            create_rp_var(v);
        }
    }
    create_rp_ctr(e);
    if (DREAL_LOG_DEBUG_IS_ON) {
        static stringstream ss;
        for (auto const & v : vars) { ss << v << " ";  }
        DREAL_LOG_DEBUG << "nra_solver::inform: " << e << " with polarity " << e->getPolarity().toInt()
                        << " vars = { " << ss.str() << "}";
        ss.str(string());
    }
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check" assertLit adds a literal(e) to
// stack of asserted literals.
bool nra_solver::assertLit (Enode * e, bool reason) {
    DREAL_LOG_INFO << "nra_solver::assertLit: " << e
                   << ", reason: " << boolalpha << reason
                   << ", polarity: " << e->getPolarity().toInt()
                   << ", level: " << _stack.size()
                   << ", ded.size = " << deductions.size();

    (void)reason;
    assert(e);
    assert(belongsToT(e));
    assert(e->hasPolarity());
    assert(e->getPolarity() == l_False || e->getPolarity() == l_True);
    if (e->isDeduced() && e->getPolarity() == e->getDeduced() && e->getDedIndex() == id) {
        DREAL_LOG_INFO << "nra_solver::assertLit: " << e << " is deduced";
        return true;
    }
    _stack.push_back(e);
    rp_constraint c;
    if (e->getPolarity() == l_True) { c = _enode_to_rp_ctr_pos[e];
    } else { c = _enode_to_rp_ctr_neg[e]; }
    if (rp_constraint_unfeasible(c, rp_problem_box(_rp_problem))) {
        get_explanation();
        DREAL_LOG_INFO << "nra_solver::assertLit: unfeasibility detected:" << e;
        return false;
    }
    rp_vector_insert(rp_problem_ctrs(_rp_problem), c);
    for (int i = 0; i < rp_constraint_arity(c); ++i) {
        ++rp_variable_constrained(rp_problem_var(_rp_problem, rp_constraint_var(c, i)));
    }
    get_deductions();
    return true;
}

// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint () {
    DREAL_LOG_INFO << "nra_solver::pushBacktrackPoint " << _stack.size();
    // _boxes
    rp_box b;
    rp_box_clone(&b, rp_problem_box(_rp_problem));
    _boxes.push_back(b);
    // _stack
    _stack.push();
    // _used_constraints_stack
    _used_constraints_stack.push();
    static bool init = false;
    if (!init) {
        rp_problem_set_initial_box(_rp_problem);
        init = true;
    }
}

ostream & operator<<(ostream & out, lbool const & l) {
    if (l == l_True) {
        out << "True";
    } else if (l == l_False) {
        out << "False";
    } else {
        out << "Undef";
    }
    return out;
}

// Restore a previous state. You can now retrieve the size of the
// stack when you pushed the last backtrack point. You have to
// implement the necessary backtrack operations (see for instance
// backtrackToStackSize() in EgraphSolver) Also make sure you clean
// the deductions you did not communicate
void nra_solver::popBacktrackPoint () {
    DREAL_LOG_INFO << "nra_solver::popBacktrackPoint\t _stack.size()      = " << _stack.size();
    DREAL_LOG_INFO << "nra_solver::popBacktrackPoint\t deductions.size()   = " << deductions.size();

    // _stack
    _stack.pop();

    // _boxes
    rp_box b = _boxes.back();
    rp_box_copy(rp_problem_box(_rp_problem), b);
    rp_box_destroy(&b);
    _boxes.pop_back();

    // _used_constraints_stack
    if (_used_constraints_stack.pop() > 0 && _used_constraints_stack.size() > 0) {
        DREAL_LOG_DEBUG << "POP + RESET USED CONSTRAINTS";
        vector<bool> uc = _used_constraints_stack.last();
        DREAL_LOG_DEBUG << "STACK SIZE = " << _stack.size();
        DREAL_LOG_DEBUG << "UC    SIZE = " << uc.size();
        set_used_constraints(uc);
    }

    // pop a constraint
    while (rp_vector_size(rp_problem_ctrs(_rp_problem)) > static_cast<int>(_stack.size())) {
        rp_constraint c = static_cast<rp_constraint>(rp_vector_elem(rp_problem_ctrs(_rp_problem), rp_vector_size(rp_problem_ctrs(_rp_problem)) - 1));
        // Adjust constrained vars
        for (int i = 0; i < rp_constraint_arity(c); ++i) {
            --rp_variable_constrained(rp_problem_var(_rp_problem, rp_constraint_var(c, i)));
        }
        rp_ctr_num_used(rp_constraint_num(c)) = 0;
        rp_vector_pop(rp_problem_ctrs(_rp_problem), static_cast<void *>(c));
    }
}

// Check for consistency.
// If flag is set make sure you run a complete check
bool nra_solver::check(bool complete) {
    DREAL_LOG_INFO << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ")";
    DREAL_LOG_DEBUG << "nra_solver::check: stack = ";
    DREAL_LOG_DEBUG << _stack;
    bool result = true;
    if (!complete) {
        _stat_check_incomplete++;
        vector<bool> uc = get_used_constraints();
        _used_constraints_stack.push_back(uc);
        result = prop();
    } else {
        // Complete Check
        _stat_check_complete++;
        result = solve();
    }
    DREAL_LOG_INFO << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ")"
                   << " result = " << boolalpha << result;
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
