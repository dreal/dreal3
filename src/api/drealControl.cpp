/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>
        Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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

#include <cassert>
#include <iostream>
#include <random>
#include <vector>
#include "api/drealControl.h"

namespace dreal {

using std::cerr;
using std::cout;
using std::endl;
using std::vector;

void checkBarrier(vector<expr>& x, vector<expr>& f, expr& B, double const eps) {
    assert(x.size() == f.size());
    unsigned n = x.size();
    solver * s = x[0].get_solver();
    expr condition = (B == -eps);
    expr LB = s -> num("0");
    for (unsigned i = 0; i < n; i++) {
        LB = LB + f[i] * der(B, x[i]);
    }
    expr spec = (LB < -eps);
    s -> add(condition && !spec);
    if (!s->check()) {
        cout << "The barrier function\n\tB = " << B << "\nis valid for the system defined by" << endl;
        cout << "\tf = [";
        for (auto e : f)
            cout << e << ";";
        cout << "]" << endl;
    } else {
        cout << "The function\n\tB = " << B << "\nis not a barrier certificate for the system defined by" << endl;
        cout << "\tf = [";
        for (auto e : f)
            cout << e << ";";
        cout << "]" << endl;
        cout << "because a counterexample has been found. ";
        s->print_model();
    }
}

void checkLyapunov(vector<expr>& x, vector<expr>& f, expr& V, double const eps) {
    assert(x.size() == f.size());
    assert(eps > 0);
    unsigned n = x.size();
    solver * s = x[0].get_solver();
    expr ball = s -> num("0");
    expr LV = s -> num("0");
    for (unsigned i = 0; i < n; i++) {
        ball = ball + (x[i]^2);
        LV = LV + f[i] * der(V, x[i]);
    }
    expr condition = implies(ball > eps, V > 0) && implies(ball > eps, LV < 0);
    s -> add(!condition);
    if (!s->check()) {
        cout << "The Lyapunov function\n\tV = " << V << "\nis valid for the system defined by" << endl;
        cout << "\tf = [";
        for (auto e : f)
            cout << e << ";";
        cout << "]" << endl;
    } else {
        cout << "The function\n\tV = " << V << "\nis not a Lyapunov function for the system defined by" << endl;
        cout << "\tf = [";
        for (auto e : f)
            cout << e << ";";
        cout << "]" << endl;
        cout << "because a counterexample has been found. ";
        s->print_model();
    }
}

void synthesizeLyapunov(vector<expr*>& x, vector<expr*>& p, vector<expr*>& f, expr& V, double const eps) {
    // number of ODEs should be same as number of state vars
    assert(x.size() == f.size());
    assert(eps > 0);
    // everything happening in the solver. to be extra safe, should check all vars share the same solver.
    solver * s = x[0]->get_solver();
    expr zero = s->num("0");
    expr v = s->var("V");
    expr lv = s->var("LV");
    // turn on polytope in solver
    s -> set_polytope();
    // s -> set_simulation();  // the simulation option gives seg fault as of Jun 23, 2016
    // ball is the epsilon-ball that will be excluded from the checking
    expr ball = zero;
    // LV is the Lie derivative of V
    expr LV = zero;
    // assemble ball and LV
    for (unsigned i = 0; i < x.size(); i++) {
        ball = ball + ((*x[i]) ^ 2);
        LV = LV + (*f[i]) * der(V, (*x[i]));
    }
    cerr<<"Candidate V: "<<V<<endl;
    cerr<<"Lie Derivative of V: "<<LV<<endl;
    // scondition will be part of the search condition
    expr scondition = (V >= 0) && (LV <= 0);
    // condition is an auxilary formula
    expr condition = (ball > eps && v < 0.000001 * eps) || (ball > eps && lv > (-0.00001 * eps));
    // search condition will be used for finding parameters
    expr search_condition = scondition;
    // prepare a push point. will first add the formula for searching, then pop, then add formula for verifying
    s->push();
    s->add(search_condition);
    // start with the trivial point
    for (auto state : x) {
        s->add(*state == zero);
    }
    // cerr << "Initial Search Condition: " << search_condition << endl;
    unsigned round = 0;
    expr tmp;
    // the check() solves the search problem and suggest candidate values for parameters
    while (s->check() && round < 3) {
        cerr << "=== Search Formula ===" << endl;
        s->dump_formulas(cerr);
        // cout << "Trying these parameters:" << endl;
        // cerr << "Round " << round << endl;
        // s->print_model();
        // will try to find counterexample, thus the negation
        expr verify_condition = condition;
        // set the parameter variables to the chosen values
        for (auto param : p) {
            verify_condition = verify_condition && ( (*param) == ((s->get_lb(*param)+s->get_ub(*param))/2));
        }
        // pop the search formula and add the verification formula
        s->pop();
        s->push();
        s->add(verify_condition);
        s->add(v == V && lv == LV);
        if (!s->check()) {
            cout << "Lyapunov function synthesized: " << V << endl;
            // todo: print the L function and system with solved parameters.
            return;
        } else {
            cerr << "=== Falsification Formula ===" << endl;
            s->dump_formulas(cerr);
            cout << "Counterexample found:" << endl;
            s->print_model();
            // sol will store the counterexample
            vector<expr*> sol;
            for (auto state : x) {
                sol.push_back(s->new_num((s->get_lb(*state)+s->get_ub(*state))/2));
            }
            unsigned sample = 0;
            // sub in the values of the counterexample, and update the search formula
            vector<expr*> full_pre;
            vector<expr*> full_post;
            full_pre.reserve(x.size()+p.size()+2);
            full_post.reserve(sol.size()+p.size()+2);
//            std::default_random_engine re(std::random_device {}());
//            while (sample < 50) {
                // full_pre holds the list of variables
                full_pre.insert(full_pre.end(), x.begin(), x.end());
                full_pre.insert(full_pre.end(), p.begin(), p.end());
                full_pre.push_back(&v);
                full_pre.push_back(&lv);
                // full_post holds the list of assignments
                full_post.insert(full_post.end(), sol.begin(), sol.end());
                full_post.insert(full_post.end(), p.begin(), p.end());
                full_post.push_back(&v);
                full_post.push_back(&lv);
                // substitution needs both vectors
                search_condition = substitute(search_condition, full_pre, full_post);
                search_condition = search_condition && substitute(scondition, full_pre, full_post);
                // cout << "loop at: " << sample << " with search condition: " << search_condition << endl;
                // clean up
//                sol.clear();
//                full_pre.clear();
//                full_post.clear();
                // add a new sample point on x
/*                for (auto state : x) {
                    // cout << "lower: " << s->get_domain_lb(*state) << " ";
                    // cout << "upper: " << s->get_domain_ub(*state) << endl;
                    std::uniform_real_distribution<double> unif(s->get_domain_lb(*state), s->get_domain_ub(*state));
                    double p = unif(re);
                    // cout << *state << " :" << p << " ";
                    sol.push_back(s->new_num(p));
                }
                sample++;
            }
*/
            // optional: exclude parameters we have tried
/*              tmp = zero;
                for (auto param : p) {
                    tmp = tmp + pow((*param - (s->get_lb(*param)+s->get_ub(*param))/2),2);
                }
                search_condition = search_condition && (tmp > 0.0001);
                delete the verification formula and add the search formula
*/
            s->pop();
            s->push();
            s->add(search_condition);
            // s->add(v == V && lv == LV);
            // cout << "Search condition: " << search_condition << endl;
        }
        cerr << "Round " << round << endl;
        round++;
    }
    cout << "No Lypaunov function found." << endl;
    return;
}

void synthesizeControlAndLyapunov(vector<expr*>& x, vector<expr*>& p_f, vector<expr*>& p_v, vector<expr*>& f, expr& V, double const eps) {
    vector<expr*> p;
    for (auto e : p_f) {
        p.push_back(e);
    }
    for (auto e : p_v) {
        p.push_back(e);
    }
    synthesizeLyapunov(x, p , f , V, eps);
}
}  // namespace dreal
