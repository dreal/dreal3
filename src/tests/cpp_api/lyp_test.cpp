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

#include <iostream>
#include <vector>
#include "api/drealControl.h"

using dreal::expr;
using dreal::poly;
using dreal::solver;
using std::vector;
using std::cerr;
using std::endl;

void test1() {
    solver s;
    expr x1 = s.var("x1", -1, 1);
    expr p1 = s.var("p1", -5, 5);
    expr p2 = s.var("p2", -5, 5);
    vector<expr*> x = {&x1};
    vector<expr*> p_f = {&p1, &p2};
    poly V = poly(x, "q", 4);
    V.setCofBounds(-5, 5);
    expr f1 = p1*x1 + p2*(x1^3);
    vector<expr*> f = {&f1};
    synthesizeControlAndLyapunov(x, p_f, V.getCofs(), f, V, 0.0001);
}

void test2() {
    solver s;
    expr x1 = s.var("x1", -0.15, 0.15);
    expr x2 = s.var("x2", -0.15, 0.15);
    vector<expr*> x = {&x1, &x2};
    expr f1 = x2;
    expr f2 = -sin(x1)-x2;
    vector<expr*> f = {&f1, &f2};
    expr p1 = s.var("p1", -10, 10);
    expr p2 = s.var("p2", -10, 10);
    expr p3 = s.var("p3", -10, 10);
    vector<expr*> p = {&p1, &p2, &p3};
    expr V = p1*pow(x1, 2) + p2*pow(x2, 2) + p3*x1*x2;
    synthesizeLyapunov(x, p, f, V, 0.05);
}

void test3() {
    solver s;
    // s.set_delta(0.00001);
    expr x1 = s.var("x1", -0.5, 0.5);
    expr x2 = s.var("x2", -0.5, 0.5);
    vector<expr*> x = {&x1, &x2};
    expr f1 = -x1;
    expr f2 = -x2;
    vector<expr*> f = {&f1, &f2};
    // poly V = poly(x, "p", 2);
    expr p1 = s.var("p1", -100, 100);
    expr p2 = s.var("p2", -100, 100);
    // V.setCofBounds(-5, 5);
    vector<expr*> p = {&p1, &p2};
    expr V = p1*pow(x1, 2) + p2*pow(x2, 2);
    synthesizeLyapunov(x, p, f, V, 0.005);
}

void test3a() {
    solver s;
    // s.set_delta(0.00001);
    expr x1 = s.var("x1", -0.5, 0.5);
    vector<expr*> x = {&x1};
    expr f1 = -x1;
    vector<expr*> f = {&f1};
    expr p1 = s.var("p1", -100, 100);
    expr p2 = s.var("p2", -100, 100);
    vector<expr*> p = {&p1, &p2};
    expr V = p1*pow(x1, 2) + p2*x1;
    synthesizeLyapunov(x, p, f, V, 0.005);
}

void test3b() {
    solver s;
    expr x = s.var("x");
    expr f1 = x^2;
    expr f2 = sin(x);
    expr f3 = cos(x);
    s.add(f1 >0);
    s.add(f2>0);
    s.push();
    s.add(f3>0);
    cerr<<"first dump"<<endl;
    s.check();
    s.dump_formulas(cerr);
    s.pop();
    cerr<<"second dump"<<endl;
    s.check();
    s.dump_formulas(cerr);
}

void test4() {
    solver s;
    s.set_delta(0.0000001);
    expr x1 = s.var("x1", -0.5, 0.5);
    vector<expr*> x = {&x1};
    expr f1 = -x1;
    vector<expr*> f = {&f1};
    poly V = poly(x, "p", 2);
    V.setCofBounds(0, 10);
    synthesizeLyapunov(x, V.getCofs(), f, V, 0.01);
}

int main() {
    test3a();
    return 0;
}
