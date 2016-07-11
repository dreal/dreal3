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
    s.set_delta(0.00000001);
    expr x1 = s.var("x1", -0.5, 0.5);
    vector<expr*> x = {&x1};
    expr f1 = -x1;
    vector<expr*> f = {&f1};
    expr p1 = s.var("p1", 1, 5);
    // expr p2 = s.var("p2", -1, 1);
    vector<expr*> p = {&p1};
    expr V = p1*pow(x1, 2);
    synthesizeLyapunov(x, p, f, V, 0.1);
}

void test3b() {
    solver s;
    expr x = s.var("x");
    expr f1 = x^2;
    expr f2 = sin(x);
    expr f3 = cos(x);
    s.add(f1 >0);
    s.add(f2 > 0);
    s.push();
    s.add(f3 > 0);
    cerr << "first dump" << endl;
    s.check();
    s.dump_formulas(cerr);
    s.pop();
    cerr << "second dump" << endl;
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

int inv_pend() {
    solver s;
    // s.set_polytope();
    expr x1 = s.var("x", -0.1, 0.1);
    expr x2 = s.var("xdot", -1, 1);
    expr x3 = s.var("theta", -0.1, 0.1);
    expr x4 = s.var("thetadot", -1, 1);
    vector<expr*> x = {&x1, &x2, &x3, &x4};
    expr p1 = s.var("p1", -10, 10);
    expr p2 = s.var("p2", -10, 10);
    expr p3 = s.var("p3", -10, 10);
    expr p4 = s.var("p4", -10, 10);
    expr p5 = s.var("p5", -10, 10);
    expr p6 = s.var("p6", -10, 10);
    expr p7 = s.var("p7", -10, 10);
    expr p8 = s.var("p8", -10, 10);
    expr p9 = s.var("p9", -10, 10);
    expr p10 = s.var("p10", -10, 10);
    expr p11 = s.var("p11", -10, 10);
    expr p12 = s.var("p12", -10, 10);
    expr p13 = s.var("p13", -10, 10);
    vector<expr*> p = {&p1, &p2, &p3, &p4, &p5, &p6, &p7, &p8, &p9, &p10, &p11, &p12, &p13};
    expr u = p10*x1 + p11*x2 - p12*x3 - p13*x4;
    expr f1 = x2;
    expr f2 = -(-6*sin(x3)*(x4^2) + 100*u - 10*x2 + 147*cos(x3)*sin(x3))/(5*(3*(cos(x3)^2) - 14));
    expr f3 = x4;
    expr f4 = -(- 3*cos(x3)*sin(x3)*(x4^2) + 343*sin(x3) + 50*u*cos(x3) - 5*x2*cos(x3))/(3*(cos(x3)^2) - 14);
    vector<expr*> f = {&f1, &f2, &f3, &f4};
    expr V = x2*(p1*x1 + p2*x2 - p3*x3 - p4*x4) + x1*(p5*x1 + x2 - p7*x3 - p8*x4) - x3*(2.63237*x1 + 3.77814*x2 - p9*x3 - 2.12247*x4) - 1.0*x4*(0.499053*x1 + 0.697897*x2 - 2.12247*x3 - p6*x4);
    synthesizeLyapunov(x, p, f, V, 0.001);
    return 0;
}

void normPend() {
    solver s;
    expr x1 = s.var("x1", -0.5, 0.5);
    expr x2 = s.var("x2", -0.5, 0.5);
    vector<expr*> x = {&x1, &x2};
    expr f1 = x2;
    expr f2 = -sin(x1)-x2;
    vector<expr*> f = {&f1, &f2};
    poly V = poly(x, "p", 2);
    V.setCofBounds(-5, 5);
    synthesizeLyapunov(x, V.getCofs(), f, V, 0.001);
}

int main() {
    normPend();
    return 0;
}
