#include <iostream>
#include <vector>
#include "drealControl.h"

using namespace std;
using namespace dreal;

void test1() {
    solver s;
    expr x1 = s.var("x1",-1,1);
    expr p1 = s.var("p1", -5, 5);
    expr p2 = s.var("p2", -5, 5);
    vector<expr*> x = {&x1};
    vector<expr*> p_f = {&p1,&p2};
    poly V = poly(x,"q",4);
    V.setCofBounds(-5,5);
    expr f1 = p1*x1 + p2*(x1^3);
    vector<expr*> f = {&f1};
    synthesizeControlAndLyapunov(x,p_f,V.getCofs(),f,V,0.0001);
}

void test2() {
    solver s;
    expr x1 = s.var("x1",-0.15,0.15);
    expr x2 = s.var("x2",-0.15,0.15);
    vector<expr*> x = {&x1,&x2};
    expr f1 = x2;
    expr f2 = -sin(x1)-x2;
    vector<expr*> f = {&f1,&f2};
    expr p1 = s.var("p1",-10,10);
    expr p2 = s.var("p2",-10,10);
    expr p3 = s.var("p3",-10,10);
    vector<expr*> p = {&p1,&p2,&p3};
    expr V = p1*pow(x1,2) + p2*pow(x2,2) + p3*x1*x2;
    synthesizeLyapunov(x,p,f,V,0.05);
}

void test3() {
    solver s;
    //s.set_delta(0.00001);
    expr x1 = s.var("x1",-0.5,0.5);
    expr x2 = s.var("x2",-0.5,0.5);
    vector<expr*> x = {&x1,&x2};
    expr f1 = -x1;
    expr f2 = -x2;
    vector<expr*> f = {&f1,&f2};
    //poly V = poly(x,"p",2);
    expr p1 = s.var("p1",0,100);
    expr p2 = s.var("p2",0,100);
    expr p3 = s.var("p3",-100,100);
    //V.setCofBounds(-5,5);
    vector<expr*> p = {&p1,&p2,&p3};
    expr V = p1*pow(x1,2) + p2*pow(x2,2) + p3*x1*x2;
    synthesizeLyapunov(x,p,f,V,0.005);
}

void test4() {
    solver s;
    s.set_delta(0.0000001);
    expr x1 = s.var("x1",-0.5,0.5);
    vector<expr*> x = {&x1};
    expr f1 = -x1;
    vector<expr*> f = {&f1};
    poly V = poly(x,"p",2);
    V.setCofBounds(0,10);
    synthesizeLyapunov(x,V.getCofs(),f,V,0.01);
}

int main() {
    test3();
    return 0;
}
