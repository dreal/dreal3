#include<iostream>
#include<vector>
#include<assert.h>
#include "dreal.hh"

using namespace std;
using namespace dreal;

int basic1() {
    solver s;
    expr x = s.var("x");
    expr zero = s.num(0.0);
    x.set_lb(-10);
    x.set_ub(10);
    expr p = upoly(x,"c",5);
    cerr << p << endl;
    expr * zz = s.new_var("zz");
    expr * zz2 = s.new_var("zz");
    zz->set_lb(2);
    expr sn = sin(x);
    sn = sn + 2;
    expr * snp = &sn;
    expr y = s.var("y", 0, 10);
    expr phi = (sin(x) < 0.9);
    expr f = cos(x) ;
    cerr << "f: " << f << endl;
    cerr << "derivative of f: "<< der(f,x)<<endl;
    expr phi2 = (-f == 0) ;
    //s.add(phi);
    s.add(p==0);
    s.add(der(p,x)==0);
    s.add(der(der(p,x),x)>0);
    s.print_problem();
    if (s.check())
        s.print_model();
    else
        cerr<<"false"<<endl;
    cerr<<"*zz:"<<*zz<<endl;
    return 0;
}

int basic2() {
    solver  s;
    expr    x = s.var("x");
    expr    y = s.var("y");
    expr    n = s.num("3.14");
    x.set_lb(1);
    y.set_ub(10);
    x.set_lb(0);
    x.set_ub(2);
    expr    phi = (x>sin(n));
    expr    psi = (y<pow(x,2));
    expr    psi2 = ((x^2) > y);
    expr    phi2 = (phi && psi || psi2);
    s.add(phi);
    s.add(!phi2);
    s.add(psi2);
    s.print_problem();
    s.solve();
    return 0;
}

void barrier_check(vector<expr>& x, vector<expr>& f, expr& B, double eps) {
    assert(x.size()==f.size());
    unsigned n = x.size();
    solver * s = x[0].get_solver();
    expr condition = (B == -eps);
    expr LB = s -> num("0");
    for (unsigned i=0;i<n;i++) {
	LB = LB + f[i]*der(B,x[i]);
    }
    expr spec = (LB < -eps);
    //s -> add(condition && !spec);
    s -> add(condition);
    s -> print_problem();
    s -> solve();    
}

int test3() {
    solver s;
    expr x1 = s.var("x1", -2, 2);
    expr x2 = s.var("x2", -2, 2);
    vector<expr> x = {x1,x2};
    expr f1 = (x1^2);
    expr f2 = x2;
    vector<expr> f = {f1,f2};
    expr B = (x1^2) + (x2^2) - 1;
    barrier_check(x,f,B,0.01);
    return 0;
}

int main(int argc, char* argv[]) {
    //cout<<basic1()<<endl;
    //cout<<basic2()<<endl;
    cout<<test3()<<endl;
}
