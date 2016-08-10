#include<iostream>
#include<vector>
#include<assert.h>

#include "dreal.h"

using namespace std;
using namespace dreal;

int basics1() {
    solver s;
    expr x = s.var("x");
    expr zero = s.num(0.0);
    x.set_lb(-10);
    x.set_ub(10);
    expr xx = s.var("xx");
    vector<expr*> xxv = {&x,&xx};
    poly ppp(xxv,"a",2);
    cerr<<*ppp.getExpr()<<endl;
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
    s.add(der(p,x)>0);
    s.add(der(der(p,x),x)>0);
    s.print_problem();
    if (s.check())
        s.print_model();
    else
        cerr<<"false"<<endl;
    cerr<<"*zz:"<<*zz<<endl;
    return 0;
}

int basics2() {
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

int open() {
    solver s;
    expr k = s.var("k");
    k.set_lb(7);
    k.set_ub(10000000);
    expr left = pow(3, k) - pow(2,k)*pow((3/2),k);
    expr right = pow(2,k) - pow(3/2,k) - 2;
    s.add(left>right);
    s.solve();
    return 0;
}

int main(int argc, char* argv[]) {
    cout<<basics1()<<endl;
    //cout<<basics2()<<endl;
    cout<<open()<<endl;
    return 0;
}
