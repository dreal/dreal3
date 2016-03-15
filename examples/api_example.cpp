#include<iostream>
#include<vector>
#include "dreal.hh"

using namespace std;
using namespace dreal;

int basic1() {
    solver s;
    expr x = s.var("x");
    expr zero = s.num(0.0);
    x.set_lb(2);
    x.set_ub(3);
    expr sn = sin(x);
    expr phi = (sin(x) > 0.9);
    expr f = x + x * x + sin(x*sin(x)) ;
    expr phi2 = (-f == 0) ;
    s.add(phi);
    s.add(!phi);
    s.print_problem();
    if (s.check()) 
	s.print_model();
    else
	cout<<"false"<<endl;
    s.print_model();
    return 0;
}

int basic2() {
    solver  s;
    expr    x = s.var("x");
    expr    y = s.var("y");
    expr    n = s.var("3.14");
    expr    phi = (x>sin(n));
    expr    psi = (y<pow(x,2));
    expr    psi2 = ((x^2) > y);
    cerr<<psi2;
    expr    phi2 = (phi && psi || psi2);
    s.add(phi);
    s.add(phi2);
    s.add(psi2);
    cout << (s.check()? "true":"false") << endl;
    return 0;
}

int main(int argc, char* argv[]) {
    cout<<basic1()<<endl;
    cout<<basic2()<<endl;
}


