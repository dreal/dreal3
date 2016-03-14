#include<iostream>
#include<vector>
#include "dreal.hh"

using namespace std;
using namespace dreal;

int basic1() {
    solver s;
    expr x = s.var("x");
    //cout << "x: [" <<s.get_lb(x)<<", "<<s.get_ub(x)<<"]"<<endl;
    //s.set_domain_lb(x,1.0);
    //s.set_domain_ub(x,2.0);
    //vector<expr> z = s.var_vec("z",10);
    //cout<<z[9];  
    expr zero = s.num(0.0);
    x.set_lb(2);
    x.set_ub(3);
    expr sn = sin(x);
    expr phi = (sin(x) > zero);
    expr f = x + x * x + sin(x*sin(x)) ;
    expr phi2 = (-f == 0) ;
    s.add(phi);
    //s.add(!phi);
    cout << phi2 << endl;
    if (s.check()) 
	s.print_model();
    else
	cout<<"false"<<endl;
    //cout << "x: [" <<s.get_lb(x)<<", "<<s.get_ub(x)<<"]"<<endl;
    return 0;
}

int basic2() {
    solver s;
    expr    x = s.var("x");
    expr    y = s.var("y");
    expr    phi = (x>sin(y));
    expr    psi = (y<pow(x,2));
    expr    psi2 = (pow(x,y) > y);
    //this isn't working? expr    psi2 = (x^y > y);
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


