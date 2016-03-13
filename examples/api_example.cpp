#include <iostream>
#include "dreal.hh"

using namespace std;
using namespace dreal;

int basic1() {
    solver s;
    expr x = s.var("x", Real);
    expr zero = s.num(0.0);
    expr sn = sin(x);
    expr phi = (sn == zero);
    expr f = x + x * x + sin(x*sin(x)) ;
    expr phi2 = (-f == 0) ;
    s.add(phi);
    s.add(phi2);
    cout << (s.check()? "true":"false") << endl;
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
    s.print(phi2);
    cout << (s.check()? "true":"false") << endl;
    return 0;
}

int main(int argc, char* argv[]) {
    cout<<basic1()<<endl;
    cout<<basic2()<<endl;
}


