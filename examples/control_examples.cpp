#include<iostream>
#include<vector>
#include<assert.h>

#include "dreal.hh"

using namespace std;
using namespace dreal;

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
    s -> add(condition && !spec);
    if (!s->check()) {
	cout<<"The barrier function\n\tB = "<<B<<"\nis valid for the system defined by"<<endl;
	cout<<"\tf = [";
	for (auto e : f)
	    cout << e <<";";
	cout<<"]"<<endl;
    }
    else {
	cout<<"The function\n\tB = "<<B<<"\nis not a barrier certificate for the system defined by"<<endl;
	cout<<"\tf = [";
	for (auto e : f)
	    cout << e <<";";
	cout<<"]"<<endl;
	cout<<"because a counterexample has been found. ";
	s->print_model();
    }
}

void lyapunov_check(vector<expr>& x, vector<expr>& f, expr& V, double eps) {
    assert(x.size()==f.size());
    assert(eps>0);
    unsigned n = x.size();
    solver * s = x[0].get_solver();
    expr ball = s -> num("0");
    expr LV = s -> num("0");
    for (unsigned i=0;i<n;i++) {
	ball = ball + (x[i]^2); 
	LV = LV + f[i]*der(V,x[i]);
    }
    expr condition = implies(ball>eps, V>0) && implies(ball>eps, LV<0);
    s -> add(!condition);
    if (!s->check()) {
	cout<<"The Lyapunov function\n\tV = "<<V<<"\nis valid for the system defined by"<<endl;
	cout<<"\tf = [";
	for (auto e : f)
	    cout << e <<";";
	cout<<"]"<<endl;
    }
    else {
	cout<<"The function\n\tV = "<<V<<"\nis not a Lyapunov function for the system defined by"<<endl;
	cout<<"\tf = [";
	for (auto e : f)
	    cout << e <<";";
	cout<<"]"<<endl;
	cout<<"because a counterexample has been found. ";
	s->print_model();
    }
}

int test1() {
    solver s;
    expr x1 = s.var("x1", -2, 2);
    expr x2 = s.var("x2", -2, 2);
    vector<expr> x = {x1,x2};
    expr f1 = -x1;
    expr f2 = -x2;
    vector<expr> f = {f1,f2};
    expr B = (x1^2) + (x2^2) - 1;
    expr V = (x1^2) + (x2^2);
    barrier_check(x,f,B,0.01);
    lyapunov_check(x,f,V,0.01);
    return 0;
}

int vdp() {
    solver s;
    expr x1 = s.var("x1",-10,10);
    expr x2 = s.var("x2",-10,10);
    vector<expr> x = {x1,x2};
    expr f1 = -x2;
    expr f2 = ((x1^2)-1)*x2+x1;
    vector<expr> f = {f1,f2};
    expr B = 42.419930460509669*(x1^2)-25.467284450100433*x1*x2+29.037525088273682*(x2^2)+0.246437703822396*(x1^3)+0.342787267928099*(x1^2)*x2+0.070061019768681*x1*(x2^2)+0.056167250785361*(x2^3)-9.747135277935248*(x1^4)+1.281447375757236*(x1^3)*x2-1.066167940090009*(x1^2)*(x2^2)-0.111337393290709*x1*(x2^3)-3.148132699966833*(x2^4)-0.058675653184320*(x1^5)-0.088630122702897*(x1^4)*x2-0.035603912757564*(x1^3)*(x2^2)-0.092730054611810*(x1^2)*(x2^3)+0.030783940378564*x1*(x2^4)-0.016849595361031*(x2^5)+1.362207232588218*(x1^6)+1.257918398491556*(x1^5)*x2+0.407802497440289*(x1^4)*(x2^2)-1.168667210949858*(x1^3)*(x2^3)+1.839303562141088*(x1^2)*(x2^4)-0.729105138802864*x1*(x2^5)+0.326281890950742*(x2^6) - 90;
    expr V = B + 90;
    barrier_check(x,f,B,0.01);
    lyapunov_check(x,f,V,0.01);
    return 0;
}

int main(int argc, char* argv[]) {
    cout<<test1()<<endl;
    cout<<vdp()<<endl;
    return 0;
}
