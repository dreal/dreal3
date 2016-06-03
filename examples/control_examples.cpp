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

void syn_lyp(vector<expr*>& x, vector<expr*>& p, vector<expr*>& f, expr& V, double eps) {

    assert(x.size()==f.size());
    assert(eps>0);

    unsigned n = x.size();
    solver * s = x[0]->get_solver();
    s -> set_polytope();
    s -> set_simulation();

    expr ball = s -> num("0");
    expr LV = s -> num("0");

    for (unsigned i=0;i<n;i++) {
	ball = ball + ((*x[i])^2); 
	LV = LV + (*f[i]) * der(V,(*x[i]));
    }

    expr scondition = V>=0 && LV<=0;
    expr condition = implies(ball>eps, V>0) && implies(ball>eps, LV<0);
//    expr condition = V>=0 && LV<=0 && implies(ball==0,V<eps)&& implies(ball==0,LV<eps);
//    expr condition = V>=0 && LV<=0; 
    expr search_condition = scondition;

    s->push();
    s->add(search_condition);

    int i=0;
    while (s->check()) {
	cout<<"Trying these parameters:"<<endl;
	cerr<<"Round "<<i<<endl;
	s->print_model();
	expr verify_condition = !condition;
	for (auto param : p) {
	    verify_condition = verify_condition && ( (*param) == ((s->get_lb(*param)+s->get_ub(*param))/2));
	}
	s->pop();
	s->push();
	s->add(verify_condition); 
	cout<<"Verifying: "<<verify_condition<<endl;
	if (!s->check()) {
	    cout<<"Lyapunov function synthesized:"<<endl;
	    return;
	} else {
	    cout<<"Counterexample found:"<<endl;
	    s->print_model();
	    vector<expr*> sol; 
	    for (auto state: x) { 
		sol.push_back(s->new_num((s->get_lb(*state)+s->get_ub(*state))/2));
	    }
	    vector<expr*> full_pre;
	    vector<expr*> full_post;
	    full_pre.reserve(x.size()+p.size());
	    full_post.reserve(sol.size()+p.size());
	    full_pre.insert(full_pre.end(),x.begin(),x.end());
	    full_pre.insert(full_pre.end(),p.begin(),p.end());
	    full_post.insert(full_post.end(),sol.begin(),sol.end());
	    full_post.insert(full_post.end(),p.begin(),p.end());
	    search_condition = substitute(search_condition,full_pre,full_post);
	    search_condition = search_condition && substitute(scondition,full_pre,full_post);
	    for (auto param : p) {
		search_condition = search_condition && (!((*param) == ((s->get_lb(*param)+s->get_ub(*param))/2)));
	    }
	    s->pop();
	    s->push();
   	    s->add(search_condition);
	    cout<<"Search condition: "<<search_condition<<endl;
	}
	cerr<<"Round "<<i<<endl;
	i++;
    } 
    
    cout<<"No Lypaunov function found."<<endl;
    return;
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
    s.set_polytope();
    barrier_check(x,f,B,0.01);
    lyapunov_check(x,f,V,0.01);
    return 0;
}

int test_lyp_syn() {
    solver s;
    expr x1 = s.var("x1",-5,5);
    expr p1 = s.var("p1", -5, 5);
    expr p2 = s.var("p2", -5, 5);
    expr p3 = s.var("p3", 0.2, 2);
    expr p4 = s.var("p4", 1, 2);
    expr p5 = s.var("p5", -5, 5);
    vector<expr*> x = {&x1};
    vector<expr*> p = {&p1,&p2,&p3,&p4,&p5};
    expr f1 = p1*x1 + p2*sin(x1);
    vector<expr*> f = {&f1};
    expr V = p3*(x1^2) + p4*x1 + p5*(sin(x1)*sin(x1));
    syn_lyp(x,p,f,V,0.0001);
    return 0;
}

int inv_pend_syn() {
    solver s;
    expr x1 = s.var("x",-0.3,0.3);
    expr x2 = s.var("xdot",-3,3);
    expr x3 = s.var("theta",-0.3,0.3);
    expr x4 = s.var("thetadot",-3,3);
    vector<expr*> x = {&x1,&x2,&x3,&x4};
    expr p1 = s.var("p1",-10,10);
    expr p2 = s.var("p2",-10,10);
    expr p3 = s.var("p3",-10,10);
    expr p4 = s.var("p4",-10,10);
    expr p5 = s.var("p5",-10,10);
    expr p6 = s.var("p6",-10,10);
    expr p7 = s.var("p7",-10,10);
    expr p8 = s.var("p8",-10,10);
    expr p9 = s.var("p9",-10,10);
    expr p10 = s.var("p10",-10,10);
    expr p11 = s.var("p11",-10,10);
    expr p12 = s.var("p12",-10,10);
    expr p13 = s.var("p13",-10,10);

    vector<expr*> p = {&p1,&p2,&p3,&p4,&p5,&p6,&p7,&p8,&p9,&p10,&p11,&p12,&p13};

    expr u = p10*x1 + p11*x2 - p12*x3 - p13*x4; 
    expr f1 = x2;
    expr f2 = -(-6*sin(x3)*(x4^2) + 100*u - 10*x2 + 147*cos(x3)*sin(x3))/(5*(3*cos(x3)^2 - 14));
    expr f3 = x4;
    expr f4 = -(- 3*cos(x3)*sin(x3)*(x4^2) + 343*sin(x3) + 50*u*cos(x3) - 5*x2*cos(x3))/(3*(cos(x3)^2) - 14);   
    vector<expr*> f = {&f1,&f2,&f3,&f4};

    expr V = x2*(p1*x1 + p2*x2 - p3*x3 - p4*x4) + x1*(p5*x1 + x2 - p7*x3 - p8*x4) - x3*(2.63237*x1 + 3.77814*x2 - p9*x3 - 2.12247*x4) - 1.0*x4*(0.499053*x1 + 0.697897*x2 - 2.12247*x3 - p6*x4);

    syn_lyp(x,p,f,V,0.001);

    return 0; 
}


int test2_lyp() {
    solver s;
    expr x = s.var("x",-1,1);
    expr p = s.var("p",0.5,1);
    expr f = p*x;
    expr V = (x^2);
    vector<expr*> xp = {&x};
    vector<expr*> pp = {&p};
    vector<expr*> fp = {&f};
    syn_lyp(xp,pp,fp,V,0.01);
    return 0;
}

int main(int argc, char* argv[]) {
    //cout<<test1()<<endl;
    //cout<<vdp()<<endl;
    cerr<<inv_pend_syn()<<endl;
    //cout<<test2_lyp()<<endl;
    //cerr<<test_lyp_syn()<<endl;
    return 0;
}
