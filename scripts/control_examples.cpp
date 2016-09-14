#include<iostream>
#include<vector>
#include<assert.h>

#include "dreal.h"

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

void lyapunov_print(vector<expr*>& x, vector<expr*>& f, expr& V, double eps, string name) {
    assert(x.size()==f.size());
    assert(eps>0);
    unsigned n = x.size();
    solver * s = x[0]->get_solver();
    expr ball = s -> num("0");
    expr LV = s -> num("0");
    for (unsigned i=0;i<n;i++) {
        ball = ball + (pow(*x[i],2));
        LV = LV + (*f[i])*der(V,*x[i]);
    }
    expr c1 = (ball <= eps); 
    expr c2 = (V>=0);
    expr c3 = (LV<=0);
    s -> add(c1 && c2 && c3);
    s -> dump_dr_file(name);
}

void syn_lyp(vector<expr*>& x, vector<expr*>& p, vector<expr*>& f, expr& V, double eps) {
    //number of ODEs should be same as number of state vars
    assert(x.size()==f.size());
    assert(eps>0);
    //everything happening in the solver. to be extra safe, should check all vars share the same solver.
    solver * s = x[0]->get_solver();
    expr zero = s->num("0");
    //turn on polytope in solver
    s -> set_polytope();
    //s -> set_simulation();  //the simulation option gives seg fault as of Jun 23, 2016
    //ball is the epsilon-ball that will be excluded from the checking
    expr ball = zero;
    //LV is the Lie derivative of V
    expr LV = zero;
    //assemble ball and LV
    for (unsigned i=0;i<x.size();i++) {
        ball = ball + ((*x[i])^2);
        LV = LV + (*f[i]) * der(V,(*x[i]));
    }
    //scondition will be part of the search condition
    expr scondition = V>=0 && LV<=0;
    //condition is an auxilary formula
    expr condition = implies(ball>eps, V>0) && implies(ball>eps, LV<0);
    //search condition will be used for finding parameters
    expr search_condition = scondition;
    //prepare a push point. will first add the formula for searching, then pop, then add formula for verifying
    s->push();
    s->add(search_condition);
    //start with the trivial solution
    for (auto param : p) {
        s->add(*param==zero);
    }
    unsigned round=0;
    //the check() solves the search problem and suggest candidate values for parameters
    while (s->check()) {
        cout<<"Trying these parameters:"<<endl;
        cerr<<"Round "<<round<<endl;
        s->print_model();
        //will try to find counterexample, thus the negation
        expr verify_condition = !condition;
        //set the parameter variables to the chosen values
        for (auto param : p) {
            verify_condition = verify_condition && ( (*param) == ((s->get_lb(*param)+s->get_ub(*param))/2));
        }
        //pop the search formula and add the verification formula
        s->pop();
        s->push();
        s->add(verify_condition);
        cout<<"Verifying: "<<verify_condition<<endl;
        if (!s->check()) {
            cout<<"Lyapunov function synthesized."<<endl;
            //todo: print the L function and system with solved parameters.
            return;
        } else {
            cout<<"Counterexample found:"<<endl;
            s->print_model();
            //sol will store the counterexample
            vector<expr*> sol;
            for (auto state: x) {
                sol.push_back(s->new_num((s->get_lb(*state)+s->get_ub(*state))/2));
            }
            //sub in the values of the counterexample, and update the search formula
            vector<expr*> full_pre;
            vector<expr*> full_post;
            full_pre.reserve(x.size()+p.size());
            full_post.reserve(sol.size()+p.size());
            //full_pre holds the list of variables
            full_pre.insert(full_pre.end(),x.begin(),x.end());
            full_pre.insert(full_pre.end(),p.begin(),p.end());
            //full_post holds the list of assignments
            full_post.insert(full_post.end(),sol.begin(),sol.end());
            full_post.insert(full_post.end(),p.begin(),p.end());
            //substitution needs both vectors
            search_condition = substitute(search_condition,full_pre,full_post);
            search_condition = search_condition && substitute(scondition,full_pre,full_post);
            //optionally we can exclude some parameters that have been tried before. but negating equalities is not useful.
            //for (auto param : p) {
            //	search_condition = search_condition && (!((*param) == ((s->get_lb(*param)+s->get_ub(*param))/2)));
            //}
            //clean up the verification formula and add the search formula
            s->pop();
            s->push();
            s->add(search_condition);
            cout<<"Search condition: "<<search_condition<<endl;
        }
        cerr<<"Round "<<round<<endl;
        round++;
    }
    cout<<"No Lypaunov function found."<<endl;
    return;
}

void syn_ctr_lyp(vector<expr*>& x, vector<expr*>& p_f, vector<expr*>& p_v, vector<expr*>& f, expr& V, double eps) {
    vector<expr*> p;
    for (auto e : p_f) {
        p.push_back(e);
    }
    for (auto e : p_v) {
        p.push_back(e);
    }
    syn_lyp(x,p,f,V,eps);
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
    expr B = 42.419930460509669*(x1^2)-25.467284450100433*x1*x2+
    29.037525088273682*(x2^2)+0.246437703822396*(x1^3)+0.342787267928099*(x1^2)*x2
    +0.070061019768681*x1*(x2^2)+0.056167250785361*(x2^3)-9.747135277935248*(x1^4)
    +1.281447375757236*(x1^3)*x2-1.066167940090009*(x1^2)*(x2^2)
    -0.111337393290709*x1*(x2^3)-3.148132699966833*(x2^4)
    -0.058675653184320*(x1^5)-0.088630122702897*(x1^4)*x2
    -0.035603912757564*(x1^3)*(x2^2)-0.092730054611810*(x1^2)*(x2^3)
    +0.030783940378564*x1*(x2^4)-0.016849595361031*(x2^5)
    +1.362207232588218*(x1^6)+1.257918398491556*(x1^5)*x2
    +0.407802497440289*(x1^4)*(x2^2)-1.168667210949858*(x1^3)*(x2^3)
    +1.839303562141088*(x1^2)*(x2^4)-0.729105138802864*x1*(x2^5)
    +0.326281890950742*(x2^6) - 90;
    expr V = B + 90;
    s.set_polytope();
    barrier_check(x,f,B,0.001);
    //lyapunov_check(x,f,V,0.01);
    return 0;
}

int vdp_print() {
    solver s;
    expr x1 = s.var("x1",-10,10);
    expr x2 = s.var("x2",-10,10);
    vector<expr*> x = {&x1,&x2};
    expr f1 = -x2;
    expr f2 = ((x1^2)-1)*x2+x1;
    vector<expr*> f = {&f1,&f2};
    expr p1 = s.var("p1",40,44);
    expr p2 = s.var("p2",24,26);
    expr p3 = s.var("p3",29,32);
    expr V = p1*(x1^2)-p2*x1*x2+p3*(x2^2)
    +0.246437703822396*(x1^3)+0.342787267928099*(x1^2)*x2
    +0.070061019768681*x1*(x2^2)+0.056167250785361*(x2^3)-9.747135277935248*(x1^4)
    +1.281447375757236*(x1^3)*x2-1.066167940090009*(x1^2)*(x2^2)
    -0.111337393290709*x1*(x2^3)-3.148132699966833*(x2^4)
    -0.058675653184320*(x1^5)-0.088630122702897*(x1^4)*x2
    -0.035603912757564*(x1^3)*(x2^2)-0.092730054611810*(x1^2)*(x2^3)
    +0.030783940378564*x1*(x2^4)-0.016849595361031*(x2^5)
    +1.362207232588218*(x1^6)+1.257918398491556*(x1^5)*x2
    +0.407802497440289*(x1^4)*(x2^2)-1.168667210949858*(x1^3)*(x2^3)
    +1.839303562141088*(x1^2)*(x2^4)-0.729105138802864*x1*(x2^5)
    +0.326281890950742*(x2^6);
    lyapunov_print(x,f,V,0.01,"vdp_3_");
    return 0;
} 

int ptc_print() {
    solver s;
    expr x1 = s.var("x1",-0.1,0.1);
    expr x2 = s.var("x2",-0.1,0.1);
    expr x3 = s.var("x3",-0.1,0.1);
    expr x4 = s.var("x4",-0.1,0.1);
    vector<expr*> x = {&x1,&x2,&x3,&x4};
    expr f1 = 19.079360496000000441654265159741
                *pow((x1 - pow((x1 + 0.89877559179912203113360646966612),2) 
                    + 0.89877559179912203113360646966612),0.5) 
                - 9.07480224*x1 
                + 2.7855072*pow((x1 + 0.89877559179912203113360646966612),2)
                - 8.0049502737159982381646017302046;
    expr f2 =  (4.0*(21.958*x1 - 6.74*pow((x1 + 0.89877559179912203113360646966612),2)
                + 19.369314444725121559631730860929))
                /((19.7622*x3 - 6.066*pow((x3 + 1.0779564350547792273005143215414),2) 
                + 20.973390660839558045758224125166)*(0.4*x2 + x4 + 1.0)) 
                - 4.0*x2 - 4.0;
    expr f3 =   19.079360496000000441654265159741*pow((x1 
                - 1.0*pow((x1 + 0.89877559179912203113360646966612),2) 
                + 0.89877559179912203113360646966612),0.5) 
                - 8.167322016*x3 + 2.50695648*pow((x3 
                + 1.0779564350547792273005143215414),2)
                - 8.6678828923117725491509588664485;
    expr f4 =   0.4*x2;
    vector<expr*> f = {&f1,&f2,&f3,&f4};
    poly V = poly(x,"q",4);
    V.setCofBounds(-100,100);
    lyapunov_print(x,f,V,0.001,"ptc");
    return 0;
}




int simple_print() {
    solver s;
    expr x1 = s.var("x1",-10,10);
    expr x2 = s.var("x2",-10,10);
    vector<expr*> x = {&x1,&x2};
    expr f1 = -x2;
    expr f2 = -x1;
    vector<expr*> f = {&f1,&f2};
    expr p1 = s.var("p1",-10,10);
    expr p2 = s.var("p2",-10,10);
    expr p3 = s.var("p3",-10,10);
    expr V = pow(x1,2)*p1 + pow(x2,2)*p2 + x1*x2*p3;
    lyapunov_print(x,f,V,0.01,"simple");
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

int testLypSyn2() {
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
    syn_ctr_lyp(x,p_f,V.getCofs(),f,V,0.0001);
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
    expr f2 = -(-6*sin(x3)*(x4^2) + 100*u - 10*x2 + 147*cos(x3)*sin(x3))/(5*(3*(cos(x3)^2) - 14));
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

void test3() {
    solver s;
    s.set_delta(0.00001);
    expr x1 = s.var("x1",-0.5,0.5);
    expr x2 = s.var("x2",-0.5,0.5);
    vector<expr*> x = {&x1,&x2};
    expr f1 = -x2;
    expr f2 = -x1;
    vector<expr*> f = {&f1,&f2};
    //poly V = poly(x,"p",2);
    expr p1 = s.var("p1",0,100);
    expr p2 = s.var("p2",0,100);
    expr p3 = s.var("p3",-100,100);
    //V.setCofBounds(-5,5);
    vector<expr*> p = {&p1,&p2,&p3};
    expr V = p1*pow(x1,2) + p2*pow(x2,2) + p3*x1*x2;
    syn_lyp(x,p,f,V,0.05);
}

int main(int argc, char* argv[]) {
    vdp();
    return 0;
}
