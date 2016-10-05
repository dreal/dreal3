#include <iostream>
#include <vector>
#include <assert.h>
#include <chrono>
#include <random>

#include "dreal.h"

using std::chrono::system_clock;
using std::mt19937_64;

using namespace std;
using namespace dreal;

string subsc(string s, unsigned i) {
    return s+"_"+to_string(i);
}

void fill_in_vars(solver & sol, vector<expr*>& v, string s, unsigned n, double b) {
    for (unsigned i=0; i<n; i++) {
        v.push_back(sol.new_var(subsc(s,i).c_str(),-b,b));
    }
}

void fill_in_vars(solver & sol, vector<expr*>& v, string s, unsigned n) {
    fill_in_vars(sol, v, s, n, 100);
}

double pick_rand(double lb, double ub) {
    static mt19937_64 rg(system_clock::now().time_since_epoch().count());
    uniform_real_distribution<double> m_dist(lb, ub);
    return m_dist(rg);
}

void car(int n) {
    solver s;
    string namex = "x";
    string namey = "y";
    string namea = "a"; //angle
    string namet = "t";
    vector<expr*> x;
    vector<expr*> y;
    vector<expr*> a;
    vector<expr*> t;
    for (unsigned i=0; i<n; i++) {
        x.push_back(s.new_var(subsc(namex,i).c_str(),-100,100));
        y.push_back(s.new_var(subsc(namey,i).c_str(),-100,100));
        a.push_back(s.new_var(subsc(namea,i).c_str(),-100,100));
        t.push_back(s.new_var(subsc(namet,i).c_str(),-100,100));	
    }
    for (unsigned i=0; i<n-2; i++) {
    	//dynamics
        s.add( *x[i+1] < *x[i]+0.001*(sin(*a[i])-pow(*x[i],2)) );
    	s.add( *y[i+1] < *y[i]+0.001*(cos(*a[i])-pow(*y[i],2)) );
    	s.add( *a[i+1] < *a[i]+0.001*(*a[i] + (*x[i]/ *y[i])) );
    	//obstacles
    	s.add( pow(*x[i],2)+pow(*y[i],2) > 3000 );
    	s.add( *x[i]+ *y[i] > 3000);
    }
    expr init = (*x[0] == 0) && (*y[0] < 1) && (*y[0] > -1) && (*a[0]<10) && (*a[0]>-10);
    s.add(init);
    expr goal = (pow(*x[n-1],2) + pow(*y[n-1],2) < 100);
    s.dump_dr_file("car"+to_string(n));
}

void mpc(int n) {
    solver s;
    string namex = "x";
    string namey = "y";
    string namep = "phi"; 
    string named = "delta";
    string namev = "v";
    string nameua = "ua";
    string nameud = "ud";
    string namet = "ud";
    vector<expr*> x;
    vector<expr*> y;
    vector<expr*> p;
    vector<expr*> d;
    vector<expr*> v;
    vector<expr*> ua;
    vector<expr*> ud;
    vector<expr*> t; //keeping track of time
    assert(n>0);
    for (unsigned i=0; i<n; i++) {
        x.push_back(s.new_var(subsc(namex,i).c_str(),-10,10));
        y.push_back(s.new_var(subsc(namey,i).c_str(),-10,10));
        p.push_back(s.new_var(subsc(namep,i).c_str(),-10,10));
        d.push_back(s.new_var(subsc(named,i).c_str(),-10,10));
        v.push_back(s.new_var(subsc(namev,i).c_str(),-10,10));
        ua.push_back(s.new_var(subsc(nameua,i).c_str(),-10,10));	
        ud.push_back(s.new_var(subsc(nameud,i).c_str(),-10,10));	
        t.push_back(s.new_var(subsc(namet,i).c_str(),-10,10));	
    }
    double dt = 0.05;
    double L = 1;
    expr f = s.num(0);
    for (unsigned i=0; i<n-1; i++) {
    	//dynamics
        s.add( *x[i+1] == *x[i] + dt*((*v[i])*cos(*p[i])) ); //xdot = vcos(phi)
    	s.add( *y[i+1] == *y[i] + dt*((*v[i])*sin(*p[i])) ); //ydot = vsin(phi)
	s.add( *p[i+1] == *p[i] + dt*((*v[i])/L)*tan(*d[i]) ); //pdot = tan(delta)*v/L
	s.add( *d[i+1] == *d[i] + dt*(*ud[i]) ); //deltadot = ud
	s.add( *v[i+1] == *v[i] + dt*(*ua[i]) ); //vdot = ua
    	//constraints
    	s.add( (*x[i])<5 && (*x[i])>-5 );
    	s.add( (*y[i])<3 && (*y[i])>-3 );
	s.add( (*ua[i])<1 && (*ua[i])>-1 );
	s.add( (*ud[i])<1 && (*ud[i])>-1 );
	//cost
	f = f+pow(*ua[i],2)+pow(*ud[i],2);
    }
    expr init = (*x[0]==0) && (*y[0]==0) && (*p[0]==1) && (*d[0]==0.5) && (*v[0]==0.1) ; //initial states
    s.add(init);
    s.add(f<2);
    s.set_delta(0.1); 
    s.check();
    //s.dump_dr_file("mpc"+to_string(n));
}

void spheres(int dim, int tuple_size, int num_ctr) {
    solver s;
    vector<expr*> x;
    fill_in_vars(s,x,"x",dim);
    for (unsigned i=0; i<num_ctr; i++) {
        expr f = s.num(1);
        for (unsigned j=0; j<tuple_size; j++) {
            unsigned current_var = floor(pick_rand(0,dim-1));
            f = f + pow((*x[current_var]-pick_rand(-50,50)),floor(pick_rand(1,10)));
        }
        expr ctr = f<=s.num(dim*dim*150*150);
        s.add(ctr);
    }
    s.dump_dr_file("ellipses"+to_string(dim)+"_"+to_string(num_ctr));
}

void prob(int n) {
    solver s;
    vector<expr*> x;
    vector<expr*> d;
    fill_in_vars(s,x,"x",n);
    fill_in_vars(s,d,"d",n,1);
    for (unsigned i=1; i<n-1; i++) {
        expr cx = *x[i+1] == pick_rand(-10,10)*(*x[i])*(*d[i]) + 
                            pick_rand(-10,10)*(*x[i-1])*(1- *d[i]);
        expr cd = *d[i+1] == 1/(1+exp(-*d[i]));
        s.add(cx);
        s.add(cd);
    }
    s.add(*x[floor(n/2)]+ *x[0]+ *x[n-1]==50);
    s.add(*d[floor(n/2)]+ *d[0]+ *d[n-1]<1);
    s.dump_dr_file(subsc("prob",n));
}

void ea_abstract(int n, int d) {
    solver s;
    vector<expr*> x;
    vector<expr*> p;
    fill_in_vars(s,x,"x",n,10);
    fill_in_vars(s,p,"p",n,20);
    expr original = s.num(0);
    expr generalized = s.num(0);
    for (unsigned i=0; i<n-1; i++) {
        original = pick_rand(-5,5)*pow(*x[i],d)*(original+1);
        generalized = generalized+(*p[i])*(*x[i]);
    }
    s.add(original >= pick_rand(-1,1));
    s.add(generalized <= pick_rand(-10,10));
    s.dump_dr_file(subsc(subsc("ea1",n),d));
}

int main() {
    for (unsigned i=19; i<20; i++) {
        mpc(i);
    }
    return 0;
}
