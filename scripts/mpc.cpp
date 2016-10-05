#include <iostream>
#include <vector>
#include <assert.h>
#include <string>
#include "dreal.h"

using namespace std;
using namespace dreal;

string sub(string s, unsigned i) {
    return s+"_"+to_string(i);
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
    assert(n>0);
    for (unsigned i=0; i<n; i++) {
        x.push_back(s.new_var(sub(namex,i).c_str(),-10,10));
        y.push_back(s.new_var(sub(namey,i).c_str(),-10,10));
        p.push_back(s.new_var(sub(namep,i).c_str(),-10,10));
        d.push_back(s.new_var(sub(named,i).c_str(),-10,10));
        v.push_back(s.new_var(sub(namev,i).c_str(),-10,10));
        ua.push_back(s.new_var(sub(nameua,i).c_str(),-10,10));	
        ud.push_back(s.new_var(sub(nameud,i).c_str(),-10,10));	
    }
    double dt = 0.1;
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
    s.solve();
    //s.dump_dr_file("mpc"+to_string(n));
}

int main() {
    for (unsigned i=1; i<11; i++) {
	cerr<<"i: "<<i<<endl;
        mpc(i);
    }
    return 0;
}



