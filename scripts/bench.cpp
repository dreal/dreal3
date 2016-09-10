#include<iostream>
#include<vector>
#include<assert.h>
#include<ctime>
#include<cstdlib>

#include "dreal.h"

using namespace std;
using namespace dreal;

string subsc(string s, unsigned i) {
    return s+"_"+to_string(i);
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
    	s.add( pow(*x[i],2)+pow(*y[i],2) < 3000 );
    	s.add( *x[i]+ *y[i] < 3000);
    }
    expr init = (*x[0] == 0) && (*y[0] < 1) && (*y[0] > -1) && (*a[0]<10) && (*a[0]>-10);
    s.add(init);
    expr goal = (pow(*x[n-1],2) + pow(*y[n-1],2) < 100);
    s.dump_dr_file("car"+to_string(n));
}

int main() {
    for (unsigned i=10; i<100; i++) {
        car(i);
    }
    cout<<endl;
    return 0;
}
