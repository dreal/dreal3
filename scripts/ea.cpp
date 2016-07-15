#include "dreal.hh"
#include <random>

using namespace std;
using namespace dreal;

expr plug_in_solutions(expr & formula, vector<expr*>& x, vector<expr*> & sol, vector<expr*> & p) {
    vector<expr*> full_pre;
    vector<expr*> full_post;
    full_pre.reserve(x.size()+p.size()+2);
    full_post.reserve(sol.size()+p.size()+2);
    // full_pre holds the list of variables
    full_pre.insert(full_pre.end(), x.begin(), x.end());
    full_pre.insert(full_pre.end(), p.begin(), p.end());
    // full_post holds the list of assignments
    full_post.insert(full_post.end(), sol.begin(), sol.end());
    full_post.insert(full_post.end(), p.begin(), p.end());
    //substitute
    return substitute(formula, full_pre, full_post);
}

void exists_forall(vector<expr*> & exists_vars, vector<expr*> & forall_vars, 
	vector<expr*> & free_uvars, vector<expr*> & derived_uvars, expr & phi) {
    solver * s = phi.get_solver();
    expr * zero = s->new_num(0);
    vector<expr*> rest_vars = derived_uvars;
    rest_vars.insert(rest_vars.end(), exists_vars.begin(), exists_vars.end());
    s -> push();
    expr verify = !phi;
    unsigned round = 0;
    cerr<<"---- Round #"<<round++<<" ----"<<endl;
    cerr<<"search starts with all existential variables set to zero..."<<endl;
    vector<expr*> sol;
    for (auto e : exists_vars) {
	sol.push_back(zero);
	verify = verify && ( *e == *zero );
    }
    s -> add(verify);
    cerr<<"added the following formula for verification step: "<<verify<<endl;
    expr search = (*zero <= *zero); //search start with true (sorry should be cleaner)
    cerr<<"verifying the zero solution..."<<endl;
    while (s->check() && round<4) {
	cerr<<"universal constraints falsified... "<<endl;
	cerr<<"printing the verification constraints solved:"<<endl<<"[";
	s->dump_formulas(cerr);
	cerr<<"]"<<endl;
	cerr<<"---- Round #"<<round++<<" ----"<<endl;
	sol.clear();
	for (auto u : forall_vars) {
	    sol.push_back(s->new_num((s->get_lb(*u)+s->get_ub(*u))/2));
	}
	search = search && plug_in_solutions(phi,forall_vars,sol,exists_vars);
	cerr<<"with counterexample: ";
	for (unsigned i=0; i<sol.size(); i++) {
	    cerr<<*forall_vars[i]<<":="<<*sol[i]<<" ";
	}
        //add a bunch of randomly sampled points on x
        unsigned sample = 0;
        std::default_random_engine re(std::random_device {}());
	cerr<<"also some new samples: ";
        while (sample < 3) {
            //clear previous solution
            sol.clear();
            for (auto u : free_uvars) {
		std::uniform_real_distribution<double> unif(s->get_domain_lb(*u), s->get_domain_ub(*u));
                double p = unif(re);
                cerr << *u << ":=" << p << " ";
		sol.push_back(s->new_num(p));
            }
            search = search && plug_in_solutions(phi,free_uvars,sol,rest_vars);
            sample++;
        }
	cerr<<endl;
	s -> pop();
	s -> push();
	s -> add(search);
	cerr<<"added the following formula for search step:"<<endl<<"["<<search<<"]"<<endl;
	cerr << "searching for existential..."<<endl;
	if (!s->check()) {
	    cerr<<"---- Result: unsat ----"<<endl;
	    cerr<<"the constraints are:"<<endl;
	    s->dump_formulas(cerr);
	    return;
	}
	cerr << "printing the search problem solved:"<<endl<<"[";
	s -> dump_formulas(cerr); 
	cerr << "]"<<endl;
	verify = !phi;
	sol.clear();
	for (auto e : exists_vars) {
	    expr * a = s->new_num((s->get_lb(*e)+s->get_ub(*e))/2);
	    sol.push_back(a);
	}
	verify = plug_in_solutions(phi,exists_vars,sol,forall_vars);
	s -> pop();
	s -> push();
	s -> add(verify);
	cerr<<"added the following formula for verification step:"<<endl<<"["<<verify<<"]"<<endl;
	cerr << "verifying the following assignment to the existential variables..."<<endl;
	for (unsigned i=0; i< sol.size(); i++) {
	    cerr<<*exists_vars[i]<<":="<<*sol[i]<<endl;
	}
    }
    cerr<<"--- Result: sat (by the witness above this line) ----"<<endl;
    return;
}

void exists_forall(vector<expr*> & exists_vars, vector<expr*> & forall_vars, expr & phi) {
    vector<expr*> tmp;
    exists_forall(exists_vars,forall_vars,forall_vars,tmp,phi);
}

void test1() {
    solver s;
    expr x = s.var("x", -10, 10);
    vector<expr*> xv = {&x};
    expr y = s.var("y", -10, 5);
    vector<expr*> yv = {&y};
    expr phi = x>y;
    expr psi = pow(y,2)<x;
    exists_forall(xv,yv,phi);
}


void test2(double eps) {
    solver s;
    s.set_delta(eps*0.1);
    s.set_polytope(true);
    expr x_in = s.var("x_in",-1,1);
    expr x_out = s.var("x_out",-1,1);
    expr x_out_real = s.var("x_out_real",-1,1);
    expr p1 = s.var("p1",0,0.1);
    expr p2 = s.var("p2",-0.1,0.1);
    expr p3 = s.var("p3",0,0.1);
    expr p4 = s.var("p4",-0.1,0.1);
    //parameters are existentially quantified
    vector<expr*> ev = {&p1,&p2,&p3,&p4};
    //x is universally quantified
    vector<expr*> uv = {&x_in,&x_out,&x_out_real};
    vector<expr*> fuv = {&x_in};
    vector<expr*> duv = {&x_out,&x_out_real};
    expr program = ( (!(x_in>-p1)) || x_out == sin(x_in)+p2 ) && ( (!(x_in<p3)) || x_out == sin(-x_in)+p4);
    expr func = (x_out_real == sin(abs(x_in)));
    expr spec = (p1 > 0.0000001) && (p1 < 0.001) && (abs(p2) < 0.0001) && p2>0.000001 && (p3<0.000001) && (p1<p3) && p4>0.1 && ( (! (program && func) )|| pow((x_out- x_out_real),2)< (s.num(eps)));
    exists_forall(ev,uv,fuv,duv,spec);
}

int main() {
    test1();
//    test2(0.0001); 
}


