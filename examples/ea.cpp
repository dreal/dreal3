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

void exists_forall(vector<expr*> & exists_vars, vector<expr*> & forall_vars, expr & phi) {
    solver * s = phi.get_solver();
    expr * zero = s->new_num(0);
    s -> push();
    expr verify = !phi;
    cerr<<"search starts with all existential variables set to zero..."<<endl;
    vector<expr*> sol;
    for (auto e : exists_vars) {
	sol.push_back(zero);
	verify = verify && ( *e == *zero );
    }
    s -> add(verify);
    expr search = (*zero <= *zero); //search start with true
    unsigned round = 0;
    cerr<<"verifying the zero solution..."<<endl;
    while (s->check()) {
	cerr<<"---- Round #"<<round++<<" ----"<<endl;
	cerr<<"universal constraints falsified... "<<endl;
	cerr<<"the constraints are:"<<endl;
	s->print_problem();
	sol.clear();
	for (auto u : forall_vars) {
	    sol.push_back(s->new_num((s->get_lb(*u)+s->get_ub(*u))/2));
	}
	search = search && plug_in_solutions(phi,forall_vars,sol,exists_vars);
	cerr<<"with counterexample: ";
	for (unsigned i=0; i<sol.size(); i++) {
	    cerr<<*forall_vars[i]<<":="<<*sol[i]<<" ";
	}
	cerr<<endl;
        //add a bunch of randomly sampled points on x
        unsigned sample = 0;
        std::default_random_engine re(std::random_device {}());
	cerr<<"also some new samples: ";
        while (sample < 5) {
            //clear previous solution
            sol.clear();
            for (auto u : forall_vars) {
		std::uniform_real_distribution<double> unif(s->get_domain_lb(*u), s->get_domain_ub(*u));
                double p = unif(re);
                cerr << *u << ":=" << p << " ";
		sol.push_back(s->new_num(p));
            }
            search = search && plug_in_solutions(phi,forall_vars,sol,exists_vars);
            sample++;
        }
	cerr<<endl;
	s -> pop();
	s -> push();
	s -> add(search);
	cerr<<"search formula: "<<search<<endl;
	cerr << "searching for existential..."<<endl;
	if (!s->check()) {
	    cerr<<"---- Result: unsat ----"<<endl;
	    cerr<<"the constraints are:"<<endl;
	    s->print_problem();
	    return;
	} 
	verify = !phi;
	sol.clear();
	for (auto e : exists_vars) {
	    expr * a = s->new_num((s->get_lb(*e)+s->get_ub(*e))/2);
	    sol.push_back(a);
	    verify = verify && ((*e)==(*a));
	}
	s -> pop();
	s -> push();
	s -> add(verify);
	cerr<<"verify formula: "<<verify<<endl;
	cerr<<"should be the same as: "<<endl;
	s -> print_problem();
	cerr << "verifying the following assignment to the existential variables..."<<endl;
	for (unsigned i=0; i< sol.size(); i++) {
	    cerr<<*exists_vars[i]<<":="<<*sol[i]<<endl;
	}
    }
    cerr<<"--- Result: sat (by the witness above this line) ----"<<endl;
    return;
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
    s.set_polytope(true);
    expr x_in = s.var("x_in",-10,10);
    expr x_out = s.var("x_out",-0.5,0.5);
    expr p1 = s.var("p1",-1,1);
    expr p2 = s.var("p2",-1,1);
    expr p3 = s.var("p3",-1,1);
    expr p4 = s.var("p4",-1,1);
    //parameters are existentially quantified
    vector<expr*> ev = {&p1,&p2,&p3,&p4};
    //x is universally quantified
    vector<expr*> uv = {&x_in,&x_out};
    expr program = ( x_in>p1 && x_out == sin(x_in)+p2 )|| ( x_in<p3 && x_out == sin(-x_in)+p4);
    expr x_out_real = sin(pow(pow(x_in,2),0.5));
    expr spec = implies(program, pow((x_out- x_out_real),2)< eps);
    exists_forall(ev,uv,spec);
}

int main() {
    test2(0.1); 
}


