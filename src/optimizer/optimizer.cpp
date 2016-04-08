#include "optimizer.h"

using std::vector;
using std::cerr;

namespace dreal {

optimizer::optimizer(box const & b, vector<Enode*> const & l, Egraph & e): domain(b), egraph(e) {
    //iterate through l and define error functions
    for (auto lit : l) {
	assert(lit->hasPolarity());
	assert(lit->getArity()==2);
	bool pos = (lit->getPolarity()==l_True);
	Enode * left = lit -> get1st();
	Enode * right = lit -> get2nd();
	Enode * f = NULL;
	Enode * f_plain = NULL; //simplified error function for ease of differentiation
	if (pos && lit->isEq()) {
	    f = egraph.mkMinus(left,right);
	    f_plain = f; 
	} else if (!pos && lit->isEq()) {
	    f = egraph.mkNum("0");
	    f_plain = f;
	} else if ( (pos && lit->isLeq()) || (pos && lit->isLt()) 
		    || (!pos && lit->isGeq()) || (!pos && lit->isGt()) ) {
	    f_plain = egraph.mkMinus(left,right);
	    f = egraph.mkPlus(f_plain,egraph.mkAbs(egraph.cons(f_plain)));
	} else if ( (pos && lit->isGeq()) || (pos && lit->isGt()) 
		    || (!pos && lit->isLeq()) || (!pos && lit->isLt()) ) {
	    f_plain = egraph.mkMinus(left,right);
	    f = egraph.mkMinus(f_plain,egraph.mkAbs(egraph.cons(f_plain)));
	}
	cerr<<"f: "<<f;
	cerr<<"f_plain: "<<f_plain;
	error_funcs.push_back(f);
	error_funcs_plain.push_back(f_plain);
    }
}

optimizer::~optimizer() {
    //clean up the traces
}

void optimizer::improve_naive(box& p) { //note that p is a point not a nontrivial box
    Enode * target; //will pick one target error function
    double max_error;
    for (auto f : error_funcs) {
	//evaluate f on p
	//return the max error and target 
    }
    //vector<Enode*> & x //collect all variables
    //for (auto xi : x ) {
	//evaluate the gradient
	//make a newton step on each variable
	//collect the box for the whole step, and check the value interval of the error function
	//if value interval has no zero, push to the learned boxes; the new point is the improved point
	//if value interval has zero, push that box to the top!
    //}
}

}
