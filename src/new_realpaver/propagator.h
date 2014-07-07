#pragma once

#include "interval.h"

namespace realpaver {

class propagator : public operator {
public:
    // Constructor
    rp_propagator(rp_problem * p, double improve = 10, bool verbose = false, std::ostream& o = std::cout);

    // Destructor
    ~rp_propagator();

    // Operator virtual functions
    int priority() const;
    int arity() const;
    int var(int i) const;
    int pruned_arity() const;
    int pruned_var(int i) const;

    // Accessors and modifiers
    double improve() const;
    void set_improve(double x);

    // Insertion of an operator
    void insert(rp_operator * o);

    // Reduction of b using all the operators
    // Useful for the first propagation process
    int apply(rp_box b);

    // Reduction of b initially using only the operators depending on v
    // Useful during search when only one variable is split
    int apply(rp_box b, int v);

private:
    rp_problem * _problem;  /* the problem to be solved                       */
    int _id;                /* identifier of propagation process              */
    rp_vector _vop;         /* vector of all the operators                    */
    rp_dependency _dep;     /* dependency variables-operators                 */
    rp_oqueue_list _queue;  /* priority queue of operators                    */
    rp_box _bsave;          /* used to check domain modifications             */
    double _improve;        /* improvement factor controling propagation      */
    /* percentage e.g. 10% --> propagation if domain  */
    /* width reduced at least by a factor of 10%      */
    int _priority;          /* low priority if expensive application          */
    rp_intset _vars;        /* variables on which the propagator depends      */
    rp_intset _pruned_vars; /* variables that can be pruned by the propagator */

    // Copy protection
    rp_propagator(const rp_propagator& p);
    rp_propagator& operator=(const rp_propagator& p);

    // Application once the working operators have been defined
    int apply_loop(rp_box b);

    // Application of o only if the domain of some variable to be pruned
    // is not precise enough
    int check_precision(rp_operator * o, rp_box b);

    void rp_interval_local(interval i, int digits, int mode);
    void rp_pprint_vars(rp_problem p, rp_box b, int digits, bool exact);
    void rp_union_display(rp_union_interval u, int digits, int mode);
    bool _verbose;
    std::ostream& _out;
};
}
