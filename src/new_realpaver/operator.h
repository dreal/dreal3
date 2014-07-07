#pragma once

namespace realpaver {

class rp_operator {
public:
    int type;

    // Construction of operator with a priority and an arity
    // (number of variables on which the operator depends)
    rp_operator(int priority, int arity, int pruned_arity);

    // Destruction
    virtual ~rp_operator();

    // Get the priority of the operator
    virtual int priority() const;

    // Variables on which the operator depends
    virtual int arity() const;
    virtual int var(int i) const = 0;

    // Variables that can be pruned by the operator
    virtual int pruned_arity() const;
    virtual int pruned_var(int i) const = 0;

    // Manage the status of the operator during propagation
    int working(int id) const;
    void set_working(int id);
    void set_unworking();

    // Application of operator to reduce the box b
    virtual int apply(rp_box b) = 0;

protected:
    // Copy
    rp_operator(const rp_operator& o);

private:
    int _priority,  /* positive integer representing the priority level        */
        _arity,     /* number of variables on which the operators depends      */
        _pruned,    /* number of variables potentially pruned by the operator  */
        _working;   /* true if the operator must be applied during propagation */

    // Copy protection
    rp_operator& operator=(const rp_operator& o);
};

}
