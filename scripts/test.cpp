#include "dreal.h"
using namespace dreal;
int main() {
    //declare a dReal solver first
    solver s;
    //Declare variables like this, by default they are real values; you can declare integers with ivar(..).
    //Everything is an expression, "expr". There'll be internal type checking.
    expr x = s.var("x");
    //Declare variable with initial domain bounds like this.
    //It's better to put bounds on all variables when possible, otherwise the solver will search in (-inf, inf).
    expr y = s.var("y", -10, 10);
    //Once you have the variables, you can apply functions to them arbitrarily.
    //All the math functions are overloaded; they take expressions and return expressions.
    //You can find all the usable operators at https://github.com/dreal/dreal3/blob/master/src/api/dreal.h#L54
    expr f = exp(x)*tan(y) + sin(y)*x;
    //Now that you have functions, you can use them to make constraints using relation symbols "==,>,<,<=,>=".
    //Add those constraints to the solver. The solver will later solve the conjunction of everything you added.
    s.add(f==0);
    //You can use logical operators "||, &&, !" too, if you need.
    s.add(f==0 || f<0);
    s.add(x<10);
    //Once you've added all the constraints, just do solve(), and you'll see solutions on the output.
    s.solve();
    return 0;
}
