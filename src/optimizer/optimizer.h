#include "opensmt/egraph/Egraph.h"
#include "util/box.h"

namespace dreal {

class optimizer {
public:
    optimizer(box const &, std::vector<Enode*> const &, Egraph &);
    ~optimizer();
    void improve(box &);

private:
    std::vector<Enode*>	error_funcs;
    std::vector<Enode*>	error_funcs_plain; 
    box const & domain;
    Egraph & egraph;
    std::vector<box*>    point_trace; //all points that have been moved around by the optimizer
    std::vector<box*>    holes; //empty spaces found duing the optimization
    bool    prioritize_me; //this is set to true when optimizer finds a highly likely box
    std::vector<Enode*>  learned; //learned clauses

private:
    void    improve_naive(box &);
    void    learn(std::vector<Enode*>&); //add learned clauses to an external storage
};

}
