#include "opensmt/egraph/Egraph.h"
#include "util/box.h"

namespace dreal {
class optimizer {
public:
    optimizer(box &, std::vector<Enode*> const &, Egraph &, SMTConfig &);
    ~optimizer();
    bool improve(box &);
    void set_domain(box &);
private:
    std::vector<Enode*>	error_funcs;
    std::map<Enode*,Enode*> plainf; //simpler version for differentiation
    box & domain;
    Egraph & egraph;
    SMTConfig & config;
    std::vector<box*>    point_trace; //all points that have been moved around by the optimizer
    std::vector<box*>    holes; //empty spaces found duing the optimization
    bool    prioritize_me; //this is set to true when optimizer finds a highly likely box
    std::vector<Enode*>  learned; //learned clauses
private:
    bool    improve_naive(box &);
    void    learn(std::vector<Enode*>&); //add learned clauses to an external storage
};
}