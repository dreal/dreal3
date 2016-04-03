#ifndef _BRANCHER_H
#define _BRANCHER_H
#include <vector>
#include <memory>
#include "util/scoped_vec.h"
#include "util/box.h"
#include "contractor/contractor.h"
using std::shared_ptr;
using std::vector;

namespace dreal {
    class BranchHeuristic {
        public:
            vector<int> sort_branches(box const &, scoped_vec<shared_ptr<constraint>>&, double) const;
            virtual vector<double> score_axes(box const & b, scoped_vec<shared_ptr<constraint>>&) const =0;
    };

    class SizeBrancher: public BranchHeuristic {
        public:
            vector<double> score_axes(box const & b, scoped_vec<shared_ptr<constraint>>&) const ;
    };

    class SizeGradAsinhBrancher: public BranchHeuristic {
        public:
            SizeGradAsinhBrancher(double c1 = 1000, double c2 = 1000, double c3 = 0.01) :
                c1(c1), c2(c2), c3(c3) {};
            vector<double> score_axes(box const & b, scoped_vec<shared_ptr<constraint>>&) const;
        private:
            const double c1;
            const double c2;
            const double c3;
    };
}
#endif //_BRANCHER_H
