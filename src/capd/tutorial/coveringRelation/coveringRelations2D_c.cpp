#include "capd/covrel/HSet2D.h"
#include "capd/capdlib.h"
#include "capd/dynset/C0RectSet.hpp"
#include "capd/dynsys/DynSysMap.h"

using namespace capd;
using namespace capd::dynset;
using namespace capd::dynsys;
using namespace std;
typedef capd::covrel::HSet2D<DMatrix, IMatrix> HSet2D;

template<typename DynSysType, typename GridSet, typename ConditionT,
		typename HSet>
bool moveGridAndCheckCondition(DynSysType & dynsys, const GridSet & grid,
		const ConditionT & condition, const HSet & hset) {

	for (typename GridSet::const_iterator i = grid.begin(); i != grid.end(); ++i) {
		capd::dynset::RectSet<typename GridSet::MatrixType> set(*i, grid.r, grid.C);
		std::cout << "\n set :" << (typename GridSet::VectorType)set;
		set.move(dynsys);
		std::cout << "\n image :" << (typename GridSet::VectorType)set;
		if (!condition(hset, set))
			return false;
	}
	return true;
}
template<typename Map, typename HSet>
bool checkCoveringRelation(Map & f, const HSet & N1, const HSet & N2) {
typedef	typename Map::MatrixType MatrixType;
	typedef capd::covrel::GridSet<MatrixType> GridSet;
	capd::dynsys::DynSysMap<Map> dynsys(f);
	GridSet grid;
	cout << "\nWe check if image of whole set N1 is spanned across the hset N2\n";
	N1.gridSet(grid, 1, 1);
	if(!moveGridAndCheckCondition(dynsys, grid, & capd::covrel::across<HSet,RectSet<MatrixType> >, N2))
	  return false;

	cout << "\n\nWe check if left edge of N1 is mapped to the left of N2\n";
	N1.gridLeftEdge(grid,1);
	if(!moveGridAndCheckCondition(dynsys, grid, & capd::covrel::onLeft<HSet,RectSet<MatrixType> >, N2))
	  return false;

	cout << "\n\nWe check if right edge of N1 is mapped to the right of N2\n";
	N1.gridRightEdge(grid,1);
	if(!moveGridAndCheckCondition(dynsys, grid, & capd::covrel::onRight<HSet,RectSet<MatrixType> >, N2))
	  return false;

	return true;
}
int main() {

	// Rotation by 30 degrees
	IMap f("var:x,y;fun:sqrt(3)/2*x+1/2*y,sqrt(3)/2*y-1/2*x;");

	// h-set N1 = [0,4]x[-0.1, 0.1]
	double c1[] = {2, 0};
	DVector center1(2, c1);
	double m[] = {1, 0,
			      0, 1};
	DMatrix M1(2, 2, m);
	double r1[] = {2, 0.1};
	DVector radius1(2, r1);
	HSet2D N1(center1, M1, radius1);

	// h-set N2 = [1,3]x[-1,1] rotated by 30 degrees
	DVector center2(2);
	center2[0] = sqrt(3);  center2[1] = -1;
	DMatrix M2(2, 2);
	M2[0][0] = M2[1][1] = sqrt(3) / 2;
	M2[1][0] = -0.5;   M2[0][1] = 0.5;
	DVector radius2(2);
	radius2[0] = radius2[1] = 1;
	HSet2D N2(center2, M2, radius2);

	std::cout << "\n COVERING RELATION  N1 => N2 : "
	           << ((checkCoveringRelation(f, N1, N2))? "YES":"NO") << "\n";
	return 0;
}
