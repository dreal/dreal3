#include "capd/facade/DMatrix.h"
#include "capd/facade/IMatrix.h"
#include "capd/facade/IMap.h"

#include "capd/covrel/HSet2D.h"
#include "capd/dynset/RectSet.hpp"
#include "capd/dynsys/DynSysMap.h"
#include "capd/dynset/C0RectSet.hpp"

using namespace capd;
using namespace capd::facade;
typedef capd::covrel::HSet2D<DMatrix, IMatrix> HSet2D;

bool checkCoveringRelation(IMap & f, const HSet2D & N1, const HSet2D & N2) {

	typedef capd::covrel::GridSet<IMatrix> GridSet;
	typedef capd::dynset::RectSet<IMatrix> RectSet;

	// To compute rigorous image of h-set we need discrete dynamical system
	capd::dynsys::DynSysMap<IMap> dynsys(f);

// 1. We check if image of h-set N1 passes through N2 without touching forbidden regions

	// Instead of product of intervals we use RectSet to represent support of h-set
	RectSet set(N1.center(), N1.box(), N1.coordinateSystem());
	set.move(dynsys);
	if (!N2.across(set))
		return false;

// 2. We check if the image of the left edge of N1 is on the left size of N2

	// We make grid containing left edge (in this simple case grid contains only one segment)
	GridSet grid;
	N1.gridLeftEdge(grid, 1);

	// We again use RectSet to avoid wrapping effect when computing its image under map f
	RectSet leftEdge(grid.centers(0), grid.box(), grid.coordinateSystem());
	leftEdge.move(dynsys);

	// in the 2D case we can simply check if leftEdge is to the left of N2
	if (!N2.onLeft(leftEdge))
		return false;

// 3. We check if the image of the left edge of N1 is on the left side of N2

	N1.gridRightEdge(grid, 1);
	RectSet rightEdge(grid.centers(0), grid.box(), grid.coordinateSystem());
	rightEdge.move(dynsys);
	if (!N2.onRight(rightEdge))
		return false;

	return true;
}
int main() {

	IMap f("var:x,y;fun:2*x,0.5*y;");
	//                            |1  0|
	// N = [-2,2]x[-2,4] = (0,1)+ |    | * (B(0,2)xB(0,3))
	//                            |0  1|
	double c[] = { 0, 1 };
	DVector center(2, c);
	double m[] = { 1, 0, 0, 1 };
	DMatrix coordinateSystem(2, 2, m);
	double r[] = { 2, 3 };
	DVector box(2, r);
	HSet2D N(center, coordinateSystem, box);

	std::cout << "\n COVERING RELATION  N =f=> N : ";
	if (checkCoveringRelation(f, N, N))
		std::cout << "YES\n";
	else
		std::cout << "NO\n";
	return 0;
}
