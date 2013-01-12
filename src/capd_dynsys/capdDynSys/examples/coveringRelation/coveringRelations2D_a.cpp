#include "capd/facade/DMatrix.h"
#include "capd/facade/IMatrix.h"
#include "capd/facade/IMap.h"

#include "capd/covrel/HSet2D.h"
#include "capd/dynset/RectSet.hpp"
#include "capd/dynsys/DynSysMap.h"

using namespace capd;
using namespace capd::facade;

typedef capd::covrel::HSet2D<DMatrix, IMatrix> HSet2D;

bool checkCoveringRelation(IMap & f, const HSet2D & N1, const HSet2D & N2) {

	typedef capd::covrel::GridSet<IMatrix> GridSet;

 std::cout <<  "\n1. We check if image of h-set N passes through N without touching forbidden regions\n";

	IVector set = N1.center() + N1.coordinateSystem() * N1.box();
	IVector setImage = f(set);
	std::cout << "\n  N   = " << set <<"\n  f(N) = " << setImage ;
	if (!N2.across(setImage))
		return false;

	std::cout << "\n\n2. We check if the image of the left edge of N is on the left size of N\n";

	// We make grid containing left edge (in this simple case grid contains only one segment)
	GridSet grid;
	N1.gridLeftEdge(grid, 1);
	IVector leftEdge = grid.centers(0) + grid.coordinateSystem() * grid.box();
	IVector leftEdgeImage = f(leftEdge);
	std::cout << "\n  leftEdge   = " << leftEdge <<"\n  f(leftEdge) = " << leftEdgeImage ;

	// in the 2D case we can simply check if leftEdge is to the left of N2
	if (!N2.onLeft(leftEdgeImage))
		return false;

  std::cout<< "\n\n3. We check if the image of the left edge of N is on the left size of N\n";

	N1.gridRightEdge(grid, 1);
	IVector rightEdge = grid.centers(0) + grid.coordinateSystem() * grid.box();
	IVector rightEdgeImage = f(rightEdge);
	std::cout << "\n  righttEdge   = " << rightEdge <<"\n  f(rightEdge) = " << rightEdgeImage ;
	if (!N2.onRight(rightEdgeImage))
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

	std::cout << "\n We check COVERING RELATION  N =f=> N : \n  where N = [-2,2]x[-2,4]\n" ;
	if (checkCoveringRelation(f, N, N))
		std::cout << "\n\nYES , N=f=>N \n";
	else
		std::cout << "\n\nNO, covering relation cannot be checked.\n";
	return 0;
}
