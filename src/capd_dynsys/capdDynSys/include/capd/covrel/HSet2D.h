

/////////////////////////////////////////////////////////////////////////////
/// @file HSet2D.h
///
/// @author Daniel Wilczak, Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_COVREL_HSET2D_H_
#define _CAPD_COVREL_HSET2D_H_

#include <vector>
#include <stdexcept>
#include <iostream>
#include "capd/covrel/HSetMD.hpp"
#include "capd/dynset/C0Set.h"


namespace capd {
namespace covrel {
/// @addtogroup covrel
/// @{

/// Converts two column vectors to given MatrixType
///
/// Example:  convertColumnsTo<DMatrix>( v1, v2);
template <typename MatrixType, typename VectorType>
MatrixType convertColumnsTo(const VectorType & column1, const VectorType & column2){
	MatrixType A(2,2);
	A(1,1)=column1[0]; A(2,1)= column1[1];
	A(1,2)=column2[0]; A(2,2)= column2[1];
	return A;
}
///
/// This class provides a h-set in R^2 with one unstable and one stable direction.
///
template<typename MatrixT, typename IMatrixT>
class HSet2D: public HSetMD<MatrixT, IMatrixT> {
public:
  typedef	typename MatrixT::RowVectorType VectorType;
	typedef typename IMatrixT::RowVectorType IVectorType;
	typedef typename IVectorType::ScalarType ScalarType;
	typedef typename VectorType::ScalarType BoundType;
	typedef MatrixT MatrixType;
	typedef IMatrixT IMatrixType;
	typedef HSetMD<MatrixType, IMatrixType> BaseHSet;

	HSet2D() {}

	/// we assume that the set is represented as center + C * B(0, r)
	/// first column of C represent unstable direction
	/// second column of C represent stable direction
	HSet2D(const VectorType& center, const MatrixType& C, const VectorType& r)
	: HSetMD<MatrixType, IMatrixType>(center, C , 1, 1 ,r) {
	}

	/// we assume that the set is represented as center + C * B(0, r)
	/// first column of C represent  unstable direction
	/// second column of C represent  stable direction
	HSet2D(const IVectorType & center, const IMatrixType & C, const VectorType& r)
	: BaseHSet(center, C , 1, 1, r) {
	}
	/// Creates HSet from given center, unstable and stable directions and their scales
	HSet2D(const VectorType & center,
			   const VectorType & unstableDirection, const VectorType & stableDirection,
			   const VectorType& scales
    ) : BaseHSet(center, convertColumnsTo<MatrixType>(unstableDirection,stableDirection),
				 1, 1, scales) {
	}
	/// Creates HSet from given center, unstable and stable directions and their scales
	HSet2D(const IVectorType & center,
		   const IVectorType & unstableDirection, const IVectorType & stableDirection,
		   const VectorType& radius)
	   : BaseHSet(center, convertColumnsTo<IMatrixType>(unstableDirection,stableDirection),
			      1, 1, radius) {
	}
	~HSet2D() {}

	typename IMatrixType::RefColumnVectorType  unstableDirection() const{
		return this->m_IB.column(0);
	}
	typename IMatrixType::RefColumnVectorType stableDirection() const {
			return this->m_IB.column(1);
	}

	bool onLeft (const VectorType &point) const {
		VectorType x = this->transformToHSetCoordinates(point);
		return x[0] < -this->m_r[0];
	}
	bool onRight (const VectorType &point) const {
		VectorType x = this->transformToHSetCoordinates(point);
		return x[0] > this->m_r[0];
	}


  bool onLeft (const IVectorType & set) const {
	  IVectorType x = this->transformToHSetCoordinates(set);
    return x[0] < -this->m_r[0];
	}
	bool onRight (const IVectorType &set) const {
		IVectorType x = this->transformToHSetCoordinates(set);
		return x[0] > this->m_r[0];
	}
	template <typename SetT>
	bool onLeft (const SetT & A_set) const {
		IVectorType x = A_set.affineTransformation(this->m_invIB, this->m_Ix);
	  return x[0] < -this->m_r[0];
	}
	template <typename SetT>
	bool onRight (const SetT & A_set) const {
		IVectorType x = A_set.affineTransformation(this->m_invIB,this->m_Ix);
    return x[0] > this->m_r[0];
	}


	/**
	 * in the \c grid it returns uniform grid of the given face
	 *
	 * @param gridSize          number of pieces in the grid
	 * @param coordinateToFix   which wall should be grided
	 * @param sideOfBox         which side of given coordinate should be grided : 0 - both, -1 - left, 1 - right
	 * @param totalDimension    dimension of the space (can be bigger than 2 if we embed the set)
	 * @param d1, d2            if hset is embedded in higher dimension
	 *                          then we put first coordinate in d1 coordinate, second in d2 and the rest set to 0.
	 */
	template<typename IMatrix>
	GridSet<IMatrix>& gridFace(GridSet<IMatrix>& grid, int gridSize, int coordinateToFix, Side sideOfBox,
			int totalDimension = 2, int d1=0, int d2=1) const {
		std::vector<int> indexes(2);
		indexes[0] = d1; indexes[1] = d2;
		std::vector<int> gridSizes(2);
		gridSizes[1-coordinateToFix] = gridSize;
		return BaseHSet::gridFace(grid, gridSizes, indexes, totalDimension, coordinateToFix, sideOfBox);
	}
	template<typename IMatrix>
	GridSet<IMatrix>& gridLeftEdge(GridSet<IMatrix>& G, int gridSize, int totalDimension = 2, int d1=0, int d2=1) const {
		return gridFace(G, gridSize, 0, leftSide, totalDimension, d1, d2);
	}
	template<typename IMatrix>
	GridSet<IMatrix>& gridRightEdge(GridSet<IMatrix>& G, int gridSize, int totalDimension = 2, int d1=0, int d2=1) const {
		return gridFace(G, gridSize, 0, rightSide, totalDimension, d1, d2);
	}
	template<typename IMatrix>
	GridSet<IMatrix>& gridBottomEdge(GridSet<IMatrix>& G, int gridSize, int totalDimension = 2, int d1=0, int d2=1) const {
		return gridFace(G, gridSize, 1, leftSide, totalDimension, d1, d2);
	}

	template<typename IMatrix>
	GridSet<IMatrix>& gridTopEdge(GridSet<IMatrix>& G, int gridSize, int totalDimension = 2, int d1=0, int d2=1) const {
		return gridFace(G, gridSize, 1, rightSide, totalDimension, d1, d2);
	}
	template<typename IMatrix>
	GridSet<IMatrix>& gridSet(GridSet<IMatrix>& G, int grid1, int grid2, int totalDimension=2, int d1=0, int d2=1) const {
		std::vector<int> indexes(2);
		indexes[0] = d1; indexes[1] = d2;
		std::vector<int> gridSizes(2);
		gridSizes[0] = grid1; gridSizes[1] = grid2;
		return BaseHSet::gridSet(G, gridSizes, indexes, totalDimension);
	}
	virtual std::string show(void) const{
	  return std::string("HSet2D : ") + this->showInfo();
	}

};

struct CheckCoveringRelation2DParameters {
	CheckCoveringRelation2DParameters(int xGrid = 1, int yGrid = 1, int leftGrid = 1, int rightGrid = 1)
	: xGrid(xGrid), yGrid(yGrid), leftGrid(leftGrid), rightGrid(rightGrid){
	}
  int xGrid, yGrid;
	int leftGrid;
	int rightGrid;
};

template<typename C0SetType, typename DynSysT, typename MatrixT, typename IMatrixT>
bool checkCoveringRelation2D(
		DynSysT & dynsys,
		const capd::covrel::HSet2D<MatrixT,IMatrixT> & N1,
		const capd::covrel::HSet2D<MatrixT,IMatrixT> & N2,
		const CheckCoveringRelation2DParameters & param = CheckCoveringRelation2DParameters(1, 1, 1, 1)
) {

	typedef IMatrixT MatrixType;
	typedef capd::covrel::GridSet<MatrixType> GridSet;
	typedef capd::covrel::HSet2D<MatrixT,IMatrixT> HSetType;

	GridSet grid;
	N1.gridSet(grid, param.xGrid, param.yGrid);
	if(!moveGridAndCheckCondition<C0SetType>(dynsys, grid, & capd::covrel::across<HSetType, C0SetType >, N2)){
		std::cout << "\n ACROSS\n\n";
		return false;
	}

	N1.gridLeftEdge(grid, param.leftGrid);
	if(!moveGridAndCheckCondition<C0SetType>(dynsys, grid, & capd::covrel::onLeft<HSetType, C0SetType >, N2)){
		std::cout << "\n LEFT\n\n";
		return false;
	}

	N1.gridRightEdge(grid,param.rightGrid);
	if(!moveGridAndCheckCondition<C0SetType>(dynsys, grid, & capd::covrel::onRight<HSetType, C0SetType >, N2)){
		std::cout << "\n RIGHT\n\n";
		return false;
	}

	return true;
}

/// @}
}} // namespace capd::covrel

#endif // _CAPD_COVREL_HSET2D_H_


