//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file MapGraph.h
///
/// @author Tomasz Kapela   @date 2009-12-09
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INVSET_MAPGRAPH_H_
#define _CAPD_INVSET_MAPGRAPH_H_
#include <limits>
#include "capd/vectalg/Vector.hpp"
#include "capd/invset/CubicalMap.h"
#include "capd/invset/Graph.h"

namespace capd{
namespace invset{



//typedef ZVectorMD Point;

template <class PointT>
struct less {

  bool operator()(const PointT& x, const PointT& y) const {
    for(int i = 0; i < x.size(); ++i) {
      if(x[i] > y[i])
        return false;
      if(x[i] < y[i])
        return true;
    }
    return false;
  }
};


template <>
struct less<capd::vectalg::Vector<short int,2> >{
  bool operator()(const capd::vectalg::Vector<short int,2> & x, const capd::vectalg::Vector<short int,2> & y)  //   std::cout << "min : "<<(min) << " max :"<< (max)<< " xmin : " << (xmin) << " xmax : " << (xmax)<<std::endl;
const {
    return (x[0]<y[0]) || ((x[0]==y[0]) && (x[1]<y[1]));
  }
};

template <typename VectorT, typename MatrixT>
struct MapGraphNodeData {
  typedef VectorT VectorType;
  typedef MatrixT MatrixType;

  MatrixType* m_coordSystem;
  MatrixType* m_invCoordSystem;
  VectorType* m_diagQuadForm;
  MapGraphNodeData() :
    m_coordSystem(0), m_invCoordSystem(0), m_diagQuadForm(0) {
  }

  ~MapGraphNodeData() {
    if(m_coordSystem)
      delete m_coordSystem;
    if(m_invCoordSystem)
      delete m_invCoordSystem;
    if(m_diagQuadForm)
      delete m_diagQuadForm;
  }
};

template <class MapT, class VertexT = capd::vectalg::Vector<int, 0>, class lessT = less<VertexT> , class ResolutionT = VertexT>
class MapGraph : public CubicalMap<MapT, Graph<VertexT, lessT, MapGraphNodeData<typename MapT::VectorType, typename MapT::MatrixType> >, ResolutionT>{
public:
  typedef MapT MapType;
  typedef typename MapType::VectorType VectorType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename VectorType::ScalarType ScalarType;
  typedef typename ScalarType::BoundType BoundType;
  // typedef typename MapType::DerivativeContainer DerivativeContainer;  //????
  typedef MapGraphNodeData<VectorType, MatrixType> NodeData;
  typedef VertexT VertexType;
  typedef Graph<VertexType, lessT,  NodeData> GraphType;
  typedef CubicalMap<MapType, GraphType , ResolutionT> CubicalMapType;

  typedef typename GraphType::OrderType OrderType;
  typedef typename GraphType::VertexSet VertexSet;

  typedef ResolutionT ResolutionType;

  typedef typename CubicalMapType::iterator iterator;
  typedef typename CubicalMapType::const_iterator const_iterator;
  using CubicalMapType::begin;
  using CubicalMapType::end;

  MapGraph(MapType & map, const ResolutionType & resolution) : CubicalMapType(map, resolution){
  }

  void saveCoordSys(const char* fileName) const {
      capd::rounding::DoubleRounding::roundNearest();
      std::ofstream file;
      file.open(fileName);
      file.precision(20);
      const_iterator b = this->begin(), e = this->end();
      while(b != e) {
        file << b->first;
        if(b->second.m_coordSystem)
          file << " " << *(b->second.m_coordSystem);
        if(b->second.m_invCoordSystem)
          file << " " << *(b->second.m_invCoordSystem);
        if(b->second.m_diagQuadForm)
          file << " " << *(b->second.m_diagQuadForm);
        ++b;
        if(b != e)
          file << "\n";
      }
      file.close();
    }

    void loadCoordSys(const char* fileName) {
      capd::rounding::DoubleRounding::roundNearest();
      std::ifstream file;
      file.open(fileName);
      int dim = this->getResolution().dimension();
      VertexType temp(dim);
      do {
        file >> temp;

        this->nodes()[temp].m_coordSystem = new MatrixType(dim, dim);
        this->nodes()[temp].m_invCoordSystem = new MatrixType(dim, dim);
        this->nodes()[temp].m_diagQuadForm = new VectorType(dim);
        file >> *(this->nodes()[temp].m_coordSystem);
        file >> *(this->nodes()[temp].m_invCoordSystem);
        file >> *(this->nodes()[temp].m_diagQuadForm);
        file.get();
      } while(!file.eof());
      file.close();
    }
};



}} // end of namespace capd::invset

#endif // _CAPD_INVSET_MAPGRAPH_H_

