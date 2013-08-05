//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file CubicalMap.h
///
/// @author Tomasz Kapela   @date 2009-12-09
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INVSET_CUBICALMAP_H_
#define _CAPD_INVSET_CUBICALMAP_H_
#include <iostream>
#include <list>
#include <vector>
#include <fstream>
#include "capd/vectalg/iobject.hpp"
#include "capd/auxil/logger.h"
#include "capd/invset/Scope.h"

namespace capd {
namespace invset {

template <class MapT, class GraphT, class ResolutionT = typename GraphT::VertexType>
class CubicalMap : public GraphT {
public:
  typedef MapT MapType;
  typedef typename MapType::VectorType VectorType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename VectorType::ScalarType ScalarType;
  typedef typename ScalarType::BoundType BoundType;
  // typedef typename MapType::DerivativeContainer DerivativeContainer;  //????

  typedef GraphT GraphType;
  typedef typename GraphType::OrderType OrderType;
  typedef typename GraphType::VertexSet VertexSet;
  typedef typename GraphType::VertexType VertexType;

  typedef ResolutionT ResolutionType;

  typedef typename GraphType::iterator iterator;
  typedef typename GraphType::const_iterator const_iterator;
  using GraphType::begin;
  using GraphType::end;

  ///deprecated
  typedef typename GraphType::VertexSet SetVertex;

  CubicalMap(MapType & map, const ResolutionType & resolution) :
    m_f(map), m_resolution(resolution) {
  }

  const ResolutionType & getResolution() const {
    return m_resolution;
  }

  MapType & getMap() {
    return m_f;
  }

  static VertexType resolutionToDenominator(const ResolutionType & resolution) {
    VertexType result(resolution.dimension());
    for(int i = 0; i < resolution.dimension(); ++i)
      result[i] = (1 << int(resolution[i]));
    return result;
  }

  static VectorType vertexToVector(const VertexType& vertex,
      const VertexType& denominator) {
    VectorType result(vertex.dimension());
    for(int i = 0; i < vertex.dimension(); ++i)
      result[i] = ScalarType(int(vertex[i]), int(vertex[i]) + 1)
          / int(denominator[i]);
    return result;
  }
  /// converts VertexType to Cube using current resolution
  VectorType vertexToCube(const VertexType& vertex) const {
    VectorType result(vertex.dimension());
    for(int i = 0; i < vertex.dimension(); ++i)
      result[i] = ScalarType(ldexp(BoundType(vertex[i]), -m_resolution[i]), // ldexp(x, n) = x * 2^n
          ldexp(BoundType(vertex[i] + 1), -m_resolution[i]));
    return result;
  }
  /// converts VertexType to Cube using given resolution
  static VectorType vertexToCube(const VertexType& vertex,
      const ResolutionType & resolution) {
    VectorType result(vertex.dimension());
    for(int i = 0; i < vertex.dimension(); ++i)
      result[i] = ScalarType(ldexp(BoundType(vertex[i]), -resolution[i]), // ldexp(x, n) = x * 2^n
          ldexp(BoundType(vertex[i] + 1), -resolution[i]));
    return result;
  }
  template <class PointVector>
  void getCubeCenter(const VertexType& vertex, PointVector& result) {
    for(int i = 0; i < vertex.dimension(); ++i)
      result[i] = ldexp((BoundType(vertex[i]) + 0.5), m_resolution[i]);
  }
  template <class PointVector>
  static void getCubeCenter(const VertexType& vertex,
      const ResolutionType & resolution, PointVector& result) {
    for(int i = 0; i < vertex.dimension(); ++i)
      result[i] = ldexp((BoundType(vertex[i]) + 0.5), resolution[i]);
  }
  template <class PointVector>
  static void centreOfCube(const VertexType& vertex, const VertexType& denominator,
      PointVector& result) {
    for(int i = 0; i < vertex.dimension(); ++i)
      result[i] = (double(vertex[i]) + 0.5) / int(denominator[i]);
  }

  static void insertVertexIfNotExists(GraphType & G, const VertexType & v) {
    G.nodes().insert(std::make_pair(v, GraphType::Node::getEmptyNode())); // we assume that insert do not change anything if key already exists (like in std::map)
  }
  static void insertVertexIfNotExists(VertexSet & G, const VertexType & v) {
    G.insert(v); // we assume that insert do not change anything if key already exists (like in std::set)
  }

  /// it grids domain with given resolution and for each box adds corresponding vertex to set G
  /// G can be either graph (GraphType) or only set of vertices (VertexSet)
  template <typename SetType>
  static void createGrid(SetType & G, const ResolutionType & resolution,
      const VectorType & domain) {
    int dim = domain.dimension();
    VertexType leftBottomCorner(dim), rightTopCorner(dim);
    typedef typename ResolutionType::ScalarType IntType;
    for(int i = 0; i < dim; ++i) {
      typename VectorType::ScalarType::BoundType lb = ldexp(
          domain[i].leftBound(), (int) resolution[i]), rb = ldexp(
          domain[i].rightBound(), (int) resolution[i]);
      leftBottomCorner[i] = static_cast<IntType> (floor(lb));
      rightTopCorner[i] = static_cast<IntType> (ceil(rb));
      // these numbers can be same! So we must assure that at least one element is added
      if(leftBottomCorner[i] == rightTopCorner[i])
        rightTopCorner[i] = rightTopCorner[i] + 1;

      //#define __DEBUG_MODE__
#ifdef __DEBUG_MODE__
      if( -lb > std::numeric_limits<IntType>::max()) {
        std::cout << "Left end cannot be encoded using given VertexType type : " << lb;
        throw 1;
      }
      if( rb > std::numeric_limits<IntType>::max()) {
        std::cout << "Right end cannot be encoded using given VertexType type : " << rb;
        throw 2;
      }
#endif
    }

    VertexType coeffs = leftBottomCorner;
    int k = dim - 1; // k indicates coordinates which was increased in current iteration
    while(k >= 0) { // k<0 everything was added
      insertVertexIfNotExists(G, coeffs);
      k = dim - 1; // try to increase last coordinate
      while(k >= 0) { // k<0 everything was added
        coeffs[k]++;
        if(coeffs[k] >= rightTopCorner[k]) { // this coordinate cannot be increased (we reach the right bound)
          coeffs[k] = leftBottomCorner[k]; // so we reset it
          --k; // and try to increase previous coordinate
        } else
          break; // coordinate successfully increased
      }
    }
  }

  /// it grids domain with given resolution and for each box adds corresponding vertex to graph
  void setDomain(const VectorType & domain) {
    this->clear();
    createGrid(*this, m_resolution, domain);
  }

  template <typename SetType>
  static void createGrid(SetType & G, const ResolutionType & resolution,
      const std::list<VectorType> & domain) {
    typename std::list<VectorType>::const_iterator b = domain.begin(), e =
        domain.end();
    while(b != e) {
      createGrid(G, resolution, *b);
      ++b;
    }
  }

  /// it grids domain with given resolution and for each box adds corresponding vertex to graph G
  void setDomain(const std::list<VectorType> & domainList) {
    this->clear();
    createGrid(*this, this->m_resolution, domainList);
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////
  ///
  ///  Creates graph that is a cubical representation of the map f with given resolution
  ///  It also creates transposed graph
  ///
  ///  we assume that:
  ///      - domain is already set
  ///      - all edges in a graph are removed
  ///
  /////////////////////////////////////////////////////////////////////////////////////////////////
  static void constructCubicalMap(MapType & m_f, GraphType & graph,
      ResolutionType & resolution) {
    typename GraphType::iterator b = graph.begin(), e = graph.end();

    while(b != e) {
      VectorType x = vertexToCube(b->first, resolution);
      std::list<VectorType> enc;
      m_f.eval(x, enc);
      typename GraphType::VertexSet & cubicalImage = b->second.outEdges;
      typename std::list<VectorType>::iterator it = enc.begin();
      while(it != enc.end()) {
        createGrid(cubicalImage, resolution, *it);
        ++it;
      }
      typename GraphType::VertexSet::iterator cube = cubicalImage.begin();
      while(cube != cubicalImage.end()) {
        graph.nodes()[*cube].inEdges.insert(b->first);
        ++cube;
      }
      ++b;
    }
  }

  void constructCubicalMap() {
    //constructCubicalMap(begin(), end(), *this);
    constructCubicalMap(m_f, *this, m_resolution);
  }

  /* /// TODO:  czy zakladamy ze b i e dotycza g???
   void constructCubicalMap(iterator b, iterator e, GraphType& g) {
   while(b != e) {
   VectorType x = vertexToCube(b->first);
   std::list<VectorType> enc;
   m_f.eval(x, enc);
   GraphType vg;
   typename std::list<VectorType>::iterator it = enc.begin();
   while(it != enc.end()) {
   createGrid(vg, m_resolution, *it);
   ++it;
   }
   iterator k = vg.begin();
   while(k != vg.end()) {
   b->second.outEdges.insert(k->first);
   //if(g.nodes().find(k->first) == g.nodes().end())
   //  g.nodes()[k->first] = typename GraphType::Node();
   g.nodes()[k->first].inEdges.insert(b->first);
   ++k;
   }
   ++b;
   }
   }
   */

  /// checks whenever set x is contained (at least partly) in the domain.
  /*static bool isInDomain(const VectorType & cube,
      const std::list<VectorType> & domain) {
    typename std::list<VectorType>::const_iterator domainComponent =
        domain.begin();
    while(domainComponent != domain.end()) {
      if(!capd::vectalg::intersectionIsEmpty(cube, *domainComponent)) {
        return true;
      }
      ++domainComponent;
    }
    return false;
  }*/

/**
 *
 *  Creates graph that is a cubical representation of the map f with given resolution
///  Edges pointing out of range are not created.
///  It also creates inverted graph
///
///  we assume that:
///      - domain is already set
///      - all edges in a graph are removed
///
*/
  /*static void constructCubicalMap(CubicalMap & graph, const std::list<VectorType> & range) {
    sbug << "\t-> constructCubicalMap(graph, range)" << std::endl;
    CubicalMap::iterator b = graph.begin(), e = graph.end();
    while(b != e) {
      VectorType x = vertexToCube(b->first, graph.getResolution());
      std::list<VectorType> intervalImage;Region
      graph.m_f.eval(x, intervalImage);
      typename GraphType::VertexSet & cubicalImage = b->second.outEdges;
      typename std::list<VectorType>::iterator it = intervalImage.begin();
      while(it != intervalImage.end()) {
        if(isInDomain(*it, range)) {
          createGrid(cubicalImage, graph.getResolution(), *it);
        }
        ++it;
      }
      graph.removeOutOfDomainVertices(cubicalImage, range);

      // we add edges to the inverse graph
      typename VertexSet::iterator cube = cubicalImage.begin();
      while(cube != cubicalImage.end()) {
        graph.nodes()[*cube].inEdges.insert(b->first);
        ++cube;
      }
      ++b;
    }
  }
*/



  template <typename ConstraintsT>
  void computeImageOfCubeWithConstraints(const VertexType & vertex, const ConstraintsT & constraints, VertexSet & cubicalImage) {
    VectorType cube = vertexToCube(vertex);
    std::list<VectorType> intervalImage;
    m_f.eval(cube, intervalImage);
    //std::cout << " compyte ";
    typename std::list<VectorType>::iterator it = intervalImage.begin();
    while(it != intervalImage.end()) {
      if(constraints.check(*it)) {
        createGrid(cubicalImage, getResolution(), *it);
      }
      ++it;
    }
    removeIncorrectVertices(cubicalImage, constraints);
  }

   /** ///////////////////////////////////////////////////////////////////////////////////////////////
   ///
   ///  Creates graph that is a cubical representation of the map f with given resolution
   ///  Vertices that do not satisfy constraints are not created.
   ///  It also creates inverted graph
   ///
   ///  we assume that:
   ///      - domain is already set
   ///      - all edges in a graph are removed
   ///
   //////////////////////////////////////////////////////////////////////////////////////////////// */
   template <typename ConstraintsT>
   static void constructCubicalMapWithConstraints(CubicalMap & graph, const ConstraintsT & constraints) {
     sbug << "\t-> constructCubicalMapWithConstraints(graph, constraints)" << std::endl;
     CubicalMap::iterator b = graph.begin(),
                          e = graph.end();
     while(b != e) {

       typename GraphType::VertexSet & cubicalImage = b->second.outEdges;
       graph.computeImageOfCubeWithConstraints(b->first, constraints, cubicalImage);
       // we add edges to the inverse graph
       typename VertexSet::iterator cube = cubicalImage.begin();
       while(cube != cubicalImage.end()) {
         graph[*cube].inEdges.insert(b->first);
         ++cube;
       }
       ++b;
     }
   }

   /// constructs cubical map with range restricted by constraints.
   template <typename ConstraintsT>
   void constructCubicalMapWithConstraints(const ConstraintsT & constraints) {
     sbug << "\t-> constructCubicalMapWithConstraints" << std::endl;
     constructCubicalMapWithConstraints(*this, constraints);
   }
   /// constructs cubical map with range restricted to given list of interval vectors
   void constructCubicalMapRestrictedTo(const std::list<VectorType> & range) {
     sbug << "\t-> constructCubicalMapRestrictedTo" << std::endl;
     constructCubicalMapWithConstraints(capd::invset::Scope<VectorType>(range));
   }
  void bisectGraph(int indexOfCoeff) {
    this->clearEdges();
    //typename GraphType::Nodes oldNodes(this->nodes().begin(), this->nodes().end());
    typename GraphType::Nodes oldNodes;
    std::swap(oldNodes, this->nodes()); // copies  nodes to oldNodes
    typename GraphType::Nodes & newNodes = this->nodes();
    newNodes.clear();
    typename GraphType::Nodes::iterator position = newNodes.begin(), b =
        oldNodes.begin();
    typename GraphType::Node emptyNode = GraphType::Node::getEmptyNode();
    while(b != oldNodes.end()) {
      VertexType p1 = b->first;
      p1[indexOfCoeff] = int(p1[indexOfCoeff]) * 2;
      position = newNodes.insert(position, std::make_pair(p1, emptyNode));
      p1[indexOfCoeff] = int(p1[indexOfCoeff]) + 1;
      position = newNodes.insert(position, std::make_pair(p1, emptyNode));
      ++b;
    }
    m_resolution[indexOfCoeff] = int(m_resolution[indexOfCoeff]) + 1;
  }

  /*void removeNodesOutOfDomain(const std::list<VectorType>& domain) {
    VectorType temp(m_resolution.dimension());
    while(true) {
      size_t numberOfNodes = this->nodes().size();
      iterator b = begin();
      while(b != end()) {
        iterator current = b;
        VectorType x = vertexToCube(current->first);
        ++b;

        if(!isInDomain(x, domain)) //if there is no arrow into current
        {
          typename VertexSet::iterator i = current->second.outEdges.begin();
          while(i != current->second.outEdges.end()) {
            this->nodes()[*i].inEdges.erase(current->first);
            ++i;
          }
          this->nodes().erase(current);
        }
      }

      if(this->nodes().size() == numberOfNodes)
        break;
      std::cout << this->nodes().size() << std::endl;
    }
  }
*/
  /// Removes vertices that do not belong to the domain
  /*void removeOutOfDomainVertices(VertexSet & vertices,
      const std::list<VectorType>& domain) const {
    typename VertexSet::iterator b = vertices.begin();
    while(b != vertices.end()) {
      typename VertexSet::iterator current = b;
      VectorType cube = vertexToCube(*current);
      ++b;
      if(!isInDomain(cube, domain)) {
        vertices.erase(current);
      }
    }
  }
  */
  /// Removes vertices that do not satisfy constraints
   template <typename ConstraintsT>
   void removeIncorrectVertices(VertexSet & vertices,
       const ConstraintsT & constraints) const {
      typename VertexSet::iterator b = vertices.begin();
      while(b != vertices.end()) {
        typename VertexSet::iterator current = b;
        VectorType cube = vertexToCube(*current);
        ++b;
        if(!constraints.check(cube)) {
          vertices.erase(current);
        }
      }
    }
   template <typename ConstraintsT>
   void removeIncorrectNodes(const ConstraintsT & constraints){
     iterator b = this->begin();
     while(b != this->end()) {
       iterator current = b;
       VectorType cube = vertexToCube(current->first);
       ++b;
       if(!constraints.check(cube)) {
         this->eraseNodeAndEdges(current);
       }
     }
   }
  /**
   * For given CubicalMap it computes exit set
   *
   * In exitSet we return all cubes that possibly escape map domain
   *
   * @param[out] exitSet it can be either VertexSet or Graph
   */
  template <typename VertexContainer>
  void computeExitSet(VertexContainer & exitSet){
    iterator b = begin(), e = end();

    while(b != e) {
      VectorType x = vertexToCube(b->first, m_resolution);
      //std::cout << "\n x = " << x;
      // we computed cubical image of x
      std::list<VectorType> enc;
      m_f.eval(x, enc);
      VertexSet cubicalImage;
      typename std::list<VectorType>::iterator it = enc.begin();
      while(it != enc.end()) {
        createGrid(cubicalImage, m_resolution, *it);
        ++it;
      }

      // we check if any cubes escapes from current domain
      bool escapes = false;
      typename VertexSet::iterator cube = cubicalImage.begin();

      while(cube != cubicalImage.end()) {
        //std::cout << " " << *cube;
        if(this->find(*cube) != this->end())
        ;
        else{
          escapes = true;
          break;
        }
        ++cube;
      }
      if(escapes){
        insertVertexIfNotExists(exitSet, b->first);
      }
      ++b;
    }
  }
  void save(const char* fileName) const {
    std::ofstream file;
    file.open(fileName);
    file << m_resolution;
    const_iterator b = this->begin(), e = this->end();
    while(b != e) {
      file << std::endl << b->first;
      typename VertexSet::const_iterator i = b->second.outEdges.begin();

      while(i != b->second.outEdges.end()) {
        file << " " << (*i);
        ++i;
      }
      ++b;
    }
    file.close();
  }

  void load(const char* fileName) {
    this->nodes().clear();
    std::ifstream file;
    file.open(fileName);
    VertexType temp, temp2;
    file >> m_resolution;
    do {
      file >> temp;
      this->nodes()[temp] = typename GraphType::Node();
      iterator i = this->nodes().find(temp);
      while(file.get() == ' ') {
        file >> temp2;
        i->second.outEdges.insert(temp2);
        if(file.eof())
          break;
      }
    } while(!file.eof());
    file.close();
    //    this->insertInEdges();
    //    this->eraseAcyclicVertices();
  }

private:
  MapType & m_f;
  ResolutionType m_resolution;
};



}
} // end of namespace capd::invset

#endif // _CAPD_INVSET_CUBICALMAP_H_
/// @}
