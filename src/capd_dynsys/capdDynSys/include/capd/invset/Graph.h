//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file Graph.h
///
/// @author Tomasz Kapela   @date 2009-12-08
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INVSET_GRAPH_H_
#define _CAPD_INVSET_GRAPH_H_

#include <map>
#include <set>
#include <climits>
#include "capd/invset/GraphNode.h"

namespace capd{
namespace invset{


////////////////////////////////////////////////////////////////////////////////////
//   template class Graph
///
///  It defines a graph that in each node can store additional data
///
///  Graph is stored as association lists using standard map and set data types
///  VertexT  defines how to encode vertices
///  lessT    is a strict ordering of vertices needed by map and set containers
///  NodeData type of data stored in each node
///
////////////////////////////////////////////////////////////////////////////////////
template <typename VertexT, typename lessT, typename NodeDataT>
class Graph : public std::map<VertexT,  GraphNode<std::set<VertexT, lessT>, NodeDataT>, lessT > {

public:

  typedef VertexT VertexType;
  typedef std::set<VertexT, lessT> VertexSet;
  typedef NodeDataT NodeData;
  typedef lessT OrderType;
  typedef GraphNode<VertexSet, NodeDataT> Node;
  typedef std::map<VertexType, Node, lessT> Nodes;
  typedef typename Nodes::iterator iterator;
  typedef typename Nodes::const_iterator const_iterator;

  Nodes& nodes() {
    return *this;
  }
  const Node & getNode(const VertexType & vertex) const {
    return (*this)[vertex];
  }

  void setNode(const VertexType & vertex, const Node & node) {
    (*this)[vertex] = node;
  }
  void insertNode(const VertexType & vertex) {
    (*this)[vertex];
  }

  const NodeData & getNodeData(const VertexType & vertex) const{
    return (*this)[vertex];
  }

  NodeData & nodeData(const VertexType & vertex){
    return (*this)[vertex];
  }

  void setNodeData(const VertexType & vertex, const NodeData & nodeData) {
      (*this)[vertex] = nodeData;
  }

  /// removes all edges for the graph
  void clearEdges() {
    iterator node = begin();
    while(node != end()) {
      node->second.clearEdges();
      ++node;
    }
  }

  /// removes all in-edges from the graph
  void clearInEdges() {
    iterator node = begin();
    while(node != end()) {
      node->second.clearInEdges();
      ++node;
    }
  }

  /// creates inverted graph
  void insertInEdges() {
    iterator node = begin();
    while(node != end()) {
      typename VertexSet::iterator i = node->second.outEdges.begin();
      while(i != node->second.outEdges.end()) {
        (*this)[*i].inEdges.insert(node->first);
        ++i;
      }
      ++node;
    }
  }

  /// it removes node given by iterator and all edges pointing to it
  void eraseNodeAndEdges(iterator & node){
    typename VertexSet::iterator i = node->second.outEdges.begin();
    while(i != node->second.outEdges.end()) {
      (*this)[*i].inEdges.erase(node->first);
      ++i;
    }
    i = node->second.inEdges.begin();
    while(i != node->second.inEdges.end()) {
      (*this)[*i].outEdges.erase(node->first);
      ++i;
    }
    Nodes::erase(node);
  }

  /// removes node given by iterator and all edges pointing to it
  void erase(iterator & node){
    eraseNodeAndEdges(node);
  }

  /// It iteratively erases acyclic vertices
  /// We assume that inverse graph is already created (e.g. by calling insertInEdges())
  void eraseAcyclicVertices() {
    size_t numberOfNodes;
    do {
      numberOfNodes = size();
      iterator b = begin();
      while(b != end()) {
        iterator current = b;
        ++b;
        if((current->second.inEdges.empty()) || (current->second.outEdges.empty())){  // if there is no arrow into current or from current
          eraseNodeAndEdges(current);                                                 // then current vertex do not belong to any cycle
        }
      }
    } while (size() != numberOfNodes);
  }

  /// It iteratively erase vertices that do not have any inward edges
  void eraseNoInVertices() {
    size_t numberOfNodes;
    do {
      numberOfNodes = size();
      iterator b = begin();
      while(b != end()) {
        iterator current = b;
        ++b;
        if(current->second.inEdges.empty()){ //if there is no arrow into current
          eraseNodeAndEdges(current);
        }
      }
    } while (size() != numberOfNodes);
  }

  /// It iteratively erase vertices that do not have any outward edges
    void eraseNoOutVertices() {
      size_t numberOfNodes;
      do {
        numberOfNodes = size();
        iterator b = begin();
        while(b != end()) {
          iterator current = b;
          ++b;
          if(current->second.outEdges.empty()){ //if there is no edge from current
            eraseNodeAndEdges(current);
          }
        }
      } while (size() != numberOfNodes);
    }

  /// returns set of vertices that have self-loop (edge that connects vertex to itself)
  VertexSet findFixedPoints() const {
    VertexSet result;
    const_iterator b = begin();
    while(b != end()) {
      if(b->second.outEdges.find(b->first) != b->second.outEdges.end())
        result.insert(b->first);
      ++b;
    }
    return result;
  }

  /// finds cyclic vertices to a given maximal cycle length
  ///
  /// in result[n] it returns vertices that belongs to some cycle of length n + 1
  /// if vertex belongs to more than one cycle than the shortest cycle is concerned
  template <typename VertexContainer>
  void findCycles(VertexContainer result[], int maxlength) const{
    int i = static_cast<int>( size());
    const_iterator b = begin();
#pragma omp parallel shared(b)
    {
#pragma omp for schedule(dynamic)
      for(int k = 0; k < i; ++k) {
        const_iterator it;
#pragma omp critical
        {
          it = b;
          ++b;
        }
        int cycleLength = findCycleLength(it, maxlength);
        if( cycleLength < 0){
#pragma omp critical
          {
            result[cycleLength].push_back(it->first);
          }
        }
      }
    }
  }

  /// for given vertex returns the shortest cycle length starting at this vertex
  ///
  /// (for self-loop length = 0,  for a-b-a length=1 etc.)
  /// returns -1 if it does not find cycle with length less or equal to maxlength.
  int findCycleLength(const_iterator vertex,  int maxlength) const {
    VertexSet temp = vertex->second.m_edgesOut;
    VertexSet image;
    for(int i = 0; i < maxlength; ++i) {
      if(i) {
        typename VertexSet::iterator b = image.begin(), e = image.end();

        while(b != e) {
          const VertexSet & outEdges = getNode(*b).m_edgesOut;
          temp.insert(outEdges.begin(), outEdges.end());
          ++b;
        }
      }
      image.clear();
      image.swap(temp);
      if(image.find(vertex->first) != image.end()) {
        return i;
      }
    }
    return -1;
  }

  using Nodes::begin;
  using Nodes::end;
  using Nodes::size;
};

}} // end of namespace capd::invset

#endif // _CAPD_INVSET_GRAPH_H_

