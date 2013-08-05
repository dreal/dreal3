//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file GraphNode.h
///
/// @author Tomasz Kapela   @date 2009-12-08
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INVSET_GRAPHNODE_H_
#define _CAPD_INVSET_GRAPHNODE_H_

namespace capd{
namespace invset{

template <typename EdgeSetT, typename NodeData>
struct GraphNode : public NodeData {
  typedef EdgeSetT EdgeSetType;
  typedef typename EdgeSetType::value_type EdgeType;
  static const GraphNode & getEmptyNode() {
    return S_emptyNode;
  }
  GraphNode operator=(const NodeData & nodeData){
    NodeData::operator=(nodeData);
    return *this;
  }
  void insertEdge(const EdgeType &edge){
    outEdges.insert(edge);
  }
  void clearInEdges(){
    inEdges.clear();
  }
  void clearOutEdges(){
      outEdges.clear();
  }
  void clearEdges(){
    inEdges.clear();
    outEdges.clear();
  }
  EdgeSetType inEdges;
  EdgeSetType outEdges;
private:
  static const GraphNode S_emptyNode ;

};

template <typename EdgeSetT, typename NodeData>
const GraphNode<EdgeSetT, NodeData> GraphNode<EdgeSetT, NodeData>::S_emptyNode = GraphNode<EdgeSetT, NodeData>();


}} // end of namespace capd::invset

#endif // _CAPD_INVSET_GRAPHNODE_H_
