//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file invariantSets.h
///
/// @author Tomasz Kapela   @date 2009-12-15
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INVSET_INVARIANTSETS_H_
#define _CAPD_INVSET_INVARIANTSETS_H_
#include "capd/invset/Scope.h"
namespace capd{
namespace invset{
template<typename GraphT>
inline void noVisualization( const GraphT & g){
}
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// computes enclosure of the positive invariant set
///
/// @param[in,out] graph    graph should contain map, resolution and optionally initial set of vertices (if not the parameter domain will be used)
/// @param[in]     domain   list of boxes that covers domain (even if domain is already set in graph, this information is needed to restrict range of a cubical map)
/// @param[in]     subdiv   number of the graph subdivision (in one iteration we subdivide only in one dimension)
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
template <class GraphT>
void computePositiveInvariantSet(GraphT& graph, std::list<typename GraphT::VectorType> & domain, int subdiv, void (* showGraph)(const GraphT & g) = noVisualization<GraphT>) {

  capd::scon << "computing positive invariant set \n";
  capd::slog2 << "  initial no. of nodes :" << graph.size() << "\n";
  if(graph.empty())
     graph.setDomain(domain);

  Scope<typename GraphT::VectorType> range(domain);
  int dimension = domain.begin()->dimension();
  for(int i = 0; i < subdiv; ++i) {
    capd::slog2 << "\n iteration : " << i << std::endl;

    graph.bisectGraph(i % dimension);
    capd::slog2 << " * graph bisected \n";
    graph.constructCubicalMapWithConstraints(range);
    capd::slog2 << " * cubical map created \n";

    graph.eraseNoInVertices();
    capd::slog2 << " * vertices with no inward edges removed\n";
    capd::slog << " resolution: " << graph.getResolution() << "   no. of nodes: " << graph.size() << "\n";

    showGraph(graph);
    // waitBt();
  }
  capd::slog2 << "  final no. of nodes :" << graph.size() << "\n";
}
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///
/// computes enclosure of the positive invariant set
/// @param[in,out] graph    graph should contain map, resolution and optionally initial set of vertices (if not the parameter domain will be used)
/// @param[in]     domain   list of boxes that covers domain (even if domain is already set in graph, this information is needed to restrict range of a cubical map)
/// @param[in]     subdiv   number of the graph subdivision (in one iteration we subdivide only in one dimension)
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
template <class GraphT>
void computeInvariantSet(GraphT& graph, std::list<typename GraphT::VectorType> & domain, int subdiv,
                         void (* showGraph)(const GraphT & g) = noVisualization<GraphT>) {

  capd::scon<< "computing invariant set \n";
  if(graph.empty())
    graph.setDomain(domain);

  int dimension = domain.begin()->dimension();
  for(int i = 0; i < subdiv; ++i) {
    capd::slog2 << "\n iteration : " << i << std::endl;

    graph.bisectGraph(i % dimension);
    capd::slog2 << " * graph bisected \n";
    graph.constructCubicalMapRestrictedTo(domain);
    capd::slog2 << " * cubical map created \n";

    graph.eraseAcyclicVertices();
    capd::slog2 << " * acyclic vertices removed\n";
    capd::slog << " resolution: " << graph.getResolution() << "   no. of nodes: " << graph.size() << "\n";

    showGraph(graph);
    // waitBt();
  }
}



struct GetKey {
  template <typename MapType>
  typename MapType::key_type operator()(typename MapType::value_type const & v){
    return v.first;
  }
};

/// inserts all map keys into set
template <typename MapType, typename SetType>
void insertMapKeysIntoSet(const MapType & map, SetType & set){
  typename MapType::const_iterator map_it = map.begin(), map_end = map.end();
  typename SetType::iterator position = set.end();
  while(map_it != map_end){
    set.insert(position, map_it->first);
    map_it++;
  }
}


/// it iteratively compute image of all cubes in the graph
/// and adds them if they satisfy constraints
/// until no more new cubes can be added
template <typename GraphT, typename ConstraintsT>
void propagateGraph(GraphT & graph, ConstraintsT & constraints,
    void (* showGraph)(const GraphT & g) = noVisualization<GraphT>){
  typedef GraphT GraphType;
  typedef typename GraphType::VectorType VectorType;
  typedef typename GraphType::VertexSet VertexSet;
  typedef typename GraphType::VertexType VertexType;

  capd::scon << "graph propagation\n";
  capd::slog << "  initial no. of nodes = " << graph.size() <<"\n";
  VertexSet unchecked;
  insertMapKeysIntoSet(graph, unchecked);
  capd::sbug << "unchecked size " << unchecked.size();
  do {

    int numberOfUnchecked = unchecked.size();
    VertexSet cubes;
    swap(unchecked, cubes);
    //std::vector<VertexType> vec(unchecked.begin(),unchecked.end());
    typename VertexSet::iterator cube_it = cubes.begin();
#pragma omp parallel shared(unchecked, numberOfUnchecked, cubes)
    {
#pragma omp for  schedule(dynamic)
      for(int counter = 0; counter < numberOfUnchecked; ++counter) {
        typename GraphType::iterator current;
#pragma omp critical
        {
          current = graph.find(*cube_it);
          cube_it++;
          capd::sbug << "it: " << counter << "   vertex :" << current->first;
        }

        VertexSet & cubicalImage = current->second.outEdges;
        try{
          graph.computeImageOfCubeWithConstraints(current->first, constraints, cubicalImage);
          capd::sbug << "vertex : " << current->first <<  "\n  cubical image size: " << cubicalImage.size() <<"\n";
        } catch(std::exception& e) {
          capd::serr << "zlapalem wyjatek \n" << e.what() << "\n vertex = " << current->first << std::endl;
          exit(0);
        }

        typename VertexSet::iterator imageIt = cubicalImage.begin();
        while(imageIt != cubicalImage.end()) {
#pragma omp critical
          {
            if(graph.find(*imageIt) == graph.end()){
              graph.insertNode(*imageIt);
              unchecked.insert(*imageIt);
            }
          } // omp critical
          ++imageIt;
        } // while
      } // for
    } // parallel

    capd::slog << "  * no. of nodes added in this iteration : " << unchecked.size() << std::endl;
    showGraph(graph);
  } while(unchecked.size() != 0);
  graph.insertInEdges();
  //graph.eraseNoInVertices();
  slog << "  final no. of nodes : " << graph.size() <<"\n";

}

/// it iteratively compute image of all cubes in the graph
/// and adds them if they satisfy constraints
/// until no more new cubes can be added
template <typename GraphT, typename ConstraintsT>
void propagateVertexSet(GraphT & graph, ConstraintsT & constraints,
    typename GraphT::VertexSet & result
   // , OutputT & output =  noVisualization<typename GraphT::VertexType>
){
  typedef GraphT GraphType;
  typedef typename GraphType::VectorType VectorType;
  typedef typename GraphType::VertexSet VertexSet;
  typedef typename GraphType::VertexType VertexType;

  capd::scon << "graph propagation\n";
  capd::slog << "  initial no. of nodes = " << graph.size() <<"\n";
  VertexSet unchecked;
  insertMapKeysIntoSet(graph, unchecked);
  result = unchecked;
  capd::sbug << "unchecked size " << unchecked.size();
  do {

    int numberOfUnchecked = unchecked.size();
    VertexSet cubes;
    swap(unchecked, cubes);
    //std::vector<VertexType> vec(unchecked.begin(),unchecked.end());
    typename VertexSet::iterator cube_it = cubes.begin();
#pragma omp parallel shared(unchecked, numberOfUnchecked, cubes)
    {
#pragma omp for  schedule(dynamic)
      for(int counter = 0; counter < numberOfUnchecked; ++counter) {
        typename VertexSet::iterator current;
#pragma omp critical
        {
          //current = result.find(*cube_it);
          current = cube_it;
          cube_it++;
          capd::sbug << "it: " << counter << "   vertex :" << *current;
        }

        VertexSet cubicalImage;
        try{
          graph.computeImageOfCubeWithConstraints(*current, constraints, cubicalImage);
          capd::sbug << "vertex : " << *current <<  "\n  cubical image size: " << cubicalImage.size() <<"\n";
        } catch(std::exception& e) {
          capd::serr << "zlapalem wyjatek \n" << e.what() << "\n vertex = " << *current << std::endl;
          exit(0);
        }

        typename VertexSet::iterator imageIt = cubicalImage.begin();
        while(imageIt != cubicalImage.end()) {
#pragma omp critical
          {
            if(result.find(*imageIt) == result.end()){
              result.insert(*imageIt);
              unchecked.insert(*imageIt);
            }
          } // omp critical
          ++imageIt;
        } // while
      } // for
    } // parallel

    capd::slog << "  * no. of nodes added in this iteration : " << unchecked.size() << std::endl;
    //output(result);
  } while(unchecked.size() != 0);
  //graph.insertInEdges();
  //graph.eraseNoInVertices();
  slog << "  final no. of nodes : " << result.size() <<"\n";

}
}} // end of namespace capd::invset

#endif // _CAPD_INVSET_INVARIANTSETS_H_

