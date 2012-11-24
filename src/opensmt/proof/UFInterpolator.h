/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifdef PRODUCE_PROOF

#ifndef UF_INTERPOLATOR_H
#define UF_INTERPOLATOR_H

#include "Enode.h"
#include "SMTConfig.h"

struct CEdge;

struct CNode
{
  CNode( const int id_
       , Enode *   e_ )
    : id    ( id_ )
    , e     ( e_ )
    , color ( CG_UNDEF )
    , next  ( NULL )
  {
    assert( id == e->getId( ) );
  }

  const int id;
  Enode *   e;
  cgcolor_t color;
  CEdge *   next;
};

typedef pair< CNode *, CNode * > path_t;

struct CEdge
{
  CEdge ( CNode * s
        , CNode * t
        , Enode * r )
    : source( s )
    , target( t )
    , reason( r )
    , color ( CG_UNDEF )
  {
    assert( source );
    assert( target );
  }

  CNode * source;
  CNode * target;
  Enode * reason;
  cgcolor_t color;

  inline friend ostream & operator<<( ostream & os, CEdge * ce )
  {
    return os << ce->source->e << " ---> " << ce->target->e;
  }
};

class Egraph;

class CGraph
{
public:

  CGraph( Egraph & egraph_
        , SMTConfig & config_ )
    : egraph  ( egraph_ )
    , config  ( config_ )
    , colored ( false )
    , conf1   ( NULL )
    , conf2   ( NULL )
    , conf    ( NULL )
  { }

  ~CGraph( ) { clear( ); }

  void     addCNode      ( Enode * );
  void     addCEdge      ( Enode *, Enode *, Enode * );
  void     revertEdges   ( CNode * );
  Enode *  getInterpolant( uint64_t );
  void     printAsDotty  ( ostream & );

  inline void setConf( Enode * c1, Enode * c2, Enode * r )
  {
    assert( conf1 == NULL );
    assert( conf2 == NULL );
    assert( c1 );
    assert( c2 );
    conf1 = c1;
    conf2 = c2;
    conf  = r;
  }

  inline void clear     ( )
  {
    while( !cnodes.empty( ) )
    {
      assert( cnodes.back( ) );
      delete cnodes.back( );
      cnodes.pop_back( );
    }
    while ( !cedges.empty( ) )
    {
      assert( cedges.back( ) );
      delete cedges.back( );
      cedges.pop_back( );
    }
    colored = false;
    conf1 = NULL;
    conf2 = NULL;
    cnodes_store.clear( );
  }

private:

  void       color          ( const uint64_t );
  void       colorNodes     ( const uint64_t );
  cgcolor_t  colorNodesRec  ( CNode *, const uint64_t );
  void       colorEdges     ( CNode *, CNode *, const uint64_t );
  void       colorEdgesRec  ( CNode *, CNode *, const uint64_t );
  void       colorEdgesFrom ( CNode *, const uint64_t );
  void       colorReset     ( );

  bool          getSubpaths          ( const path_t &, path_t &, path_t &, path_t & );
  size_t        getSortedEdges       ( CNode *, CNode *, vector< CEdge * > & );
  Enode *       I                    ( const path_t & );
  Enode *       Irec                 ( const path_t &, map< path_t, Enode * > & );
  Enode *       J                    ( const path_t &, vector< path_t > & );
  void          B                    ( const path_t &, vector< path_t > & );
  void          Brec                 ( const path_t &, vector< path_t > &, set< path_t > & );
  bool          getFactorsAndParents ( const path_t &, vector< path_t > &, vector< path_t > & );
  inline path_t path                 ( CNode * c1, CNode * c2 ) { return make_pair( c1, c2 ); }

  Egraph &                        egraph;
  SMTConfig &                     config;
  vector< CNode * >               cnodes;
  map< enodeid_t, CNode * >       cnodes_store;
  set< CNode * >                  colored_nodes;
  set< pair< CNode *, CNode * > > colored_edges;
  vector< CEdge * >               cedges;
  bool                            colored;
  Enode *                         conf1;
  Enode *                         conf2;
  Enode *                         conf;
};

#endif

#endif
