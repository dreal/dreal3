/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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

#include "UFInterpolator.h"
#include "Egraph.h"

void CGraph::addCNode( Enode * e )
{
  assert( e );
  map< enodeid_t, CNode * >::iterator it = cnodes_store.find( e->getId( ) );
  if ( it != cnodes_store.end( ) ) return;
  CNode * n = new CNode( e->getId( ), e );
  cnodes_store[ e->getId( ) ] = n;
  cnodes.push_back( n );
}

void CGraph::colorNodes( const uint64_t mask )
{
  for ( size_t i = 0 ; i < cnodes.size( ) ; i ++ )
    colorNodesRec( cnodes[ i ], mask );
}

cgcolor_t CGraph::colorNodesRec( CNode * c, const uint64_t mask )
{
  // Already done
  if ( colored_nodes.find( c ) != colored_nodes.end( ) )
    return c->color;
  // Base case, color variables
  if ( c->e->getArity( ) == 0 )
  {
    cgcolor_t color = CG_UNDEF;
    // Belongs to B
    if ( (egraph.getIPartitions( c->e ) &  mask) != 0 )
      color |= CG_B;
    // Belongs to A
    if ( (egraph.getIPartitions( c->e ) & ~mask) != 0 )
      color |= CG_A;
    c->color = color;
  }
  else
  {
    // Function symbol: color depending on the arguments
    // Decide color of term as intersection
    cgcolor_t color = CG_AB;
    Enode * args = c->e->getCdr( );
    for ( args = c->e->getCdr( ) 
	; !args->isEnil( )
	; args = args->getCdr( ) )
    {
      Enode * arg = args->getCar( );
      // Not necessairly an argument is needed in the graph
      if ( cnodes_store.find( arg->getId( ) ) != cnodes_store.end( ) )
	color &= colorNodesRec( cnodes_store[ arg->getId( ) ], mask );
    }
    c->color = color;
  }
  assert( colored_nodes.find( c ) == colored_nodes.end( ) );
  colored_nodes.insert( c );
  return c->color;
}

void CGraph::addCEdge( Enode * s, Enode * t, Enode * r )
{
  assert( s );
  assert( t );
  // Retrieve corresponding nodes
  CNode * cs = cnodes_store[ s->getId( ) ];
  CNode * ct = cnodes_store[ t->getId( ) ];
  // Create edge
  CEdge * edge = new CEdge( cs, ct, r );
  // Storing edge in cs and ct
  assert( cs->next == NULL ); 
  cs->next = edge;
  cedges.push_back( edge ); 
}

void CGraph::color( const uint64_t mask )
{
  assert( conf1 );
  assert( conf2 );
  // Starting from
  CNode * c1 = cnodes_store[ conf1->getId( ) ]; 
  CNode * c2 = cnodes_store[ conf2->getId( ) ]; 
  assert( !colored );
  assert( colored_nodes.empty( ) );
  // Color nodes
  colorNodes( mask );
  // Edges can be colored as consequence of nodes
  colorEdges( c1, c2, mask );
  // Graph is now colored
  colored = true;
}

void CGraph::colorReset( )
{
  assert( colored );
  colored_nodes.clear( );
  colored_edges.clear( );
  colored = false;
}

void CGraph::colorEdges( CNode * c1, CNode * c2, const uint64_t mask )
{
  colorEdgesRec( c1, c2, mask );
}

void CGraph::colorEdgesRec( CNode * c1
                          , CNode * c2
			  , const uint64_t mask )
{
  const pair< CNode *, CNode * > p = path( c1, c2 );
  // Already processed, no need to color again
  if ( !colored_edges.insert( p ).second )
    return;
  CNode * x = c1;
  CNode * y = c2;
  colorEdgesFrom( x, mask );
  colorEdgesFrom( y, mask );
}

void CGraph::colorEdgesFrom( CNode * x, const uint64_t mask )
{
  // Color from x
  CNode * n = NULL;
  while( x->next != NULL 
      && x->next->color == CG_UNDEF )
  {
    n = x->next->target;
    // Congruence edge, recurse on arguments
    if ( x->next->reason == NULL )
    {
      assert( x->e->getArity( ) == n->e->getArity( ) );
      // Color children of the congruence relation, and
      // introduce intermediate nodes if necessary
      Enode * arg_list_x, * arg_list_n;
      for ( arg_list_x = x->e->getCdr( )
	  , arg_list_n = n->e->getCdr( )
	  ; !arg_list_x->isEnil( ) 
	  ; arg_list_x = arg_list_x->getCdr( )
	  , arg_list_n = arg_list_n->getCdr( ) )
      {
	Enode * arg_x = arg_list_x->getCar( );
	Enode * arg_n = arg_list_n->getCar( );
	if ( arg_x == arg_n ) continue;
	// Call recursively on arguments
	colorEdgesRec( cnodes_store[ arg_x->getId( ) ]
	             , cnodes_store[ arg_n->getId( ) ] 
		     , mask );	
      }
      // Incompatible colors: this is possible
      // for effect of congruence nodes: adjust
      if ( (x->color == CG_A && n->color == CG_B)
	|| (x->color == CG_B && n->color == CG_A) )
      {
	// Need to introduce auxiliary nodes and edges
	// For each argument, find node that is equivalent
	// and of shared color
	list< Enode * > new_args;
	Enode * arg_list_x, * arg_list_n;
	for ( arg_list_x = x->e->getCdr( )
	    , arg_list_n = n->e->getCdr( )
	    ; !arg_list_x->isEnil( ) 
	    ; arg_list_x = arg_list_x->getCdr( )
	    , arg_list_n = arg_list_n->getCdr( ) )
	{
	  Enode * arg_x = arg_list_x->getCar( );
	  Enode * arg_n = arg_list_n->getCar( );
	  CNode * cn_arg_x = cnodes_store[ arg_x->getId( ) ];
	  CNode * cn_arg_n = cnodes_store[ arg_n->getId( ) ];
	  // If same node, keep
	  if ( arg_x == arg_n )
	  {
	    new_args.push_front( arg_x );
	  } 
	  // If argument 
	  else if ( (cn_arg_x->color & n->color) == 0 )
	  {
	    // Scan first argument that is equivalent to x and shared
	    CNode * xnext;
	    for ( xnext = cn_arg_x->next->target
		; xnext != NULL 
		; xnext = xnext->next->target )
	    {
	      if ( xnext->color == CG_AB )
		break;
	    }
	    assert( xnext != NULL );
	    assert( xnext->color == CG_AB );
	    new_args.push_front( xnext->e );
	  }
	  else if ( (cn_arg_n->color & x->color) == 0 )
	  {
	    // Scan first argument that is equivalent to x and shared
	    CNode * nnext;
	    for ( nnext = cn_arg_n->next->target
		; nnext != NULL 
		; nnext = nnext->next->target )
	    {
	      if ( nnext->color == CG_AB )
		break;
	    }
	    assert( nnext != NULL );
	    assert( nnext->color == CG_AB );
	    new_args.push_front( nnext->e );
	  }
	  else
	  {
	    opensmt_error( "something went wrong" );
	  }
	  // New arguments must be shared
	  assert( cnodes_store[ new_args.front( )->getId( ) ]->color == CG_AB );
	}
	Enode * na = egraph.cons( new_args );
	Enode * s = x->e->getCar( );
	// nn is the node that can be connected to x and n
	Enode * nn = egraph.cons( s, na );
	// There are two cases now. It is possible
	// that nn is equal to either x or n
	assert( nn != x->e );
	assert( nn != n->e );
	// Adds corresponding node
	addCNode( nn );
	// Remember this
	assert( x->next->target == n );
	CNode * cnn = cnodes.back( );
	cnn->color = CG_AB;
	/*
	// Situation ... --> x | then make ... --> x --> nn
	if ( x->next == NULL )
	  addCEdge( x->e, nn, NULL );
	// Situation ... <-- x | then make ... <-- x <-- nn
	else
	{
	  addCEdge( nn, x->e, NULL );	
	}
	*/
	// Situation x --> n | then make x --> nn
	x->next = NULL;
	addCEdge( x->e, nn, NULL );
	assert( x->next->target == cnn );
	// Choose a color
	cedges.back( )->color = x->color;
	/*
	// Situation x --> nn   n | then make x --> nn --> n
	if ( cnn->next == NULL )
	  addCEdge( nn, x->e, NULL );	
	// Situation x <-- nn   n <-- | then make x <-- nn <-- n <--
	else if ( n->next == NULL )
	  addCEdge( nn, n->e, NULL );	
	// Situation x <-- nn   n --> | then make x <-- nn <-- n <--
	else 
	{
	  revertEdges( n );
	  addCEdge( n->e, nn, NULL );	
	}
	*/
	addCEdge( nn, n->e, NULL );	
	cedges.back( )->color = n->color;
	x = cnn;
      }
      // Now all the children are colored, we can decide how to color this
      if ( x->color == n->color )
      {
	assert( x->color );
	// Choose one color: default A
	if ( x->color == CG_AB )
	  x->next->color = CG_A;
	// Color with proper color
	else
	  x->next->color = x->color;
      }
      // Different colors: choose intersection
      else
      {
	// It is not possible that are incompatible
	assert( x->color != CG_A || n->color != CG_B );
	assert( x->color != CG_B || n->color != CG_A );
	x->next->color = x->color & n->color;
	assert( x->next->color != CG_UNDEF );
      }
    }
    // Color basic edge with proper color
    else 
    {
      // If it's AB, color B
      x->next->color = ((egraph.getIPartitions( x->next->reason ) & mask) != 0) 
	          ? CG_B
		  : CG_A;
    }
    // Color must be a power of 2
    assert( x->next->color == CG_A || x->next->color == CG_B );
    assert( x->next->color != CG_A || x->next->color != CG_B );
    // Pass to next node
    x = n;
  }
}

//
// Revert path starting from x, if 
// any outgoing edge is present
//
void CGraph::revertEdges( CNode * x )
{
  if ( x->next == NULL )
    return;
  // It has outgoing edge: rewrite 
  CNode * p = x;
  CEdge * prev = p->next;
  while ( prev != NULL )
  {
    // Next is the connecting edge to reverse
    CEdge * next = prev;
    assert( next->source == p );
    // from | p -- next --> t | to | p <-- next -- t
    CNode * t = next->target;
    // Adapt data structures
    next->source = t;
    next->target = p; 
    prev = t->next;
    t->next = next;
    // Next step
    p = t; 
  }
  x->next = NULL;
}

//
// Here mask is a bit-mask of the form 0..01..1
// which indicates the current splitting for the
// formula into A and B.
//
Enode * CGraph::getInterpolant( const uint64_t mask )
{
  assert( !colored );
  color( mask );
  assert( colored );

  // Traverse the graph, look for edges of "color" to summarize  
  CNode * c1 = cnodes_store[ conf1->getId( ) ]; 
  CNode * c2 = cnodes_store[ conf2->getId( ) ]; 

  assert( c1 );
  assert( c2 );
  uint64_t conf_color;

  // Conflict is due to a negated equality
  if ( conf != NULL )
  {
    // Color of A if AB
    conf_color = ((egraph.getIPartitions( conf ) & mask) == 0 
	       ? CG_A 
	       : CG_B); 
  }
  // Conflict is due to different constants
  else
  {
    // We arbitrairly set to B
    conf_color = CG_B;
  }

  Enode * result = NULL;
  path_t pi = path( c1, c2 );
  //
  // Compute interpolant as described in Fuchs et al. paper
  // Ground Interpolation for the Theory of Equality
  //
  // Conflict belongs to A part
  if ( conf_color == CG_A )
  {
    list< Enode * > conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
#if 0
    if ( !getSubpaths( pi, pi_1, theta, pi_2 ) )
    {
      result = egraph.mkFalse( );
    }
    else
    {
#else
    if ( !getSubpaths( pi, pi_1, theta, pi_2 ) )
    {
      // Compute B( pi_1 ) U B( pi_2 )
      vector< path_t > b_paths;
      B( pi_1, b_paths );
      B( pi_2, b_paths );

      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj.push_back( I( b_paths[ i ] ) );
      // Finally compute implication
      list< Enode * > conj_impl;
      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj_impl.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
		           , egraph.cons( b_paths[ i ].second->e ) ) ) );
      Enode * implicant = egraph.mkAnd( egraph.cons( conj_impl ) );
      Enode * implicated = egraph.mkFalse( );
      conj.push_back( egraph.mkImplies( egraph.cons( implicant
	            , egraph.cons( implicated ) ) ) );
      result = egraph.mkAnd( egraph.cons( conj ) );
    }
    else
    {
#endif
      // Compute I( theta )
      conj.push_back( I( theta ) );
      // Compute B( pi_1 ) U B( pi_2 )
      vector< path_t > b_paths;
      B( pi_1, b_paths );
      B( pi_2, b_paths );

      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj.push_back( I( b_paths[ i ] ) );
      // Finally compute implication
      list< Enode * > conj_impl;
      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj_impl.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
		           , egraph.cons( b_paths[ i ].second->e ) ) ) );
      Enode * implicant = egraph.mkAnd( egraph.cons( conj_impl ) );
      Enode * implicated = egraph.mkNot( egraph.cons( egraph.mkEq( egraph.cons( theta.first->e
		                       , egraph.cons( theta.second->e ) ) ) ) );
      conj.push_back( egraph.mkImplies( egraph.cons( implicant
	            , egraph.cons( implicated ) ) ) );
      result = egraph.mkAnd( egraph.cons( conj ) );
    }
  }
  // Much simpler case when conflict belongs to B
  else if ( conf_color == CG_B )
  {
    result = I( pi );
  }
  else
  {
    opensmt_error( "something went wrong" );
  }

  assert( result );
  colorReset( );
  assert( !colored );
  return result;
}

//
// Retrieve subpaths. Returns false if the
// entire path belongs to A, which means
// that the interpolant is "false"
//
bool CGraph::getSubpaths( const path_t & pi
                        , path_t &       pi_1
			, path_t &       theta
			, path_t &       pi_2 )
{
  CNode * x = pi.first;
  CNode * y = pi.second;
  assert( x );
  assert( y );

  // Sorted list of edges from x
  vector< CEdge * > sorted_edges;
  const size_t x_path_length = getSortedEdges( x, y, sorted_edges );
  // Decide maximal B path
  unsigned largest_path_length = 0;

  for ( size_t i = 0 ; i < sorted_edges.size( ) ; ) 
  {
    // Skip A-path
    while ( i < sorted_edges.size( ) 
	 && sorted_edges[ i ]->color == CG_A ) i ++;
    if ( i == sorted_edges.size( ) ) continue;
    unsigned path_length = 0;
    // Save source
    CNode * s = i < x_path_length 
	      ? sorted_edges[ i ]->source
	      : sorted_edges[ i ]->target;
    CNode * t = s;
    // Now scan B-path
    while ( i < sorted_edges.size( )
	 && sorted_edges[ i ]->color == CG_B )
    { 
      t = i < x_path_length 
	? sorted_edges[ i ]->target 
	: sorted_edges[ i ]->source ;
      i ++;
      path_length ++;
    }
    if ( path_length > largest_path_length )
    {
      assert( s != t );
      largest_path_length = path_length;
      theta.first = s;
      theta.second = t;
    }
    assert( path_length != 0 || s == t );
  }
  // No path found: arbitrary split
  if ( largest_path_length == 0 )
  {
    pi_1.first = pi.first;
    pi_1.second = pi.first;
    pi_2.first = pi.first;
    pi_2.second = pi.second;
    return false;
  }

  // Set pi_1 theta pi_2
  pi_1.first = pi.first;
  pi_1.second = theta.first;
  pi_2.first = theta.second;
  pi_2.second = pi.second; 

  return true;
}

Enode * CGraph::J( const path_t &     p
                 , vector< path_t > & b_paths )
{
  // True on empty path
  if ( p.first == p.second ) return egraph.mkTrue( );

  list< Enode * > conj;
  for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
    conj.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
	                       , egraph.cons( b_paths[ i ].second->e ) ) ) );
  Enode * implicant = egraph.mkAnd( egraph.cons( conj ) );
  Enode * implicated = egraph.mkEq( egraph.cons( p.first->e, egraph.cons( p.second->e ) ) );
  Enode * res = egraph.mkImplies( egraph.cons( implicant, egraph.cons( implicated ) ) );
  return res;
}

Enode * CGraph::I( const path_t & p )
{
  map< path_t, Enode * > cache;
  return Irec( p, cache );
}

Enode * CGraph::Irec( const path_t & p, map< path_t, Enode * > & cache )
{
  // True on empty path
  if ( p.first == p.second ) return egraph.mkTrue( );

  map< path_t, Enode * >::iterator it = cache.find( p );
  // Return previously computed value
  if ( it != cache.end( ) )
    return it->second;

  list< Enode * > conj;
  // Will store factors
  vector< path_t > factors;
  factors.push_back( p );
  // Will store parents of B-path
  vector< path_t > parents;

  const bool a_factor = getFactorsAndParents( p, factors, parents );

  if ( factors.size( ) == 1 )
  {
    // It's an A-path
    if ( a_factor )
    {
      // Compute J
      vector< path_t > b_premise_set;
      B( p, b_premise_set );
      conj.push_back( J( p, b_premise_set ) );
      for ( unsigned i = 0 ; i < b_premise_set.size( ) ; i ++ )
	conj.push_back( Irec( b_premise_set[ i ], cache ) );
    }
    // It's a B-path
    else
    {
      // Recurse on parents
      for ( unsigned i = 0 ; i < parents.size( ) ; i ++ )
	conj.push_back( Irec( parents[ i ], cache ) );
    }
  }
  else
  {
    // Recurse on factors
    for ( unsigned i = 0 ; i < factors.size( ) ; i ++ )
      conj.push_back( Irec( factors[ i ], cache ) );
  }

  Enode * res = egraph.mkAnd( egraph.cons( conj ) );

  assert( res );

  cache[ p ] = res;

  return res;
}

void CGraph::B( const path_t & p
	      , vector< path_t > & b_premise_set )
{
  set< path_t > cache;
  Brec( p, b_premise_set, cache );
}

void CGraph::Brec( const path_t     & p
                 , vector< path_t > & b_premise_set
                 , set< path_t >    & cache )
{
  // Skip trivial call
  if ( p.first == p.second ) return;
  // Skip seen calls
  if ( !cache.insert( p ).second ) return;

  // Will store factors
  vector< path_t > factors;
  factors.push_back( p );
  // Will store parents of B-path
  vector< path_t > parents;

  const bool a_factor = getFactorsAndParents( p, factors, parents );

  if ( factors.size( ) == 1 )
  {
    // It's an A-path
    if ( a_factor )
    {
      for ( unsigned i = 0 ; i < parents.size( ) ; i ++ )
	Brec( parents[ i ], b_premise_set, cache );
    }
    // It's a B-path
    else
      b_premise_set.push_back( p );
  }
  else
  {
    // Recurse on factors
    for ( unsigned i = 0 ; i < factors.size( ) ; i ++ )
      Brec( factors[ i ], b_premise_set, cache );
  }
}
//
// We don't know how to reach x from y. There are
// three cases to consider (see below). This procedure
// retrieves the edges in the correct order to reach
// y from x
//
size_t CGraph::getSortedEdges( CNode * x
                             , CNode * y
			     , vector< CEdge * > & sorted_edges )
{
  assert( x );
  assert( y );
  assert( x != y );

  CNode * x_orig = x;
  CNode * y_orig = y;

  set< CNode * > visited;
  visited.insert( x );
  visited.insert( y );

  vector< CEdge * > & from_x = sorted_edges;
  vector< CEdge * > tmp;

  bool done = false;
  while( !done )
  {
    // Advance x by 1
    if ( x->next != NULL )
    {
      CEdge * candidate = x->next;
      x = x->next->target;
      // Touching an already seen node (by y)
      // x is the nearest common ancestor
      // Clear y vector until x is found
      if ( !visited.insert( x ).second )
      {
	while( !tmp.empty( ) && tmp.back( )->target != x )
	  tmp.pop_back( );	  
	done = true;
      }
      from_x.push_back( candidate );
    }
    if ( done ) break;
    // Advance y by 1
    if ( y->next != NULL )
    {
      CEdge * candidate = y->next;
      y = y->next->target;
      // Touching an already seen node (by x)
      // y is the nearest common ancestor
      // Clear x vector until y is found
      if ( !visited.insert( y ).second )
      {
	while( !from_x.empty( ) && from_x.back( )->target != y )
	  from_x.pop_back( );	  
	done = true;
      }
      tmp.push_back( candidate );
    }
  }
  x = x_orig;
  y = y_orig;

#if 0
  // Retrieve edges from y
  vector< CEdge * > tmp;
  // Load edges from x
  while ( x->next != NULL )
  {
    sorted_edges.push_back( x->next );
    if ( x->next->target == y )
      break;
    x = x->next->target;
  }
  // If y was reached, fine, otherwise check path from y
  if ( x->next == NULL || x->next->target != y )
  {
    while ( y->next != NULL )
    {
      tmp.push_back( y->next );
      if ( y->next->target == x_orig )
	break;
      y = y->next->target;
    }
    // If reached from y, then forget about current x, and
    // restore original x
    if ( y->next != NULL && y->next->target == x_orig )
    {
      sorted_edges.clear( );
      x = x_orig;
    }
  }
#endif

  const size_t x_path_length = sorted_edges.size( );

  // The two paths must collide
  assert( !tmp.empty( ) || sorted_edges.back( )->target == y );
  assert( !sorted_edges.empty( ) || tmp.back( )->target == x );
  assert( sorted_edges.empty( ) 
       || tmp.empty( ) 
       || sorted_edges.back( )->target == tmp.back( )->target );

  // Now load edges from y in the correct order
  while ( !tmp.empty( ) )
  {
    sorted_edges.push_back( tmp.back( ) );
    tmp.pop_back( );
  }

  return x_path_length;
#if 0
  assert( x );
  assert( y );
  assert( x != y );
  // So there are 3 cases
  // 1. x --> ... --> y
  // 2. x <-- ... <-- y
  // 3. x --> ... <-- y
  // Check if from x we can reach y
  CNode * n = x;
  while ( n->next != NULL && n != y ) 
  {
    sorted_edges.push_back( n->next );
    n = n->next->target;
  }
  const bool case1 = n == y;
  // Nothing else to do
  if ( case1 ) return sorted_edges.size( );
  // Check if from y we can reach x
  n = y;
  vector< CEdge * > tmp;
  while ( n->next != NULL && n != x )
  {
    tmp.push_back( n->next );
    n = n->next->target;
  }
  const bool case2 = n == x;
  if ( case2 )
  {
    // Fill sorted_edges in reverse order
    sorted_edges.clear( );
    while ( !tmp.empty( ) ) 
    {
      sorted_edges.push_back( tmp.back( ) );
      tmp.pop_back( );
    }
    return 0;
  }
  const size_t x_path_length = sorted_edges.size( );
  // The two paths must collide
  assert( !tmp.empty( ) || sorted_edges.back( )->target == y );
  assert( !sorted_edges.empty( ) || tmp.back( )->target == x );
  assert( sorted_edges.empty( ) 
       || tmp.empty( ) 
       || sorted_edges.back( )->target == tmp.back( )->target );
  // Now load edges from y in the correct order
  while ( !tmp.empty( ) )
  {
    sorted_edges.push_back( tmp.back( ) );
    tmp.pop_back( );
  }
  return x_path_length;
#endif
}

//
// Return the set of factors
bool CGraph::getFactorsAndParents( const path_t &     p
				 , vector< path_t > & factors
                                 , vector< path_t > & parents )
{
  assert( factors.size( ) == 1 );
  assert( parents.size( ) == 0 );
  CNode * x = p.first;
  CNode * y = p.second;
  assert( x );
  assert( y );
  vector< CEdge * > sorted_edges;
  const size_t x_path_length = getSortedEdges( x, y, sorted_edges );
  const bool a_factor = sorted_edges[ 0 ]->color == CG_A;
  uint64_t last_color = sorted_edges[ 0 ]->color;
  x = 0 < x_path_length 
    ? sorted_edges[ 0 ]->target
    : sorted_edges[ 0 ]->source ;
  y = p.second;
  size_t i = 1;
  // Add parents
  if ( sorted_edges[ 0 ]->reason == NULL )
  {
    CNode * tx = p.first;
    CNode * tn = x;
    assert( tx->e->getArity( ) == tn->e->getArity( ) );
    // Examine children of the congruence edge
    Enode * arg_list_tx, * arg_list_tn;
    for ( arg_list_tx = tx->e->getCdr( )
	, arg_list_tn = tn->e->getCdr( )
	; !arg_list_tx->isEnil( ) 
	; arg_list_tx = arg_list_tx->getCdr( )
	, arg_list_tn = arg_list_tn->getCdr( ) )
    {
      Enode * arg_tx = arg_list_tx->getCar( );
      Enode * arg_tn = arg_list_tn->getCar( );
      if ( arg_tn == arg_tx ) continue;
      // Add parents for further recursion
      parents.push_back( path( cnodes_store[ arg_tx->getId( ) ]
	                     , cnodes_store[ arg_tn->getId( ) ] ) );
    }
  }
  CNode * n;
  while( x != y )
  {
    // Next x
    n = i < x_path_length 
      ? sorted_edges[ i ]->target
      : sorted_edges[ i ]->source ;
    // Retrieve parents for congruence edges
    if ( sorted_edges[ i ]->reason == NULL )
    {
      assert( x->e->getArity( ) == n->e->getArity( ) );
      // Examine children of the congruence edge
      Enode * arg_list_x, * arg_list_n;
      for ( arg_list_x = x->e->getCdr( )
	  , arg_list_n = n->e->getCdr( )
	  ; !arg_list_x->isEnil( ) 
	  ; arg_list_x = arg_list_x->getCdr( )
	  , arg_list_n = arg_list_n->getCdr( ) )
      {
	Enode * arg_x = arg_list_x->getCar( );
	Enode * arg_n = arg_list_n->getCar( );
	if ( arg_n == arg_x ) continue;
	// Add parents for further recursion
        parents.push_back( path( cnodes_store[ arg_x->getId( ) ]
	                       , cnodes_store[ arg_n->getId( ) ] ) );
      }
    }
    // New factor
    if ( i < sorted_edges.size( )
      && sorted_edges[ i ]->color != last_color )
    {
      factors.back( ).second = x;
      factors.push_back( path( x, y ) );
      last_color = sorted_edges[ i ]->color;
    }
    // Increment
    i ++;
    // Pass to next
    x = n;
  }

  return a_factor;
}

void CGraph::printAsDotty( ostream & os )
{
  os << "digraph cgraph {" << endl;
  // Print all nodes
  for ( map< enodeid_t, CNode * >::iterator it = cnodes_store.begin( ) 
      ; it != cnodes_store.end( )
      ; it ++ )
  {
    CNode * c = it->second;
    string color = "grey";
    if ( c->color == CG_A ) color = "red";
    if ( c->color == CG_B ) color = "blue";
    if ( c->color == CG_AB ) color = "green";
    os << c->e->getId( ) 
       << " [label=\"" 
       << c->e 
       << "\",color=\"" << color
       << "\",style=filled]" 
       << endl;
    /*
    if ( c->e->getArity( ) > 0 )
    {
      Enode * args = c->e->getCdr( );
      for ( args = c->e->getCdr( ) 
	  ; !args->isEnil( )
	  ; args = args->getCdr( ) )
      {
	Enode * arg = args->getCar( );
	if ( cnodes_store.find( arg->getId( ) ) == cnodes_store.end( ) )
	  continue;
	os << c->e->getId( ) 
	   << " -> " 
	   << arg->getId( )
	   << " [style=dotted]" 
	   << endl;
      }
    }
    */
  }
  // Print all edges
  for ( size_t i = 0 ; i < cedges.size( ) ; i ++ )
  {
    CEdge * c = cedges[ i ];
    string color = "grey";
    if ( c->color == CG_A ) color = "red";
    if ( c->color == CG_B ) color = "blue";
    if ( c->color == CG_AB ) color = "green";
    os << c->source->e->getId( ) 
       << " -> " 
       << c->target->e->getId( ) 
       << " [color=\"" << color
       << "\",style=\"bold"
       << (c->reason == NULL ? ",dashed" : "")
       << "\"]"
       << endl;
  }
  // Print conflict
  os << conf1->getId( )
     << " -> "
     << conf2->getId( )
     << " [style=bold]"
     << endl;
  os << "}" << endl; 
}
#endif
