/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008-2010, Roberto Bruttomesso

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

#include <sstream>
#include "util/fp.h"
#include "egraph/Egraph.h"
#include "common/LA.h"
#include "simplifiers/BVNormalize.h"
#include "simplifiers/BVBooleanize.h"
#include "smtsolvers/SimpSMTSolver.h"
#include "version.h"

using std::ostringstream;
using std::stod;
using std::cerr;
using std::endl;
using std::pair;
using std::make_pair;
using std::vector;
using std::map;
using std::string;
using std::list;
using std::ostream;
using std::ofstream;
using std::runtime_error;

void Egraph::initializeStore( )
{
  //
  // Reserve room for at least 65536 nodes
  //
  id_to_enode .reserve( 65536 );

  assert( config.logic != UNDEF );

  //
  // Create default sorts
  //
  Snode * sbool0  = sort_store.mkBool( );
  Snode * spara0  = sort_store.mkPara( "A" );
  sarith0 = config.logic == QF_LIA
         || config.logic == QF_IDL
         || config.logic == QF_UFIDL
          ? sort_store.mkInt ( )
          : sort_store.mkReal( );
  Snode * sarray0 = sort_store.mkArray( );
  Snode * selem0  = sort_store.mkElem ( );
  Snode * sindex0 = sort_store.mkIndex( );
  //
  // Some useful shortcuts
  //
  Snode * sbool1_list  = sort_store.cons( sbool0 );
  Snode * sbool2_list  = sort_store.cons( sbool0, sbool1_list );
  Snode * sbool3_list  = sort_store.cons( sbool0, sbool2_list );

  Snode * sbool2       = sort_store.mkDot( sbool2_list );

  Snode * sbool3_right = sort_store.mkDot( sbool3_list, RIGHT_ASSOC );
  Snode * sbool3_left  = sort_store.mkDot( sbool3_list, LEFT_ASSOC );

  Snode * spara2_bool = sort_store.mkDot( sort_store.cons( spara0
                                        , sort_store.cons( spara0
                                        , sort_store.cons( sbool0 ) ) ) );

  Snode * sbool_para3 = sort_store.mkDot( sort_store.cons( sbool0
                                        , sort_store.cons( spara0
                                        , sort_store.cons( spara0
                                        , sort_store.cons( spara0 ) ) ) ) );
  //
  // Allocates SMTLIB predefined symbols
  //
  newSymbol( "true"    , sbool0 ); assert( ENODE_ID_TRUE    == id_to_enode.size( ) - 1 );
  newSymbol( "false"   , sbool0 ); assert( ENODE_ID_FALSE   == id_to_enode.size( ) - 1 );
  //
  // Core
  //
  newSymbol( "not"     , sbool2 );       assert( ENODE_ID_NOT     == id_to_enode.size( ) - 1 );
  newSymbol( "=>"      , sbool3_right ); assert( ENODE_ID_IMPLIES == id_to_enode.size( ) - 1 );
  newSymbol( "and"     , sbool3_left  ); assert( ENODE_ID_AND     == id_to_enode.size( ) - 1 );
  newSymbol( "or"      , sbool3_left  ); assert( ENODE_ID_OR      == id_to_enode.size( ) - 1 );
  newSymbol( "xor"     , sbool3_left  ); assert( ENODE_ID_XOR     == id_to_enode.size( ) - 1 );
  newSymbol( "="       , spara2_bool  ); assert( ENODE_ID_EQ      == id_to_enode.size( ) - 1 );
  newSymbol( "ite"     , sbool_para3  ); assert( ENODE_ID_ITE     == id_to_enode.size( ) - 1 );
  //
  // Distinct
  // Sort is actually different, as a distinction may contain several terms.
  // However this is the only case in all the SMTLIB and dealt with as a
  // special one
  //
  newSymbol( "distinct", sbool0       ); assert( ENODE_ID_DISTINCT == id_to_enode.size( ) - 1 );
  //
  // Arithmetic predefined operators and predicates
  //
  // TODO: from here down this has to be changed to something
  //       that parses the signature ...
  //
  //
  // Some useful shortcuts
  //
  Snode * sarith1_list = sort_store.cons( sarith0 );
  Snode * sarith2_list = sort_store.cons( sarith0, sarith1_list );

  Snode * sarith1       = sort_store.mkDot( sarith1_list );
  Snode * sarith2_left  = sort_store.mkDot( sarith2_list, LEFT_ASSOC  );

  Snode * sarith1_bool  = sort_store.mkDot( sort_store.cons( sarith0
                                          , sort_store.cons( sbool0 ) ) );

  Snode * sarith2_bool  = sort_store.mkDot( sort_store.cons( sarith0
                                          , sort_store.cons( sarith0
                                          , sort_store.cons( sbool0 ) ) ) );
  Snode * sarith5_bool = sort_store.mkDot(sort_store.cons( sarith0,
                                          sort_store.cons( sarith0,
                                          sort_store.cons( sarith0,
                                          sort_store.cons( sarith0,
                                          sort_store.cons( sarith0,
                                          sort_store.cons( sbool0 )))))));

  newSymbol( "+"       , sarith2_left ); assert( ENODE_ID_PLUS   == id_to_enode.size( ) - 1 );
  newSymbol( "-"       , sarith1      ); assert( ENODE_ID_MINUS  == id_to_enode.size( ) - 1 );
  newSymbol( "-"       , sarith2_left ); assert( ENODE_ID_UMINUS == id_to_enode.size( ) - 1 );
  newSymbol( "*"       , sarith2_left ); assert( ENODE_ID_TIMES  == id_to_enode.size( ) - 1 );
  newSymbol( "/"       , sarith2_left ); assert( ENODE_ID_DIV    == id_to_enode.size( ) - 1 );
  newSymbol( "<="      , sarith2_bool ); assert( ENODE_ID_LEQ    == id_to_enode.size( ) - 1 );
  newSymbol( ">="      , sarith2_bool ); assert( ENODE_ID_GEQ    == id_to_enode.size( ) - 1 );
  newSymbol( "<"       , sarith2_bool ); assert( ENODE_ID_LT     == id_to_enode.size( ) - 1 );
  newSymbol( ">"       , sarith2_bool ); assert( ENODE_ID_GT     == id_to_enode.size( ) - 1 );
  //
  // Array operators
  //
  Snode * sarray_index_elem_array = sort_store.mkDot( sort_store.cons( sarray0
                                                    , sort_store.cons( sindex0
                                                    , sort_store.cons( selem0
                                                    , sort_store.cons( sarray0 ) ) ) ) );

  Snode * sarray_index_elem = sort_store.mkDot( sort_store.cons( sarray0
                                              , sort_store.cons( sindex0
                                              , sort_store.cons( selem0 ) ) ) );

  newSymbol( "store"   , sarray_index_elem_array ); assert( ENODE_ID_STORE  == id_to_enode.size( ) - 1 );
  newSymbol( "select"  , sarray_index_elem       ); assert( ENODE_ID_SELECT == id_to_enode.size( ) - 1 );

  /* added for dReal2 */
  newSymbol( "exp"       , sarith1 ); assert( ENODE_ID_EXP   == id_to_enode.size( ) - 1 );
  newSymbol( "log"       , sarith1 ); assert( ENODE_ID_LOG   == id_to_enode.size( ) - 1 );
  newSymbol( "sin"       , sarith1 ); assert( ENODE_ID_SIN   == id_to_enode.size( ) - 1 );
  newSymbol( "cos"       , sarith1 ); assert( ENODE_ID_COS   == id_to_enode.size( ) - 1 );
  newSymbol( "tan"       , sarith1 ); assert( ENODE_ID_TAN   == id_to_enode.size( ) - 1 );
  newSymbol( "asin"      , sarith1 ); assert( ENODE_ID_ASIN == id_to_enode.size( ) - 1 );
  newSymbol( "acos"      , sarith1 ); assert( ENODE_ID_ACOS == id_to_enode.size( ) - 1 );
  newSymbol( "atan"      , sarith1 ); assert( ENODE_ID_ATAN == id_to_enode.size( ) - 1 );
  newSymbol( "sinh"      , sarith1 ); assert( ENODE_ID_SINH   == id_to_enode.size( ) - 1 );
  newSymbol( "cosh"      , sarith1 ); assert( ENODE_ID_COSH   == id_to_enode.size( ) - 1 );
  newSymbol( "tanh"      , sarith1 ); assert( ENODE_ID_TANH   == id_to_enode.size( ) - 1 );
  newSymbol( "^"         , sarith2_left); assert (ENODE_ID_POW == id_to_enode.size() - 1 );
  newSymbol( "atan2"     , sarith2_left ); assert( ENODE_ID_ATAN2 == id_to_enode.size( ) - 1 );
  newSymbol( "matan"     , sarith1 ); assert( ENODE_ID_MATAN == id_to_enode.size( ) - 1 );
  newSymbol( "safesqrt"  , sarith1 ); assert( ENODE_ID_SAFESQRT == id_to_enode.size( ) - 1 );
  newSymbol( "sqrt"      , sarith1 ); assert( ENODE_ID_SQRT == id_to_enode.size( ) - 1 );
  newSymbol( "forallt"   , sarith1_bool ); assert( ENODE_ID_FORALLT == id_to_enode.size( ) - 1 );
  newSymbol( "integral"  , sarith5_bool ); assert( ENODE_ID_INTEGRAL == id_to_enode.size( ) - 1 );
  newSymbol( "abs"       , sarith1 ); assert( ENODE_ID_ABS == id_to_enode.size( ) - 1 );
  newSymbol( "min"       , sarith2_left ); assert( ENODE_ID_MIN == id_to_enode.size( ) - 1 );
  newSymbol( "max"       , sarith2_left ); assert( ENODE_ID_MAX == id_to_enode.size( ) - 1 );
  newSymbol( "forall"    , sbool2 ); assert( ENODE_ID_FORALL == id_to_enode.size( ) - 1 );
  newSymbol( "exists"    , sbool2 ); assert( ENODE_ID_EXISTS == id_to_enode.size( ) - 1 );
  /* ---------------- */

 //
  // Set top node to empty
  //
  top = nullptr;
  //
  // Allocate true and false
  //
  etrue  = allocTrue ( );
  efalse = allocFalse( );
  //
  // Does not have ites (yet)
  //
  has_ites = false;
  //
  // Inserts true and false in signature table
  //
  insertSigTab( etrue );
  insertSigTab( efalse );
}

void   Egraph::setPrecision ( double p)
{
    if (p < 0) {
        cerr << "Precision should be positive number: Current Value = " << p << endl;
        exit(1);
    }

    // Assign the new precision value only if we do not have one from
    // the command-line arguments
    if(config.nra_precision == 0.0)
        precision = p;
}

double Egraph::getPrecision( ) const
{
    return precision;
}

//
// Allocates true
//
Enode * Egraph::allocTrue ( )
{
  Enode * res = cons( id_to_enode[ ENODE_ID_TRUE ] );
  assert( res );
  assert( res->isTerm( ) );
  res->allocCongData( );
  res->setConstant( res );
  return res;
}

//
// Allocates false
//
Enode * Egraph::allocFalse ( )
{
  Enode * res = cons( id_to_enode[ ENODE_ID_FALSE ] );
  assert( res );
  assert( res->isTerm( ) );
  res->allocCongData( );
  res->setConstant( res );
  return res;
}

//
// Inserts a number
//
Enode * Egraph::insertNumber( Enode * n )
{
  assert( n->isNumb( ) );
  pair< map< string, Enode * >::iterator, bool > res = name_to_number.insert( make_pair( n->getName( ), n ) );
  // Number has been inserted
  if ( res.second )
  {
    // TODO: should make this incremental as well ? not clear
    // undo_stack_term.push_back( n );
    // undo_stack_oper.push_back( NUMB );
    id_to_enode .push_back( n );
    assert( n->getId( ) == (enodeid_t)id_to_enode.size( ) - 1 );
    return n;
  }
  // Number was already there, get rid of n
  delete n;
  // Return the old one
  return res.first->second;
}

//
// Inserts a symbol
//
void Egraph::insertSymbol( Enode * s )
{
  assert( s );
  assert( s->isSymb( ) );
  // Consistency for id
  assert( (enodeid_t)id_to_enode.size( ) == s->getId( ) );
  // Symbol is not there
  assert( name_to_symbol.find( s->getNameFull( ) ) == name_to_symbol.end( ) );
  // Insert Symbol
  name_to_symbol[ s->getNameFull( ) ] = s;
  id_to_enode .push_back( s );
}

//
// Removes a symbol
//
void Egraph::removeSymbol( Enode * s )
{
  assert( s->isSymb( ) );
  assert( config.incremental );
  map< string, Enode * >::iterator it = name_to_symbol.find( s->getName( ) );
  assert( it != name_to_symbol.end( ) );
  assert( it->second == s );
  name_to_symbol.erase( it );
  id_to_enode[ s->getId( ) ] = nullptr;
  delete s;
}

//
// Inserts a number
//
void Egraph::removeNumber( Enode * n )
{
  assert( n->isNumb( ) );
  assert( config.incremental );
  map< string, Enode * >::iterator it = name_to_number.find( n->getName( ) );
  assert( it != name_to_number.end( ) );
  assert( it->second == n );
  name_to_number.erase( it );
  assert( n->getId( ) == (enodeid_t)id_to_enode.size( ) - 1 );
  id_to_enode.pop_back( );
  delete n;
}

//
// Retrieves a symbol from the name
//
Enode * Egraph::lookupSymbol( const char * name )
{
  assert( name );
  map< string, Enode * >::iterator it = name_to_symbol.find( name );
  if ( it == name_to_symbol.end( ) ) return nullptr;
  return it->second;
}

//
// Retrieves a define
//
Enode * Egraph::lookupDefine( const char * name )
{
  assert( name );
  map< string, Enode * >::iterator it = name_to_define.find( name );
  if ( it == name_to_define.end( ) ) return nullptr;
  return it->second;
}

//
// Store a define
//
void Egraph::insertDefine( const char * n, Enode * d )
{
  assert( d );
  assert( n );
  assert( d->isDef( ) );
  assert( (enodeid_t)id_to_enode.size( ) == d->getId( ) );
  assert( name_to_define.find( n ) == name_to_define.end( ) );
  name_to_define[ n ] = d;
  id_to_enode.push_back( d );
}

//
// Insert into signature table possibly creating a new node
//
Enode * Egraph::insertSigTab ( const enodeid_t id, Enode * car, Enode * cdr )
{
  assert( car == car->getRoot( ) );
  assert( cdr == cdr->getRoot( ) );

#ifdef BUILD_64
  enodeid_pair_t sig = encode( car->getCid( ), cdr->getCid( ) );
#else
  const Pair( enodeid_t ) sig = make_pair( car->getCid( ), cdr->getCid( ) );
#endif
  Enode * res = sig_tab.lookup( sig );

  if ( res == nullptr )
  {
    Enode * e = new Enode( id, car, cdr );
    sig_tab.insert( e );
    return e;
  }

  return res;
}

//
// Insert into Store
//
Enode * Egraph::insertStore( const enodeid_t id, Enode * car, Enode * cdr )
{
  Enode * e = new Enode( id, car, cdr );
  Enode * x = store.insert( e );
  // Insertion done
  if ( x == e ) return e;
  // Node already there
  delete e;
  return x;
}

//
// Remove from Store
//
void Egraph::removeStore( Enode * e )
{
  assert( e );
  store.remove( e );
}

//
// Retrieve element from signature table
//
Enode * Egraph::lookupSigTab ( Enode * e )
{
  Enode * res = sig_tab.lookup( e->getSig( ) );
  return res;
}

//
// Adds element to signature table
//
Enode * Egraph::insertSigTab ( Enode * e )
{
  sig_tab.insert( e );
  return e;
}

//
// Remove element from signature table
//
void Egraph::removeSigTab ( Enode * e )
{
  assert( lookupSigTab( e ) );
  sig_tab.erase( e );
}

//
// Copy list into a new one whose elements are retrieved from the cache
//

Enode * Egraph::copyEnodeEtypeListWithCache( Enode * l, bool map2 )
{
  assert(  map2 || active_dup_map1 );
  assert( !map2 || active_dup_map2 );

  list< Enode * > new_args;
  for ( Enode * arg = l ; !arg->isEnil( ) ; arg = arg->getCdr( ) )
  {
    new_args.push_front( map2
                       ? valDupMap2( arg->getCar( ) )
                       : valDupMap1( arg->getCar( ) )
                       );
  }

  Enode * res = cons( new_args );
  return res;
}

//
// Create a new term of the same kind but using info in the cache and
// also performs some simplifications
//
Enode * Egraph::copyEnodeEtypeTermWithCache( Enode * term, bool map2 )
{
  assert(  map2 || active_dup_map1 );
  assert( !map2 || active_dup_map2 );
  Enode * ll = copyEnodeEtypeListWithCache( term->getCdr( ), map2 );
  assert( ll->isList( ) );
  //
  // Case
  //
  if ( term->isAnd        ( ) ) return mkAnd       ( ll );
  if ( term->isOr         ( ) ) return mkOr        ( ll );
  if ( term->isNot        ( ) ) return mkNot       ( ll );
  if ( term->isImplies    ( ) ) return mkImplies   ( ll );
  if ( term->isXor        ( ) ) return mkXor       ( ll );
  if ( term->isEq         ( ) ) return mkEq        ( ll );
  if ( term->isLeq        ( ) ) return mkLeq       ( ll );
  if ( term->isPlus       ( ) ) return mkPlus      ( ll );
  if ( term->isTimes      ( ) ) return mkTimes     ( ll );
  if ( term->isDiv        ( ) ) return mkDiv       ( ll );
  if ( term->isDistinct   ( ) ) return mkDistinct  ( ll );

  if ( ll->getArity( ) == 3 )
  {
    Enode * i = ll->getCar( );
    Enode * t = ll->getCdr( )->getCar( );
    Enode * e = ll->getCdr( )->getCdr( )->getCar( );

    if ( term->isIte        ( ) ) return mkIte        ( i, t, e );
  }

  if ( term->isVar( ) || term->isConstant( ) )
    return term;

  //
  // Enable if you want to make sure that your case is handled
  //
  // error( "Please add a case for ", term->getCar( ) );

  Enode * new_term = cons( term->getCar( ), ll );
  return new_term;
}

//
// FIXME: This is a little bit counter intuitive
// The list given is now in reverse order w.r.t.
// the returned one, they should insted be the
// same, more logical. But that implies that we
// have to modify other parts of the code, so
// be careful
//
Enode * Egraph::cons( list< Enode * > & args )
{
  Enode * elist = const_cast< Enode * >( enil );

  for ( list< Enode * >::iterator it = args.begin( )
      ; it != args.end( )
      ; it ++ )
    elist = cons( *it, elist );

  return elist;
}

//
// Creates a new term and its correspondent modulo equivalence
//
Enode * Egraph::cons( Enode * car, Enode * cdr )
{
  assert( car );
  assert( cdr );
  assert( car->isTerm( ) || car->isSymb( ) || car->isNumb( ) );
  assert( cdr->isList( ) );
  Enode * e = nullptr;
  // Create and insert a new enode if necessary
  e = insertStore( id_to_enode.size( ), car, cdr );
  assert( e );
  // The node was there already. Return it
  if ( (enodeid_t)id_to_enode.size( ) != e->getId( ) )
    return e;

  /*
   * Had to disable because of problems
   * connected with incrementality of
   * congruence closure. It seems that a node
   * after it is removed still survive in the
   * signature tab, causing obvious inconsistencies
   * in the invariants
   *
   * TO BE CLARIFIED !
   *
  if ( config.incremental )
  {
    // Save Backtrack information
    undo_stack_term.push_back( e );
    undo_stack_oper.push_back( INSERT_STORE );
  }
  */

  // We keep the created enode
  id_to_enode.push_back( e );
  return e;
}

//
// Create a variable
//

/*
   TODO: create mkVar which takes LB and RB of a variable
 */
Enode * Egraph::mkVar( const char * name, bool model_var )
{
  Enode * e = lookupSymbol( name );
  // Not a variable, is it a define ?
  if ( e == nullptr )
  {
    e = lookupDefine( name );
    // Not a define, abort
    if ( e == nullptr )
      opensmt_error2( "undeclared identifier ", name );
    assert( e->isDef( ) );
    // It's a define, return itss definition
    return e->getDef( );
  }
  // It's a variable
  Enode * res = cons( e );
  if ( model_var )
    variables.insert( res );
  return res;
}

Enode * Egraph::mkNum( const char * value )
{
  Enode * const new_enode = new Enode( id_to_enode.size( )
                                       , value
                                       , ETYPE_NUMB
                                       , sarith0 );
  assert( new_enode );
  Enode * const res = insertNumber( new_enode );
  Enode * const ret = cons ( res );
  double const lb = dreal::stod_downward(res->getName());
  double const ub = dreal::stod_upward(res->getName());
  ret->setValueLowerBound(lb);
  ret->setValueUpperBound(ub);
  return ret;
}

Enode * Egraph::mkNum(const double v)
{
  char buf[ 256 ];
  sprintf( buf, "%.30lf", v );
  return mkNum(buf);
}

// Enode * Egraph::mkNum( const Real & real_value )
// {
// #if FAST_RATIONALS
//   return mkNum( const_cast< char * >(real_value.get_str( ).c_str( )) );
// #elif USE_GMP
//   return mkNum( const_cast< char * >(real_value.get_str( ).c_str( )) );
// #else
//   char buf[ 128 ];
//   sprintf( buf, "%lf", real_value );
//   return mkNum( buf );
// #endif
// }

Enode * Egraph::mkNum( const char * num, const char * den )
{
  string s = (string)num + "/" + (string)den;

// #if FAST_RATIONALS
//   Real real_value( s.c_str() );
//   return mkNum( const_cast< char * >(real_value.get_str( ).c_str( )) );
// #else
  double const num_d = stod( num );
  double const den_d = stod( den );
  double const value = num_d / den_d;
  return mkNum( value );
}

Enode * Egraph::mkFun( const char * name, Enode * args )
{
  assert( args->isList( ) );
  //
  // Retrieve sort from arguments
  //
  ostringstream ss;
  ss << name;
  for ( Enode * l = args ; !l->isEnil( ) ; l = l->getCdr( ) )
  {
    ss << " ";
    l->getCar( )->getLastSort( )->print( ss, false );
  }

  Enode * e = lookupSymbol( ss.str( ).c_str( ) );
  if ( e == nullptr ) opensmt_error2( "undeclared function symbol ", ss.str( ).c_str( ) );

  Enode * ret = cons( e, args );

  return ret;
}

//
// Creates a new symbol. Name must be new
//
Enode * Egraph::newSymbol( const char * name, Snode * s , bool isModelVar, double p )
{
  assert( s );
  assert( s->isTerm( ) );

  ostringstream ss;
  ss << name;
  const string args = s->getArgs( );
  if ( args != "" ) ss << " " << args;

  Enode * e = lookupSymbol( ss.str( ).c_str( ) );
  if ( e != nullptr ) {
      if ( e->getSort() != s ) {
          opensmt_error2( "symbol already declared ", ss.str( ).c_str( ) );
      } else {
          return e;
      }
  }

  Enode * new_enode = new Enode( id_to_enode.size( )
                               , ss.str( ).c_str( )
                               , ETYPE_SYMB
                               , s );

  insertSymbol( new_enode );
  assert( lookupSymbol( ss.str( ).c_str( ) ) == new_enode );
  if (p != 0.0) {
    new_enode->setPrecision(p);
  }

  if (isModelVar) {
      mkVar(ss.str().c_str(), true);
  }

  return new_enode;
}

Enode * Egraph::getDefine( const char * name )
{
  Enode * e = lookupDefine( name );
  assert( e );
  assert( e->getCar( ) != nullptr );
  return e->getCar( );
}

void Egraph::mkDefine( const char * name, Enode * def )
{
  Enode * e = lookupDefine( name );
  if( e == nullptr )
  {
    Enode * new_enode = new Enode( id_to_enode.size( ), def );
    insertDefine( name, new_enode );
  }
  else
  {
    // This symbol has been declared before. We just
    // replace its definition with this new one
    e->setDef( def );
  }
}

Enode * Egraph::mkSelect( Enode * a, Enode * i )
{
  //
  // Check arguments: select is applied to an array expression and
  // an index expression remember the possibility of having ite
  // expressions as arguments
  //
  assert( a );
  assert( i );
  assert( a->hasSortArray( ) );
  assert( config.logic != QF_AX || i->hasSortIndex( ) );
  Enode * newSel = cons( id_to_enode[ ENODE_ID_SELECT ], cons( a, cons( i ) ) );
  return newSel;
}

Enode * Egraph::mkStore( Enode * a, Enode * i, Enode * e )
{
  //
  // check arguments: select is applied to an array expression,
  // an index expression, and an element expression
  // remember the possibility of having ite expressions as arguments
  //
  assert( a );
  assert( i );
  assert( e );
  assert( a->hasSortArray( ) );
  assert( config.logic != QF_AX    || i->hasSortIndex( ) );
  assert( config.logic != QF_AX    || e->hasSortElem( ) );

  Enode * newSto = cons( id_to_enode[ ENODE_ID_STORE ], cons( a, cons( i, cons( e ) ) ) );

  return newSto;
}

Enode * Egraph::mkEq( Enode * args )
{
  assert( args );
  assert( args->isList( ) );
  assert( args->getCar( ) );
  assert( args->getCdr( )->getCar( ) );
  if (!args || !args->isList() || !args->getCar() || !args->getCdr()->getCar()) {
      return nullptr;
  }

  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );
  // TODO(soonhok): for now, we remove the requirement that
  // "sort(LHS) = sort(RHS)". We still need to check LHS and RHS are
  // Real and Int (or Int/Real).
  //
  // assert( x->getLastSort( ) == y->getLastSort( ) );

  if ( x->hasSortBool( ) )
    return mkIff( args );

  // Two equal terms
  // x = x => true
  if ( x == y )
    return mkTrue( );

  // Constants
  //
  // Soonho: Previously, we return False if both of x and y are
  // constants but their pointers are not the same. However, it's
  // possible that two different Enodes are equal. For example,
  // consider Enode("0.00") and Enode("0.0"). When constructed, they
  // are two different Enodes (because it only checks string value)
  // but we should have "0.0 == 0".
  if ( x->isConstant( ) && y->isConstant( ) ) {
    if (x->getValueLowerBound() == y->getValueLowerBound() &&
        x->getValueUpperBound() == y->getValueUpperBound()) {
      return mkTrue( );
    } else {
      return mkFalse( );
    }
  }

  if ( x->getId( ) > y->getId( ) )
    args = cons( y, cons( x ) );

  return cons( id_to_enode[ ENODE_ID_EQ ], args );
}

Enode * Egraph::mkLeq( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if ( !args || args->getArity() != 2) {
      return nullptr;
  }

  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );

  assert( !x->hasSortBool( ) );
  assert( !y->hasSortBool( ) );

  // Two equal terms
  // x = x => true
  if ( x == y )
    return mkTrue( );

  // Two constants: evaluate
  if ( x->isConstant( ) && y->isConstant( ) )
    return x->getValue( ) <= y->getValue( )
         ? mkTrue ( )
         : mkFalse( );

  Enode * res = cons( id_to_enode[ ENODE_ID_LEQ ], args );
  return res;
}


/* added for dReal2 */
//transcendental functions
Enode * Egraph::mkAbs (Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(fabs(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_ABS], args );
  assert( res );
  return res;
}

Enode * Egraph::mkPow (Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if ( !args || args->getArity() != 2) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg1 = args->getCar();
    Enode * const arg2 = args->getCdr()->getCar();
    if (arg1->isConstant() && arg2->isConstant()) {
      return mkNum(pow(arg1->getValue(), arg2->getValue()));
    }
    if (arg2->isConstant() && arg2->getValue() == 1) {
      // x ^ 1 = x
      return arg1;
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_POW], args );
  assert( res );
  return res;
}

Enode * Egraph::mkSin              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(sin(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_SIN], args );
  assert( res );
  return res;
}

Enode * Egraph::mkCos              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(cos(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_COS], args );
  assert( res );
  return res;
}

Enode * Egraph::mkTan              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(tan(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_TAN], args );
  assert( res );
  return res;
}

Enode * Egraph::mkAsin              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(asin(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_ASIN], args );
  assert( res );
  return res;
}

Enode * Egraph::mkAcos              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(acos(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_ACOS], args );
  assert( res );
  return res;
}

Enode * Egraph::mkAtan              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(atan(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_ATAN], args );
  assert( res );
  return res;
}

Enode * Egraph::mkSinh             ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(sinh(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_SINH ], args );
  assert( res );
  return res;
}

Enode * Egraph::mkCosh             ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(cosh(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_COSH ], args );
  assert( res );
  return res;
}

Enode * Egraph::mkTanh             ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(tanh(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_TANH ], args );
  assert( res );
  return res;
}

Enode * Egraph::mkAtan2             ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if ( !args || args->getArity() != 2) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg1 = args->getCar();
    Enode * const arg2 = args->getCdr()->getCar();
    if (arg1->isConstant() && arg2->isConstant()) {
      return mkNum(atan2(arg1->getValue(), arg2->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_ATAN2], args );
  assert( res );
  return res;
}

Enode * Egraph::mkMin             ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if ( !args || args->getArity() != 2) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg1 = args->getCar();
    Enode * const arg2 = args->getCdr()->getCar();
    if (arg1->isConstant() && arg2->isConstant()) {
      return mkNum(fmin(arg1->getValue(), arg2->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_MIN], args );
  assert( res );
  return res;
}

Enode * Egraph::mkMax             ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if ( !args || args->getArity() != 2) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg1 = args->getCar();
    Enode * const arg2 = args->getCdr()->getCar();
    if (arg1->isConstant() && arg2->isConstant()) {
      return mkNum(fmax(arg1->getValue(), arg2->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_MAX], args );
  assert( res );
  return res;
}

Enode * Egraph::mkMatan             ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      double const v = arg->getValue();
      if (v == 0) {
        return mkNum(1);
      } else if (v > 0) {
        return mkNum(atan(sqrt(v) / sqrt(v)));
      } else {
        return mkNum((log((1 + sqrt(-v)) / (1 - sqrt(-v)))) / (2 * sqrt(-v)));
      }
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_MATAN], args );
  assert( res );
  return res;
}

Enode * Egraph::mkSafeSqrt            ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      double const v = arg->getValue();
      if (v >= 0.0) {
        return mkNum(v);
      } else {
        ostringstream ss;
        ss << "Failed to build an expression: safesqrt(" << v << ") "
           << "because " << v << " is negative.";
        throw runtime_error(ss.str());
      }
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_SAFESQRT], args );
  assert( res );
  return res;
}

Enode * Egraph::mkSqrt                ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(sqrt(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_SQRT], args );
  assert( res );
  return res;
}

Enode * Egraph::mkExp              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(exp(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_EXP], args );
  assert( res );
  return res;
}

Enode * Egraph::mkLog              ( Enode * args)
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  if (config.nra_simp) {
    Enode * const arg = args->getCar();
    if (arg->isConstant()) {
      return mkNum(log(arg->getValue()));
    }
  }
  Enode * res = cons( id_to_enode[ ENODE_ID_LOG], args );
  assert( res );
  return res;

}

Enode * Egraph::mkPlus( Enode * args )
{
  assert( args );
  assert( args->getArity( ) >= 1 );
  if ( !args || args->getArity() < 1) {
      return nullptr;
  }

  if ( args->getArity( ) == 1 )
    return args->getCar( );

  Enode * res = nullptr;
  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );
  //
  // Simplify constants
  //
  if ( config.nra_simp && x->isConstant( ) && y->isConstant( ) && args->getArity( ) == 2 )
  {
    const double xval = x->getValue( );
    const double yval = y->getValue( );
    double sum = xval + yval;
    res = mkPlus( cons(mkNum( sum ), args->getCdr( )->getCdr()));
  }
  else
  {
    res = cons( id_to_enode[ ENODE_ID_PLUS ], args );
  }

  assert( res );
  return res;
}

Enode * Egraph::mkMinus( Enode * args )
{
  assert( args );

  if ( !args || args->getArity() < 1) {
      return nullptr;
  }

  if ( args->getArity( ) == 1 )
    return mkUminus( args );

  assert( args->getArity( ) == 2 );

  Enode * res = nullptr;

  Enode * const x = args->getCar( );
  Enode * const y = args->getCdr( )->getCar( );

  if (config.nra_simp && x->isConstant() && y->isConstant())
  {
    res = mkNum(x->getValue() - y->getValue());
  } else {
    Enode * mo = mkNum( "-1" );
    res = mkPlus( cons( x, cons( mkTimes( cons( mo, cons( y ) ) ) ) ) );
  }
  return res;
}

Enode * Egraph::mkUminus( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 1 );
  if ( !args || args->getArity() != 1) {
      return nullptr;
  }
  Enode * const x = args->getCar( );
  if (config.nra_simp && x->isConstant()) {
    return mkNum(- x->getValue());
  }
  Enode * const mo = mkNum( "-1" );
  return mkTimes( cons( mo, cons( x ) ) );
}

Enode * Egraph::mkTimes( Enode * args )
{
  assert( args );
  assert( args->getArity( ) >= 2 );
  if ( !args || args->getArity() < 2) {
      return nullptr;
  }

  Enode * res = nullptr;
  if (config.nra_simp) {
      double const zero_ = 0;
      Enode * zero = mkNum( zero_ );

      // Check whether it contains zero or not
      bool contain_zero = false;
      for (Enode const * head = args; !head->isEnil(); head = head->getCdr()) {
          Enode const * const arg = head->getCar();
          if (arg->isConstant() && arg->getValue() == 0.0) {
              contain_zero = true;
              break;
          }
      }
      if (contain_zero) {
          res = zero;
      } else if (args->getArity() == 2) {
          Enode * x = args->getCar( );
          Enode * y = args->getCdr( )->getCar( );
          if ( x->isConstant( ) && y->isConstant( ) ) {
              // Simplify constants
              const double xval = x->getValue( );
              const double yval = y->getValue( );
              double times = xval * yval;
              res = mkNum( times );
          }
          else if ( x == y ) {
              return mkPow( cons(x, cons(mkNum(2.0)) ) );
          }
      }
  }
  if (!res) {
      res = cons( id_to_enode[ ENODE_ID_TIMES ], args );
  }
  assert( res );
  return res;
}

Enode * Egraph::mkDiv( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if ( !args || args->getArity() != 2) {
      return nullptr;
  }

  Enode * res = nullptr;
  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );

  double zero_ = 0;
  Enode * zero = mkNum( zero_ );

  if ( y == zero )
    opensmt_error2( "explicit division by zero in formula", "" );

  if (config.nra_simp) {
      //
      // 0 * x --> 0
      //
      if ( x == zero )
          {
              res = zero;
          }
      //
      // Simplify constants
      //
      else if ( x->isConstant( ) && y->isConstant( ) ) {
          const double xval = x->getValue( );
          const double yval = y->getValue( );
          double div = xval / yval;
          res = mkNum( div );
      }
  }
  if (!res) {
      res = cons( id_to_enode[ ENODE_ID_DIV ], args );
  }

  assert( res );
  return res;
}

Enode * Egraph::mkNot( Enode * args )
{
  assert( args );
  assert( args->isList( ) );
  assert( args->getCar( ) );
  if ( !args || !args->isList() || !args->getCar() ) {
      return nullptr;
  }

  Enode * arg = args->getCar( );
  assert( arg->hasSortBool( ) );
  assert( arg->isTerm( ) );
  if ( !arg || !arg->hasSortBool() || !arg->isTerm() ) {
      return nullptr;
  }

  // not not p --> p
  if ( arg->isNot( ) )
    return arg->get1st( );

  // not false --> true
  if ( arg->isFalse( ) )
    return mkTrue( );

  // not true --> false
  if ( arg->isTrue( ) )
    return mkFalse( );

  return cons( id_to_enode[ ENODE_ID_NOT ], args );
}

Enode * Egraph::mkAnd( Enode * args )
{
  assert( args );
  assert( args->isList( ) );

  if (!args || !args->isList()) {
      return nullptr;
  }

  initDup1( );

  list< Enode * > new_args;
  for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
  {
    Enode * e = alist->getCar( );
    assert( e->hasSortBool( ) );
    if (!e->hasSortBool()) {
        return nullptr;
    }

    if ( isDup1( e ) ) continue;
    if ( e->isTrue( ) ) continue;
    if ( e->isFalse( ) ) { doneDup1( ); return mkFalse( ); }

    new_args.push_front( e );
    storeDup1( e );
  }

  doneDup1( );

  Enode * res = nullptr;

  if ( new_args.size( ) == 0 )
    res = mkTrue( );
  else if ( new_args.size( ) == 1 )
    res = new_args.back( );
  else
    res = cons( id_to_enode[ ENODE_ID_AND ], cons( new_args ) );

  assert( res );
  return res;
}

Enode * Egraph::mkOr( Enode * args )
{
  assert( args );
  assert( args->isList( ) );
  if (!args || !args->isList()) {
      return nullptr;
  }

  initDup1( );

  list< Enode * > new_args;
  for ( Enode * list = args ; !list->isEnil( ) ; list = list->getCdr( ) )
  {
    Enode * e = list->getCar( );

    assert( e->hasSortBool( ) );
    if (!e->hasSortBool()) {
        return nullptr;
    }

    if ( isDup1( e ) ) continue;
    if ( e->isFalse( ) ) continue;
    if ( e->isTrue( ) ) { doneDup1( ); return mkTrue( ); }

    new_args.push_front( e );
    storeDup1( e );
  }

  doneDup1( );

  if ( new_args.size( ) == 0 )
    return mkFalse( );

  if ( new_args.size( ) == 1 )
    return new_args.back( );

  return cons( id_to_enode[ ENODE_ID_OR ], cons( new_args ) );
}

Enode * Egraph::mkIff( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if (!args || args->getArity() != 2) {
      return nullptr;
  }
  Enode * first  = args->getCar( );
  Enode * second = args->getCdr( )->getCar( );

  if ( first ->isTrue ( ) )               return second;
  if ( first ->isFalse( ) )               return mkNot( cons( second ) );
  if ( second->isTrue ( ) )               return first;
  if ( second->isFalse( ) )               return mkNot( cons( first ) );
  if ( first == second )                  return mkTrue ( );
  if ( first == mkNot( cons( second ) ) ) return mkFalse( );

  return cons( id_to_enode[ ENODE_ID_EQ ], args );
}

Enode * Egraph::mkIte( Enode * args )
{
  assert( args );
  if (!args) {
      return nullptr;
  }
  Enode * i = args->getCar( );
  Enode * t = args->getCdr( )->getCar( );
  Enode * e = args->getCdr( )->getCdr( )->getCar( );
  return mkIte( i, t, e );
}

Enode * Egraph::mkIte( Enode * i, Enode * t, Enode * e )
{
  assert( i );
  assert( t );
  assert( e );
  assert( i->hasSortBool( ) );
  if (!i || !t || !e || !i->hasSortBool()) {
      return nullptr;
  }

  if ( i->isTrue( )  ) return t;
  if ( i->isFalse( ) ) return e;
  if ( t == e )        return t;

  has_ites = true;

  return cons( id_to_enode[ ENODE_ID_ITE ], cons( i, cons( t, cons( e ) ) ) );
}

Enode * Egraph::mkXor( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  if (!args || args->getArity() != 2) {
      return nullptr;
  }

  Enode * first  = args->getCar( );
  Enode * second = args->getCdr( )->getCar( );
  assert( first->hasSortBool( ) );
  assert( second->hasSortBool( ) );
  if (!first->hasSortBool() || second->hasSortBool()) {
      return nullptr;
  }

  if ( first ->isFalse( ) )               return second;
  if ( first ->isTrue ( ) )               return mkNot( cons( second ) );
  if ( second->isFalse( ) )               return first;
  if ( second->isTrue ( ) )               return mkNot( cons( first ) );
  if ( first == second )                  return mkFalse( );
  if ( first == mkNot( cons( second ) ) ) return mkTrue ( );

  return cons( id_to_enode[ ENODE_ID_XOR ], args );
}

Enode * Egraph::mkImplies( Enode * args )
{
  assert( args );
  if (!args) {
      return nullptr;
  }

  Enode * first  = args->getCar( );
  Enode * second = args->getCdr( )->getCar( );
  Enode * not_first = mkNot( cons( first ) );

  if ( first ->isFalse( ) ) return mkTrue( );
  if ( second->isTrue ( ) ) return mkTrue( );
  if ( first ->isTrue ( ) ) return second;
  if ( second->isFalse( ) ) return not_first;

  return mkOr( cons( not_first
             , cons( second ) ) );
}

Enode * Egraph::mkDistinct( Enode * args )
{
  assert( args );
  if (!args) {
      return nullptr;
  }
  Enode * res = nullptr;
  //
  // Replace distinction with negated equality when it has only 2 args
  //
  if ( args->getArity( ) == 2 )
  {
    Enode * x = args->getCar( );
    Enode * y = args->getCdr( )->getCar( );
    res = mkNot( cons( mkEq( cons( x, cons( y ) ) ) ) );
  }
  else
  {
    res = cons( id_to_enode[ ENODE_ID_DISTINCT ], args );

    // The thing is that this distinction might have been
    // already processed. So if the index is -1 we are sure
    // it is new
    if ( !config.incremental
      && res->getDistIndex( ) == -1 )
    {
      size_t index = index_to_dist.size( );

      if ( index > sizeof( dist_t ) * 8 )
        opensmt_error2( "max number of distinctions supported is " ,sizeof( dist_t ) * 8 );

      res->setDistIndex( index );
      // Store the correspondence
      index_to_dist.push_back( res );
      // Check invariant
      assert( index_to_dist[ index ] == res );
    }
  }

  assert( res );
  return res;
}
//
// Packs assertions and formula and return it into a single enode
//
Enode * Egraph::getUncheckedAssertions( bool const clear )
{
  if ( assertions.empty( ) )
    return mkTrue( );

  // Pack the formula and the assertions
  // into an AND statement, and return it
  if ( top != nullptr )
    assertions.push_back( top );

  Enode * args = cons( assertions );

  // Clear assertions for incremental solving
  if (clear) {
      assertions.clear( );
  }

  return mkAnd( args );
}

#ifdef PRODUCE_PROOF
Enode * Egraph::getNextAssertion( )
{
  if ( assertions.empty( ) )
    return nullptr;

  Enode * ret = assertions.front( );
  assertions.pop_front( );
  return ret;
}
#endif

//
// Computes the polarities for theory atoms and
// set the decision polarity
// Nodes with both polarities gets a random polarity
//
void Egraph::computePolarities( Enode * formula )
{
  // Polarity will be all true or all false or all random
  if ( config.sat_polarity_mode <= 2 )
    return;

  assert( config.logic != UNDEF );

  vector< Enode * > unprocessed_enodes;
  initDup1( );

  unprocessed_enodes  .push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    unprocessed_enodes  .pop_back( );
    //
    // Skip if the node has already been processed before
    //
    if ( isDup1( enode ) )
      continue;

    //
    // Process children
    //
    if ( enode->isBooleanOperator( ) )
    {
      Enode * arg_list;
      for ( arg_list = enode->getCdr( )
          ; !arg_list->isEnil( )
          ; arg_list = arg_list->getCdr( ) )
      {
        Enode * arg = arg_list->getCar( );
        assert( arg->isTerm( ) );
        unprocessed_enodes  .push_back( arg );
      }

      storeDup1( enode );
      continue;
    }

    assert( enode->isAtom( ) );
    //
    // Skip Boolean atoms
    //
    if ( !enode->isTAtom( ) )
      continue;
    //
    // Here set polarity
    //
    if ( config.logic == QF_UF )
    {
      if ( enode->isEq( ) )
      {
        Enode * lhs = enode->get1st( );
        Enode * rhs = enode->get2nd( );
        //
        // Equality between the same f
        //
        if ( lhs->getCar( ) == rhs->getCar( ) )
          enode->setDecPolarity( l_False );
        else
          enode->setDecPolarity( l_True );
      }
      else if ( enode->isUp( ) )
        enode->setDecPolarity( l_False );
    }
    //
    // This function assumes polynomes to be canonized
    // in the form a_1 * x_1 + ... + a_n * x_n <= c
    // including difference logic constraints
    //
    else if ( config.logic == QF_IDL
              || config.logic == QF_RDL
              || config.logic == QF_LRA
              || config.logic == QF_LIA
              || config.logic == QF_UFIDL
              || config.logic == QF_UFLRA
              || config.logic == QF_NRA     /* added for dReal */
              || config.logic == QF_NRA_ODE /* added for dReal */
              )
    {
      if ( enode->isLeq( ) )
      {
        assert( enode->get1st( )->isConstant( )
             || enode->get2nd( )->isConstant( ) );
        if ( enode->get1st( )->isConstant( ) )
        {
          const double weight = enode->get1st( )->getValue( );
          enode->setDecPolarity( weight > 0 ? l_True : l_False );
        }
        if ( enode->get2nd( )->isConstant( ) )
        {
          const double weight = enode->get2nd( )->getValue( );
          enode->setDecPolarity( weight < 0 ? l_True : l_False );
        }
      }
    }

    storeDup1( enode );
  }

  // Done with cache
  doneDup1( );
}

void Egraph::addAssertion( Enode * e )
{
  assert( e );

  if ( config.incremental )
  {
    //
    // Canonize arithmetic and split equalities
    //
    if ( config.logic == QF_IDL
      || config.logic == QF_RDL
      || config.logic == QF_LRA
      || config.logic == QF_LIA
      || config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    {
      if ( config.sat_lazy_dtc != 0 )
        e = canonizeDTC( e, true );
      else
        e = canonize( e, true );
    }
    //
    // Booleanize and normalize bitvectors
    //
    else if ( config.logic == QF_BV )
    {
      BVBooleanize booleanizer( *this, config );
      BVNormalize normalizer  ( *this, config );
      e = booleanizer.doit( e );
      e = normalizer .doit( e );
    }
    else
    {
      // warning( "assumption not canonized/normalized" );
    }
  }

  //slacking operations
  if ( (config.logic==QF_NRA||config.logic==QF_NRA_ODE) && config.nra_slack_level != 0) {
    // build slacks
    //cerr<<"working on:"<<e<<endl;
    vector<Enode *> tmp;
    assertions.push_back(slackFormula(e, config.nra_slack_level, tmp));
    for (auto l : tmp) {
      assertions.push_back(l);
    }
  } else {
    assertions.push_back( e );
  }

#ifdef PRODUCE_PROOF
  // Tag formula for interpolation
  // (might not be necessary, but we do it)
  assert( formulae_to_tag.empty( ) );
  formulae_to_tag.push_back( assertions.back( ) );
  addIFormula( );
  formulae_to_tag.clear( );
#endif

  assert( !assertions.empty( ) );
}

unsigned Egraph::newSlackVar() {
    Snode * s = sort_store.mkReal();
    unsigned index = svars.size();
    string name("slack_var_");
    name += std::to_string(index);
    newSymbol(name.c_str(), s, true);
    Enode * var = mkVar(name.c_str());
    svars.push_back(var);
    return index;
}

Enode * Egraph::mkSlack(Enode * e, vector<unsigned> * vs) {
    // find if already stored. if not, introduce a new var and push
    // them to the tables
    auto it = find(originals.begin(), originals.end(), e);
    unsigned ind;  // index of the slack var
    if (it != originals.end()) {
        ind = it - originals.begin();
    } else {
        originals.push_back(e);
        ind = newSlackVar();  // Enode of the new var is pushed inside the function
    }
    // push index to the current vector of slack vars
    vs->push_back(ind);
    // return the slack var only
    return svars[ind];
}

Enode * Egraph::slackTerm(Enode * e, unsigned level, vector<unsigned> * vs) {
    if (e->isConstant() || e->isNumb() || e->isVar()) {
      return e;
    } else if (e->isTerm()) {
      assert(e->getArity() >= 1);
      enodeid_t id = e->getCar()->getId();
      Enode * ret;
      Enode * tmp = e;
      switch (id) {
        case ENODE_ID_PLUS:
          ret = slackTerm(tmp->get1st(), level, vs);
          tmp = tmp->getCdr()->getCdr();
          while (!tmp->isEnil()) {
            ret = mkPlus(ret,slackTerm(tmp->getCar(), level, vs));
            tmp = tmp->getCdr();
          }
          return ret;
        case ENODE_ID_MINUS:
          //only binary minus is allowed in opensmt
          return mkMinus(slackTerm(tmp->get1st(),level,vs),slackTerm(tmp->get2nd(),level,vs));
        case ENODE_ID_UMINUS:
          assert(tmp->getArity() == 1);
          ret = slackTerm(tmp->get1st(), level, vs);
          return mkUminus(cons(ret));
        default:
          if (level >= 2) {  // level 1 only handles top layer
            slackTerm(tmp->get1st(), level, vs);
            tmp = tmp->getCdr()->getCdr();
            while (!tmp->isEnil()) {
              slackTerm(tmp->getCar(), level, vs);
              tmp = tmp->getCdr();
            }
          }
          return mkSlack(e, vs);
      }
    } else {
        throw runtime_error("Slack operation error.");
    }
}

Enode * Egraph::slackAtom(Enode * e, unsigned level, vector<Enode *> & lits) {
  if (e->isIntegral()||e->isForall()||e->isForallT()||e->isTrue()||e->isFalse()) {
    // no slacking for fancy atoms
    return e;
  }
  if (e->getArity() != 2) {
    assert(e->getArity()==0);
    return e;
  }
  // prepare a vector that'll hold indices of all slack variables involved
  vector<unsigned> * current_svars = new vector<unsigned>;
  // break into three parts.
  Enode * left = e -> get1st();
  Enode * right = e -> get2nd();
  Enode * head = e -> getCar();
  // do slacking on both sides
  Enode * linear_left = slackTerm(left, level, current_svars);
  Enode * linear_right = slackTerm(right, level, current_svars);
  // prepare the vector of enode that'll have all the constraints corresponding to e
  vector<Enode *> * slack_result = new vector<Enode *>;
  //after-slack result
  Enode * ret;
  // link the current e with its replacements
  if (!current_svars->empty()) {
    //assemble the result
    ret = cons(head, cons(linear_left, cons(linear_right)));
    // next, prepare all the additional constraints
    for (auto sv : *current_svars) {
      Enode * sctr = mkEq(cons(svars[sv], cons(originals[sv])));
      slack_result->push_back(sctr);
    }
  } else {
    ret = e;
  }
  // if we still want the original term -- usually you don't, unless
  // you set level to 3.
  if (!current_svars->empty() && level >= 3)
    slack_result->push_back(e);
  // add the mapping from e to the assembled vector
  enode_to_sctrs.emplace(e, slack_result);
  // then add all the new constraints for the slack variables to lits
  for (auto l : *slack_result) {
    lits.push_back(l);
  }
  // no longer need the indices
  delete current_svars;
  return ret;
}

Enode * Egraph::slackFormula(Enode * e, unsigned level, vector<Enode *> & lits) {
  if (e->isAtom()) {
    return slackAtom(e,level,lits);
  } else if (e->isBooleanOperator()){
    assert(e->getArity()>=1);
    enodeid_t id = e->getCar()->getId();
    Enode * tmp = e;
    Enode * ret;
    switch (id) {
      case ENODE_ID_NOT:
        return mkNot(cons(slackFormula(e->getCdr()->getCar(),level,lits)));
      case ENODE_ID_AND:
        ret = slackFormula(e->get1st(),level,lits);
        tmp = tmp -> getCdr()->getCdr();
        while (!tmp->isEnil()) {
          ret = mkAnd(cons(ret,cons(slackFormula(tmp->getCar(),level,lits))));
          tmp = tmp->getCdr();
        }
        return ret;
      case ENODE_ID_OR:
        ret = slackFormula(e->get1st(),level,lits);
        tmp = tmp->getCdr()->getCdr();
        while (!tmp->isEnil()) {
          ret = mkOr(cons(ret,cons(slackFormula(tmp->getCar(),level,lits))));
          tmp = tmp->getCdr();
        }
        return ret;
      case ENODE_ID_IMPLIES:
        ret = slackFormula(e->get1st(),level,lits);
        tmp = tmp->getCdr()->getCdr();
        while (!tmp->isEnil()) {
          ret = mkImplies(cons(ret,cons(slackFormula(tmp->getCar(),level,lits))));
          tmp = tmp->getCdr();
        }
        return ret;
      case ENODE_ID_EQ:
        return mkIff(cons(slackFormula(e->get1st(),level,lits),
                      cons(slackFormula(e->get2nd(),level,lits))));
      default:
        cerr<<"Can't handle: "<<e<<endl;
        throw runtime_error("Slack operation not supported for ITE or XOR.");
    }
  } else {
    cerr<<"Can't handle: "<<e<<endl;
    throw runtime_error("Error at slackFormula");
  }
}

Enode * Egraph::canonize( Enode * formula, bool split_eqs )
{
  assert( config.logic != QF_UFIDL || config.sat_lazy_dtc == 0 );
  assert( config.logic != QF_UFLRA || config.sat_lazy_dtc == 0 );

  vector< Enode * > unprocessed_enodes;
  initDupMap1( );

  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( valDupMap1( enode ) != nullptr )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
        ; arg_list != enil
        ; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( valDupMap1( arg ) == nullptr )
      {
        unprocessed_enodes.push_back( arg );
        unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );
    Enode * result = nullptr;
    //
    // Replace arithmetic atoms with canonized version
    //
    if (  enode->isTAtom( )
      && !enode->isUp( ) )
    {
      LAExpression a( enode );
      result = a.toEnode( *this );
#ifdef PRODUCE_PROOF
      const uint64_t partitions = getIPartitions( enode );
      assert( partitions != 0 );
      setIPartitions( result, partitions );
#endif

      if ( split_eqs && result->isEq( ) )
      {
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
          opensmt_error2( "can't compute interpolant for equalities at the moment ", enode );
#endif
        LAExpression aa( enode );
        Enode * e = aa.toEnode( *this );
#ifdef PRODUCE_PROOF
        assert( partitions != 0 );
        setIPartitions( e, partitions );
#endif
        Enode * lhs = e->get1st( );
        Enode * rhs = e->get2nd( );
        Enode * leq = mkLeq( cons( lhs, cons( rhs ) ) );
        LAExpression b( leq );
        leq = b.toEnode( *this );
#ifdef PRODUCE_PROOF
        assert( partitions != 0 );
        setIPartitions( leq, partitions );
#endif
        Enode * geq = mkGeq( cons( lhs, cons( rhs ) ) );
        LAExpression c( geq );
        geq = c.toEnode( *this );
#ifdef PRODUCE_PROOF
        assert( partitions != 0 );
        setIPartitions( geq, partitions );
#endif
        result = mkAnd( cons( leq, cons( geq ) ) );
      }
    }
    //
    // If nothing have been done copy and simplify
    //
    if ( result == nullptr )
      result = copyEnodeEtypeTermWithCache( enode );

    assert( valDupMap1( enode ) == nullptr );
    storeDupMap1( enode, result );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
    {
      // Setting partitions for result
      setIPartitions( result, getIPartitions( enode ) );
      // Setting partitions for negation as well occ if atom
      if ( result->hasSortBool( ) )
      {
        setIPartitions( mkNot( cons( result ) )
                      , getIPartitions( enode ) );
      }
    }
#endif
  }

  Enode * new_formula = valDupMap1( formula );
  assert( new_formula );
  doneDupMap1( );

  return new_formula;
}

#ifndef SMTCOMP
//
// Functions for evaluating an expression
//
void Egraph::evaluateTerm( Enode * e, double& v )
{
  assert( model_computed );
  assert( e->hasSortReal( ) );
  // Recursively compute value
  evaluateTermRec( e, v );
}

void Egraph::evaluateTermRec( Enode * e, double&  v )
{
  assert( false );
  //
  // Base cases
  //
  if ( e->isConstant( ) )
  {
    v = e->getValue( );
  }
  else if ( e->isVar( ) )
  {
    if ( !e->hasValue( ) )
      opensmt_error2( "cannot determine value for ", e );

    v = e->getValue( );
  }
  else
  {
    double a, b = 0;
    if ( e->isPlus( ) )
    {
      Enode * l;
      for ( l = e->getCdr( )
          ; !l->isEnil( )
          ; l = l->getCdr( ) )
      {
        evaluateTermRec( l->getCar( ), a );
        b += a;
      }
      v = b;
    }
    else if ( e->isTimes( ) )
    {
      b = 1;
      Enode * l;
      for ( l = e->getCdr( )
          ; !l->isEnil( )
          ; l = l->getCdr( ) )
      {
        evaluateTermRec( l->getCar( ), a );
        b *= a;
      }
      v = b;
    }
    else if ( e->isUminus( ) )
    {
      evaluateTermRec( e->get1st( ), a );
      v = -a;
    }
    else if ( e->isMinus( ) )
    {
      evaluateTermRec( e->get1st( ), a );
      evaluateTermRec( e->get2nd( ), b );
      v = a - b;
    }
    else
    {
      opensmt_error2( "operator not handled (yet) ", e->getCar( ) );
    }
  }
}
#endif

#ifdef PRODUCE_PROOF
void Egraph::addIFormula( )
{
  tagIFormulae( SETBIT( iformula ) );
  iformula ++;
  if ( iformula == 63 )
    opensmt_error( "currently only up to 62 partitions are allowed" );
}

void Egraph::tagIFormulae( const uint64_t partitions )
{
  assert( partitions != 0 );
  tagIFormulae( partitions, formulae_to_tag );
}

void Egraph::tagIFormulae( const uint64_t partitions
                         , vector< Enode * > & f_to_tag )
{
  initDup1( );
  while( !f_to_tag.empty( ) )
  {
    Enode * enode = f_to_tag.back( );

    if ( isDup1( enode ) )
    {
      f_to_tag.pop_back( );
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
        ; !arg_list->isEnil( )
        ; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !isDup1( arg ) )
      {
        f_to_tag.push_back( arg );
        unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    f_to_tag.pop_back( );
    // tagIFormula( enode, partitions );
    setIPartitions( enode, partitions );
    storeDup1( enode );
  }

  doneDup1( );
}

void
Egraph::tagIFormula( Enode * e, uint64_t partitions )
{
  vector< Enode * > f_to_tag;
  f_to_tag.push_back( e );
  tagIFormulae( partitions, f_to_tag );
  /*
  if ( e->getId( ) >= static_cast< int >( id_to_iformula.size( ) ) )
    id_to_iformula.resize( e->getId( ) + 1, 0 );
  // Store info about partition
  id_to_iformula[ e->getId( ) ] |= partitions;
  */
}
#endif

Enode * Egraph::mkLet( Enode * t )
{
  initDupMap1( );
  vector< Enode * > unprocessed_enodes;

  unprocessed_enodes.push_back( t );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( valDupMap1( enode ) != nullptr )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
        ; arg_list != enil
        ; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( valDupMap1( arg ) == nullptr )
      {
        unprocessed_enodes.push_back( arg );
        unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );
    Enode * result = nullptr;
    //
    // Replace with corresponding definition
    //
    if ( enode->isDef( ) )
      result = enode->getDef( );
    else
      result = copyEnodeEtypeTermWithCache( enode );

    assert( valDupMap1( enode ) == nullptr );
    storeDupMap1( enode, result );
  }

  Enode * new_t = valDupMap1( t );
  assert( new_t );
  doneDupMap1( );

  return new_t;
}

//=================================================================================================
// Debugging Routines

#ifdef STATISTICS
void Egraph::printMemStats( ostream & os )
{
  unsigned total = 0;

  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];
    assert( e != nullptr );
    total += e->sizeInMem( );
  }

  os << "# " << endl;
  os << "# General Statistics" << endl;
  os << "#" << endl;
  os << "# Total enodes..........: " << id_to_enode.size( ) << endl;
  os << "# Enode size in memory..: " << ( total / 1048576.0 ) << " MB" << endl;
  os << "# Avg size per enode....: " << ( total / id_to_enode.size( ) ) << " B" << endl;
  os << "#" << endl;
  os << "# Splay Tree Statistics" << endl;
  store.printStatistics( os );
  os << "#" << endl;
  os << "# Signature Table Statistics" << endl;
  enodeid_t maximal;
  sig_tab.printStatistics( os, &maximal );
  os << "# Maximal node..........: " << id_to_enode[ maximal ] << endl;
  os << "#" << endl;
  os << "# Supporting data structures" << endl;
  os << "#" << endl;
  os << "# id_to_enode........: " << id_to_enode.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# duplicates1........: " << duplicates1.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# duplicates2........: " << duplicates2.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# dup_map1...........: " << dup_map1.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# dup_set1...........: " << dup_set1.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# dup_map2...........: " << dup_map2.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# dup_set2...........: " << dup_set2.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# id_to_belong_mask..: " << id_to_belong_mask.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# id_to_fan_in.......: " << id_to_fan_in.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# index_to_dist......: " << index_to_dist.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# cache..............: " << cache.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# ext_store..........: " << ext_store.size( ) * sizeof( pair< pair< int, int >, Enode * > ) / 1048576.0 << " MB" << endl;
  os << "# se_store...........: " << se_store.size( ) * sizeof( pair< pair< int, int >, Enode * > ) / 1048576.0 << " MB" << endl;
  os << "# id_to_inc_edges....: " << id_to_inc_edges.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "#" << endl;

}

void Egraph::printEnodeList( ostream & os )
{
  os << "# =================================================" << endl;
  os << "# Enode Bank Information" << endl;
  os << "# " << endl;
  os << "# -----+-------------------------------------------" << endl;
  os << "# Enode Symbol List" << endl;
  os << "# -----+-------------------------------------------" << endl;
  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];

    if( e->getId( ) <= ENODE_ID_LAST )
      continue;

    if( e->isSymb( ) || e->isNumb( ) || e->isDef( ) )
    {
      // Print index formatted
      ostringstream tmp; tmp << i;
      os << "# ";
      for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
      os << tmp.str( ) << " | ";

      e->print( os );
      os << endl;
    }
  }
  os << "# -----+-------------------------------------------" << endl;
  os << "# Enode Term List" << endl;
  os << "# -----+-------------------------------------------" << endl;
  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];
    if( e->isTerm( ) )
    {
      // Print index formatted
      ostringstream tmp; tmp << i;
      os << "# ";
      for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
      os << tmp.str( ) << " | ";

      e->print( os );
      os << endl;
    }
  }
  os << "# -----+-------------------------------------------" << endl;
  os << "# Enode List List" << endl;
  os << "# -----+-------------------------------------------" << endl;
  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];
    if( e->isList( ) )
    {
      // Print index formatted
      ostringstream tmp; tmp << i;
      os << "# ";
      for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
      os << tmp.str( ) << " | ";

      e->print( os );
      os << endl;
    }
  }
}
#endif

void Egraph::dumpToFile( const char * filename, Enode * formula )
{
  ofstream dump_out ( filename );
  dumpHeaderToFile  ( dump_out );
  dump_out << endl;
  dumpFormulaToFile ( dump_out, formula );
  dump_out << "(check-sat)" << endl;
  dump_out << "(exit)" << endl;
  dump_out.close( );
  cerr << "[Dumped " << filename << "]" << endl;
}

void Egraph::dumpHeaderToFile( ostream & dump_out )
{
  dump_out << "(set-logic " << logicStr( config.logic ) << ")" << endl;
  dump_out << "(set-info :source |" << endl
           << "Dumped with "
           << PACKAGE_STRING
           << " on "
           << __DATE__ << "." << endl
           << "For info contact Roberto Bruttomesso <roberto.bruttomesso@gmail.com>" << endl
           << "|)"
           << endl;
  dump_out << "(set-info :smt-lib-version 2.0)" << endl;
  // Dump sorts
  sort_store.dumpSortsToFile( dump_out );
  // Dump function declarations
  for ( map< string, Enode * >::iterator it = name_to_symbol.begin( )
      ; it != name_to_symbol.end( )
      ; it ++ )
  {
    Enode * s = it->second;
    // Skip predefined symbols
    if ( s->getId( ) <= ENODE_ID_LAST )
      continue;
    dump_out << "(declare-fun " << s << " " << s->getSort( ) << ")" << endl;
  }
}

void Egraph::dumpFormulaToFile( ostream & dump_out, Enode * formula, bool negate )
{
  vector< Enode * > unprocessed_enodes;
  map< enodeid_t, string > enode_to_def;

  unprocessed_enodes.push_back( formula );
  // Open assert and let
  dump_out << "(assert" << endl;
  dump_out << "(let (";
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( enode_to_def.find( enode->getId( ) ) != enode_to_def.end( ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
        ; !arg_list->isEnil( )
        ; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( enode_to_def.find( arg->getId( ) ) == enode_to_def.end( )
        && arg->isBooleanOperator( ) )
      {
        unprocessed_enodes.push_back( arg );
        unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    char buf[ 32 ];
    sprintf( buf, "?def%d", enode->getId( ) );

    // Open binding
    dump_out << "(" << buf << " ";

    if ( enode->getArity( ) > 0 )
      dump_out << "(";
    dump_out << enode->getCar( );
    for ( Enode * list = enode->getCdr( )
        ; !list->isEnil( )
        ; list = list->getCdr( ) )
    {
      Enode * arg = list->getCar( );
      if ( arg->isBooleanOperator( ) )
        dump_out << " " << enode_to_def[ arg->getId( ) ];
      else
        dump_out << " " << arg;
    }
    if ( enode->getArity( ) > 0 ) dump_out << ")";

    // Closes binding
    dump_out << ")" << endl;

    assert( enode_to_def.find( enode->getId( ) ) == enode_to_def.end( ) );
    enode_to_def[ enode->getId( ) ] = buf;
  }

  // Closes binding list
  dump_out << ")" << endl;
  // Formula
  if ( negate ) dump_out << "(not ";
  dump_out << enode_to_def[ formula->getId( ) ] << endl;
  if ( negate ) dump_out << ")";
  // Close let
  dump_out << ")";
  // Closes assert
  dump_out << ")" << endl;
}

Enode * Egraph::mkForallT             ( Enode * mode, Enode * lb, Enode * rb, Enode * args)
{
  assert( mode );
  assert( lb );
  assert( rb );
  assert( args );
  assert( args->getArity( ) == 1 );
  Enode * res = cons( id_to_enode[ ENODE_ID_FORALLT ], cons(mode, cons(lb, cons(rb, args ))));
  assert( res );
  return res;
}

Enode * Egraph::mkIntegral             ( Enode * time_0, Enode * time_t, Enode * vec_0, Enode * vec_t, const char * flowname )
{
  assert( time_0 );
  assert( time_t );
  assert( vec_0 );
  assert( vec_t );
  assert( flowname );
  // elist = vec_0_n, vec_t_n, vec_0_{n-1}, vec_t_{n-1}, ..., vec_0_0, vec_t_0
  Enode * elist = const_cast< Enode * >( enil );
  vector<Enode*> v0s;
  vector<Enode*> vts;

  while(!vec_0->isEnil() && !vec_t->isEnil()) {
      v0s.push_back(vec_0->getCar());
      vts.push_back(vec_t->getCar());
      vec_0 = vec_0->getCdr();
      vec_t = vec_t->getCdr();
  }
  reverse(v0s.begin(), v0s.end());
  reverse(vts.begin(), vts.end());
  for (unsigned int i = 0; i < v0s.size(); i++) {
      elist = cons(v0s[i], cons(vts[i], elist));
  }
  string flow_str(flowname);
  unsigned flow_id = std::stoi(flow_str.substr(flow_str.find_last_of('_') + 1)); /* flow_xxx => xxx */
  Enode * res = cons(id_to_enode[ ENODE_ID_INTEGRAL ], cons(mkNum(flow_id), cons(time_0, cons(time_t, elist))));
  assert( res );
  return res;
}

Enode * Egraph::mkForall ( vector<pair<string, Snode *>> const & sorted_var_list, Enode * e) {
    /// TODO(soonhok): For now, we ignore sorts in the sorted_var_list
    /// and only collect the names of variables, relying on the sorts
    /// used to define those quantified variables in `declare-fun`.
    /// It should be fixed while it's unclear for me how to do it.
    ///
    /// This is the case for 'mkExists' as well.
    Enode * elist = const_cast< Enode * >( enil );
    for (auto it = sorted_var_list.crbegin(); it != sorted_var_list.crend(); ++it) {
        pair<string, Snode *> p = *it;
        string const & name = p.first;
        elist = cons(mkVar(name.c_str()), elist);
    }
    Enode * res = cons(id_to_enode[ ENODE_ID_FORALL ], cons(e, elist));
    assert (res);
    return res;
}
Enode * Egraph::mkExists ( vector<pair<string, Snode *>> const & sorted_var_list, Enode * e) {
    Enode * elist = const_cast< Enode * >( enil );
    for (auto it = sorted_var_list.crbegin(); it != sorted_var_list.crend(); ++it) {
        pair<string, Snode *> p = *it;
        string const & name = p.first;
        elist = cons(mkVar(name.c_str()), elist);
    }
    Enode * res = cons(id_to_enode[ ENODE_ID_EXISTS ], cons(e, elist));
    assert (res);
    return res;
}

Enode * Egraph::mkDeriv(Enode * e, Enode * v) {
  assert(v->isVar());
  Enode * zero = mkNum("0");
  Enode * one = mkNum("1");
  if (e == v) {
    return one;
  }
  if (e->isVar()) {
    if (e == v) {
      return one;
    } else {
      // Variable is found in var_map
      return zero;
    }
  } else if (e->isConstant()) {
    return zero;
  } else if (e->isSymb()) {
    throw runtime_error("mkDeriv: Symb");
  } else if (e->isNumb()) {
    return zero;
  } else if (e->isTerm()) {
    assert(e->getArity() >= 1);
    enodeid_t id = e->getCar()->getId();
    //double ret = 0.0;
    Enode * ret;
    Enode * tmp = e;
    switch (id) {
    case ENODE_ID_PLUS:
      ret = mkDeriv(tmp->get1st(), v);
      tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
      while (!tmp->isEnil()) {
        ret = mkPlus(ret, mkDeriv(tmp->getCar(), v));
        tmp = tmp->getCdr();
      }
      return ret;
    case ENODE_ID_MINUS:
      ret = mkDeriv(tmp->get1st(), v);
      tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
      while (!tmp->isEnil()) {
        ret = mkMinus(ret, mkDeriv(tmp->getCar(), v));
        tmp = tmp->getCdr();
      }
      return ret;
    case ENODE_ID_UMINUS:
      ret = mkDeriv(tmp->get1st(), v);
      assert(tmp->getArity() == 1);
      return mkUminus(cons(ret));
    case ENODE_ID_TIMES: {
      // (f * g)' = f' * g + f * g'
      Enode * f = tmp->get1st();
      Enode * f_p = mkDeriv(f, v);
      if (tmp->getArity() == 2){
        Enode * g = tmp->get2nd();
        Enode * g_p = mkDeriv(g, v);
        return mkPlus(mkTimes(f,g_p),mkTimes(g,f_p));
      }
      else if (tmp->getArity() > 2){
        //reduce the rest of the list to a standalone product
        Enode * g = mkTimes(tmp->getCdr()->getCdr()->getCar(),tmp->getCdr()->getCdr()->getCdr());
        Enode * g_p = mkDeriv(g, v);
        return mkPlus(mkTimes(f,g_p),mkTimes(g,f_p));
      }
    }
    case ENODE_ID_DIV: {
      // (f / g)' = (f' * g - f * g') / g^2
      Enode * f = tmp->get1st();
      Enode * f_p = mkDeriv(f, v);
      if (tmp->getArity() == 2){
        Enode * g = tmp->get2nd();
        Enode * g_p = mkDeriv(g, v);
        assert(g!=zero);
        return mkDiv(mkMinus(mkTimes(f,g_p),mkTimes(g,f_p)),mkTimes(g, g));
      }
      else if (tmp->getArity() > 2){
        //reduce the rest of the list to a standalone product
        Enode * g = mkDiv(tmp->getCdr()->getCdr()->getCar(),tmp->getCdr()->getCdr()->getCdr());
        Enode * g_p = mkDeriv(g, v);
        assert(g!=zero);
        return mkDiv(mkMinus(mkTimes(f,g_p),mkTimes(g,f_p)),mkTimes(g, g));
      }
    }
    case ENODE_ID_ACOS: {
      // (acos f)' = -(1 / sqrt(1 - f^2)) f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkUminus(cons(mkDiv(one,mkSqrt(cons(mkMinus(one, mkTimes(f,f))))))),f_p);
    }
    case ENODE_ID_ASIN: {
      // (asin f)' = (1 / sqrt(1 - f^2)) f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkDiv(one,mkSqrt(cons(mkMinus(one, mkTimes(f,f))))),f_p);
    }
    case ENODE_ID_ATAN: {
      // (atan f)' = (1 / (1 + f^2)) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkDiv(one, mkPlus(one, mkTimes(f,f))),f_p);
    }
    case ENODE_ID_ATAN2: {
      // atan2(x,y)' = -y / (x^2 + y^2) dx + x / (x^2 + y^2) dy
      //             = (-y dx + x dy) / (x^2 + y^2)
      assert(e->getArity() == 2);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      Enode * g = e->get2nd();
      Enode * g_p = mkDeriv(g,v);
      return mkDiv(mkPlus(mkTimes(mkUminus(cons(g)), f_p),mkTimes(f, g_p)),
                   mkPlus(mkTimes(f,f),mkTimes(g,g)));
    }
    case ENODE_ID_MIN:
      assert(e->getArity() == 2);
      throw runtime_error("mkDeriv: no support for min");
    case ENODE_ID_MAX:
      assert(e->getArity() == 2);
      throw runtime_error("mkDeriv: no support for max");
    case ENODE_ID_MATAN:
      assert(e->getArity() == 1);
      throw runtime_error("mkDeriv: no support for matan");
    case ENODE_ID_SAFESQRT:
      assert(e->getArity() == 1);
      throw runtime_error("mkDeriv: no support for safesqrt");
    case ENODE_ID_SQRT: {
      // (sqrt(f))' = 1/2 * 1/(sqrt(f)) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkDiv(one,mkTimes(mkNum("2"),mkSqrt(cons(f)))), f_p);
    }
    case ENODE_ID_EXP: {
      // (exp f)' = (exp f) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkExp(cons(f)),f_p);

    }
    case ENODE_ID_LOG: {
      // (log f)' = f' / f
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkDiv(f_p,f);
    }
    case ENODE_ID_POW: {
      // (f^g)' = f^g (f' * g / f + g' * ln g)
      assert(e->getArity() == 2);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      Enode * g = e->get2nd();
      if (g->isConstant()) {
        return mkTimes(mkTimes(g,mkPow(cons(f,cons(mkMinus(g,one))))),f_p);
      }
      else {
        Enode * g_p = mkDeriv(g,v);
        return mkTimes(mkPow(cons(f, cons(g))),mkDiv(mkTimes(f_p,g),mkPlus(f,mkTimes(g_p, mkLog(cons(g))))));
      }
    }
    case ENODE_ID_ABS: {
      assert(e->getArity() == 1);
      throw runtime_error("mkDeriv: no support for safesqrt");
    }
    case ENODE_ID_SIN: {
      // (sin f)' = (cos f) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkCos(cons(f)), f_p);
    }
    case ENODE_ID_COS: {
      // (cos f)' = - (sin f) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkUminus(cons(mkTimes(mkSin(cons(f)), f_p)));
    }
    case ENODE_ID_TAN: {
      // (tan f)' = (1 + tan^2 f) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkPlus(one, mkTimes(mkTan(cons(f)), mkTan(cons(f)))),f_p);
    }
    case ENODE_ID_SINH: {
      // (sinh f)' = (e^f + e^(-f))/2 * f'
      //           = cosh(f) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkCosh(cons(f)), f_p);
    }
    case ENODE_ID_COSH: {
      // (cosh f)' = (e^f - e^(-f))/2 * f'
      //           = sinh(f) * f'
      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkSinh(cons(f)),f_p);
    }
    case ENODE_ID_TANH: {
      // (tanh f)' = (sech^2 f) * f'
      //           = (1 - tanh(f) ^ 2) * f'

      assert(e->getArity() == 1);
      Enode * f = e->get1st();
      Enode * f_p = mkDeriv(f, v);
      return mkTimes(mkMinus(one,mkTimes(mkTanh(cons(f)),mkTanh(cons(f)))), f_p);
    }
    default:
      throw runtime_error("mkDeriv: Unknown Term");
    }
  } else if (e->isList()) {
    throw runtime_error("mkDeriv: List");
  } else if (e->isDef()) {
    throw runtime_error("mkDeriv: Def");
  } else if (e->isEnil()) {
    throw runtime_error("mkDeriv: Nil");
  } else {
    throw runtime_error("mkDeriv: unknown case");
  }
  throw runtime_error("Not implemented yet: mkDeriv");
}
