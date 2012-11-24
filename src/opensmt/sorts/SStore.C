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

#include "SStore.h"

void SStore::initializeStore( )
{
  //
  // Allocates SMTLIB predefined symbols
  //
  newSymbol( "Dot"   );  assert( SNODE_ID_DOT   == id_to_snode.size( ) - 1 );
  newSymbol( "Bool"  );  assert( SNODE_ID_BOOL  == id_to_snode.size( ) - 1 );
  newSymbol( "Real"  );  assert( SNODE_ID_REAL  == id_to_snode.size( ) - 1 );
  newSymbol( "Int"   );  assert( SNODE_ID_INT   == id_to_snode.size( ) - 1 );
  newSymbol( "Array" );  assert( SNODE_ID_ARRAY == id_to_snode.size( ) - 1 );
  newSymbol( "Elem"  );  assert( SNODE_ID_ELEM  == id_to_snode.size( ) - 1 );
  newSymbol( "Index" );  assert( SNODE_ID_INDEX == id_to_snode.size( ) - 1 );
  newSymbol( "Cost" );   assert( SNODE_ID_COST  == id_to_snode.size( ) - 1 );
}

Snode * SStore::newSymbol( const char * name, const bool para )
{
  Snode * s = lookupSymbol( name );
  // Return old symbol if there
  if ( s != NULL )
  {
    if ( para )
      return s;
    else
      opensmt_error2( "sort symbol already declared ", name );
  }
  // Create new symbol/parameter
  Snode * new_snode = new Snode( id_to_snode.size( ), name, para );
  // Insert new symbol
  insertSymbol( new_snode );	                   
  assert( lookupSymbol( name ) == new_snode );     
  return new_snode;
}

Snode * SStore::newPara( const char * name )
{
  return newSymbol( name, true );
}

Snode * SStore::mkVar( const char * name )
{
  Snode * s = lookupSymbol( name );
  // Not a variable, is it a define ?
  if ( s == NULL ) 
      opensmt_error2( "undeclared sort identifier ", name );
  Snode * res = cons( s );
  return res;
}

//
// Inserts a symbol
//
void SStore::insertSymbol( Snode * s )
{
  assert( s );
  assert( s->isSymb( ) || s->isPara( ) );
  // Consistency for id
  assert( (snodeid_t)id_to_snode.size( ) == s->getId( ) );
  // Symbol is not there
  assert( name_to_symbol.find( s->getName( ) ) == name_to_symbol.end( ) );
  // Insert Symbol
  name_to_symbol[ s->getName( ) ] = s;
  id_to_snode.push_back( s );
}

//
// Removes a symbol
//
void SStore::removeSymbol( Snode * s )
{
  assert( s->isSymb( ) );
  map< string, Snode * >::iterator it = name_to_symbol.find( s->getName( ) );
  assert( it != name_to_symbol.end( ) );
  assert( it->second == s );
  name_to_symbol.erase( it );
  delete s;
}

//
// Retrieves a symbol from the name
//
Snode * SStore::lookupSymbol( const char * name )
{
  assert( name );
  map< string, Snode * >::iterator it = name_to_symbol.find( name );
  if ( it == name_to_symbol.end( ) ) return NULL;
  return it->second;
}

//
// Insert into Store
//
Snode * SStore::insertStore( const snodeid_t id, Snode * car, Snode * cdr )
{
  Snode * e = new Snode( id, car, cdr );
  Snode * x = store.insert( e );
  // Insertion done
  if ( x == e ) return e;
  // Node already there
  delete e;
  return x;
}

//
// Notice: different behaviour from Egraph::cons( list ... )
//
Snode * SStore::cons( list< Snode * > & args )
{
  Snode * elist = const_cast< Snode * >( snil );

  while( !args.empty( ) )
  {
    elist = cons( args.back( ), elist );
    args.pop_back( );
  }

  return elist;
}

//
// Creates a new term or list concretely (i.e., not modulo equivalence)
//
Snode * SStore::cons( Snode * car, Snode * cdr )
{
  assert( car );
  assert( cdr );
  assert( car->isTerm( ) || car->isSymb( ) || car->isPara( ) );
  assert( cdr->isList( ) );
  Snode * e = NULL;
  // Create and insert a new snode if necessary
  e = insertStore( id_to_snode.size( ), car, cdr );
  assert( e );
  // The node was there already. Return it
  if ( (snodeid_t)id_to_snode.size( ) != e->getId( ) )
    return e;
  // We keep the created snode
  id_to_snode.push_back( e );
  return e;
}

// 
// Create a parameter, unless it exists already
// in which case it returns the same
//
Snode * SStore::mkPara( const char * name )
{
  return cons( newPara( name ) );
}

void
SStore::dumpSortsToFile ( ostream & dump_out )
{
  // Dump function declarations
  for ( map< string, Snode * >::iterator it = name_to_symbol.begin( )
      ; it != name_to_symbol.end( ) 
      ; it ++ )
  {
    Snode * s = it->second;
    // Skip predefined symbols
    if ( s->getId( ) <= SNODE_ID_LAST )
      continue;
    // Skip parameters
    if ( s->isPara( ) )
      continue;
    dump_out << "(declare-sort " << s << " 0)" << endl;
  }
}
