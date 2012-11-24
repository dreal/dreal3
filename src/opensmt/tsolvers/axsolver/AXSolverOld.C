/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>
      , Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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

#include "Egraph.h"

// a != b → R( a, i_{a,b} ) = R( b, i_{a,b} )
void Egraph::ExtAxiom( Enode * a, Enode * b )
{
  assert( isDynamic( a ) );
  assert( isDynamic( b ) );
  Enode * as = dynamicToStatic( a );
  Enode * bs = dynamicToStatic( b );
  assert( isStatic( as ) );
  assert( isStatic( bs ) );

  assert( as->isDTypeArray( ) );
  assert( bs->isDTypeArray( ) );

  // create fresh index i_a,b for pair a,b
  char def_name[ 48 ];
  sprintf( def_name, IND_STR, as->getId( ), bs->getId( ) );
  const unsigned type = DTYPE_ARRAY_INDEX;
  if ( lookupSymbol( def_name ) == NULL )
    newSymbol( def_name, type );
  // Create new variable
  Enode * i = mkVar( def_name );
  // Create two new selections
  Enode * select1  = mkSelect( as, i );
  Enode * select2  = mkSelect( bs, i );
  // Create new literals
  Enode * lit1     = mkEq( cons( as, cons( bs ) ) );
  Enode * lit2_pos = mkEq( cons( select1, cons( select2 ) ) );
  Enode * lit2     = mkNot( cons( lit2_pos ) );
#ifdef PRODUCE_PROOF
  if ( config.gconfig.print_inter > 0 )
  {
    const uint64_t shared = getIPartitions( as ) 
			  & getIPartitions( bs );
    // Mixed can't be one at this point
    assert( shared != 1 );
    // Set AB-mixed partition if no intersection
    if ( shared == 0 )
    {
      setIPartitions( i, 1 );
      setIPartitions( select1, 1 );
      setIPartitions( select2, 1 );
      setIPartitions( lit1, 1 );
      setIPartitions( lit2_pos, 1 );
      setIPartitions( lit2, 1 );
    }
    // Otherwise they share something
    else
    {
      setIPartitions( i, shared );
      setIPartitions( select1, shared );
      setIPartitions( select2, shared );
      setIPartitions( lit1, shared );
      setIPartitions( lit2_pos, shared );
      setIPartitions( lit2, shared );
    }
  }
#endif
  vector< Enode * > v;
  v.push_back( lit1 );
  v.push_back( lit2 );
#ifdef ARR_VERB
  cout << "Axiom Ext ->   " << "( or " << lit1 << " " << lit2 << " )" << endl;
#endif
  splitOnDemand( v, id );

  handleArrayAssertedAtomTerm( select1 );
  handleArrayAssertedAtomTerm( select2 );

  // New contexts to propagate info about new index
  // Given R(a,new) look for all store users W(a,i,e) 
  // and instantiate RoW over R(W(a,i,e),new)
  vector< Enode * > sela;
  vector< Enode * > stoa;
  vector< Enode * > selb;
  vector< Enode * > stob;
  Enode * select3 = NULL;

  // Act over a
  getUsers( a, sela, stoa );
  for( size_t j = 0 ; j < stoa.size( ) ; j++ )
  {
    assert( isDynamic( stoa[ j ] ) );
    Enode * ss = dynamicToStatic( stoa[ j ] );
    assert( isStatic( ss ) );
    // Creation new select for each store user of a
    select3 = mkSelect( ss, i );
    // RoW over new select
    handleArrayAssertedAtomTerm( select3 );
#ifdef PRODUCE_PROOF
    if ( config.gconfig.print_inter > 0 )
    {
      const uint64_t shared = getIPartitions( ss ) 
	                    & getIPartitions( i );
      // Mixed can't be one at this point
      assert( shared != 1 );
      // Set AB-mixed partition if no intersection
      if ( shared == 0 )
	setIPartitions( select3, 1 );
      // Otherwise they share something
      else
	setIPartitions( select3, shared );
    }
#endif
  }

  // Act over b
  getUsers( b, selb, stob );
  for ( size_t j = 0 ; j < stob.size( ) ; j++ )
  {
    assert( isDynamic( stoa[ j ] ) );
    Enode * ss = dynamicToStatic( stob[ j ] );
    assert( isStatic( ss ) );
    // Creation new select for each store user of b
    select3 = mkSelect( ss, i );
#ifdef PRODUCE_PROOF
    if ( config.gconfig.print_inter > 0 )
    {
      const uint64_t shared = getIPartitions( ss ) 
	                    & getIPartitions( i );
      // Mixed can't be one at this point
      assert( shared != 1 );
      // Set AB-mixed partition if no intersection
      if ( shared == 0 )
	setIPartitions( select3, 1 );
      // Otherwise they share something
      else
	setIPartitions( select3, shared );
    }
#endif
    // RoW over new select
    handleArrayAssertedAtomTerm( select3 );
  }
}


void Egraph::handleArrayMerge( Enode * x, Enode * y )
{
  assert( ( x->isDTypeArray( ) && y->isDTypeArray( ) )
       || ( x->isDTypeArrayElement( ) && y->isDTypeArrayElement( ) ) );

  vector< Enode * > xSelUsers, xStoUsers;
  getUsers( x, xSelUsers, xStoUsers );
  vector<Enode * >::iterator xSelUsersIt;
  vector<Enode * >::iterator xStoUsersIt;

  vector< Enode * > ySelUsers, yStoUsers;
  getUsers( y, ySelUsers, yStoUsers );
  vector<Enode * >::iterator ySelUsersIt;
  vector<Enode * >::iterator yStoUsersIt;

#ifdef ARR_VERB_POSTMERGE
  cout << endl << "Getting x and y equivalence class users: " << endl;
  cout << "Equivalence class of x is: " << endl;
  Enode * aux=x;
  do { cout << aux << "   "; aux=aux->getNext(); } while(aux!=x);
  cout << endl << "Here are x class select users: " << endl;
  for ( xSelUsersIt = xSelUsers.begin( ); xSelUsersIt != xSelUsers.end( ); xSelUsersIt++ ) {cout << *xSelUsersIt << "   ";}
  cout << endl << "Here are x class store users: " << endl;
  for ( xStoUsersIt = xStoUsers.begin( ); xStoUsersIt != xStoUsers.end( ); xStoUsersIt++ ) {cout << *xStoUsersIt << "   ";}
  cout << endl << "Equivalence class of y is: " << endl;
  aux=y;
  do { cout << aux << "   "; aux=aux->getNext(); } while(aux!=y);
  cout <<  endl << "Here are y class select users: " << endl;
  for ( ySelUsersIt = ySelUsers.begin( ); ySelUsersIt != ySelUsers.end( ); ySelUsersIt++ ) {cout << *ySelUsersIt << "   ";}
  cout <<  endl << "Here are y class store users: " << endl;
  for ( yStoUsersIt = yStoUsers.begin( ); yStoUsersIt != yStoUsers.end( ); yStoUsersIt++ ) {cout << *yStoUsersIt << "   ";}
  cout << endl << endl;
#endif

  Enode * z, * zIndex;
  // , * zElement, * zArray,

  // TODO join all the cases together for more efficiency

  // NB x,y are elements of equivalence classes X,Y, we need to scan X or Y looking for store terms
  if( y->isDTypeArray() )
  {
    // Case 1: x is b, y is W(a,i,e), exists z as R(b,j)
    // Scan all R(b,j)
    for ( xSelUsersIt = xSelUsers.begin( )
	; xSelUsersIt != xSelUsers.end( )
	; xSelUsersIt++ )
    {
      z = * xSelUsersIt;
      zIndex = z->get2nd( );

      // scan Y looking for store terms
      Enode * YElem = y;
      do
      {
	if( YElem->isStore( ) )
	{
#ifdef ARR_VERB
	  cout << "Arrow down   B: " << x << "   W(A,I,E): " << YElem << "   R(B,J): " << z << endl;
#endif
	  // create new term R(W(a,i,e),j)
	  Enode * s_yelem = dynamicToStatic( YElem );
	  Enode * s_z2nd  = dynamicToStatic( z->get2nd( ) );
	  Enode * select = mkSelect( s_yelem, s_z2nd );
#ifdef PRODUCE_PROOF
	  if ( config.gconfig.print_inter > 0 )
	  {
	    const uint64_t shared = getIPartitions( s_yelem ) 
	                          & getIPartitions( s_z2nd );
	    // Mixed can't be one at this point
	    assert( shared != 1 );
	    // Set AB-mixed partition if no intersection
	    if ( shared == 0 )
	      setIPartitions( select, 1 );
	    // Otherwise they share something
	    else
	      setIPartitions( select, shared );
	  }
#endif
	  handleArrayAssertedAtomTerm( select );
	}

	YElem = YElem->getNext( );
      }
      while ( YElem != y );
    }
    /*// Case 2: x is b, y is W(a,i,e), exists z as W(b,j,f)
    // Scan all W(b,j,f)
    for (xStoUsersIt=xStoUsers.begin(); xStoUsersIt<xStoUsers.end(); xStoUsersIt++)
    {
    z=*xStoUsersIt;
    zElement=z->get3rd();
    zIndex=z->get2nd();

    // create new term W(W(a,i,e),j,f)
    newSto=mkStore(y,zIndex,zElement,present);

    // TODO check if term already seen in a previous assertion on the current path
    // deduce clauses for the new store
    newArrayDed(newSto);
    }*/
  }

  if( x->isDTypeArray() )
  {
    // Case 1 reverse: y is b, x is W(a,i,e), exists z as R(b,j)
    // Scan all R(b,j)
    for ( ySelUsersIt = ySelUsers.begin( )
	; ySelUsersIt != ySelUsers.end( )
	; ySelUsersIt++ )
    {
      z = *ySelUsersIt;
      zIndex = z->get2nd( );

      // scan X looking for store terms
      Enode * XElem = x;
      do
      {
	if( XElem->isStore( ) )
	{

#ifdef ARR_VERB
	  cout << "Arrow down   B: " << XElem << "   W(A,I,E): " << y << "   R(B,J): " << z << endl;
#endif

	  // Create new term R(W(a,i,e),j) from static version
	  Enode * s_xelem = dynamicToStatic( XElem );
	  Enode * s_z2nd = dynamicToStatic( z->get2nd( ) );
	  Enode * select = mkSelect( s_xelem, s_z2nd );
#ifdef PRODUCE_PROOF
	  if ( config.gconfig.print_inter > 0 )
	  {
	    const uint64_t shared = getIPartitions( s_xelem ) 
	                          & getIPartitions( s_z2nd );
	    // Mixed can't be one at this point
	    assert( shared != 1 );
	    // Set AB-mixed partition if no intersection
	    if ( shared == 0 )
	      setIPartitions( select, 1 );
	    // Otherwise they share something
	    else
	      setIPartitions( select, shared );
	  }
#endif
	  handleArrayAssertedAtomTerm( select );
	}

	XElem = XElem->getNext( );
      }
      while ( XElem != x );
    }
    /*// Case 2 reverse: y is a term b of type array, x is a Store W(a,i,e), exists z as W(b,j,f)
    // Scan all W(b,j,f)
    for (yStoUsersIt=yStoUsers.begin(); yStoUsersIt<yStoUsers.end(); yStoUsersIt++)
    {
    z=*yStoUsersIt;
    zElement=z->get3rd();
    zIndex=z->get2nd();

    // create new term W(W(a,i,e),j,f)
    newSto=mkStore(y,zIndex,zElement,present);

    // TODO check if term already seen in a previous assertion on the current path
    // deduce clauses for the new store
    newArrayDed(newSto);
    }*/
  }

  Enode * w;
  if( x->isDTypeArray( ) 
   && y->isDTypeArray( ) )
  {
    //Case 3: x is a term a of type array, y is a term b of type array, exist z as W(a,i,e) and w as R(b,j)
    //scan all W(a,i,e) and R(b,j)
    for ( ySelUsersIt = ySelUsers.begin( )
	; ySelUsersIt < ySelUsers.end( )
	; ySelUsersIt++ )
    {
      for ( xStoUsersIt = xStoUsers.begin( )
	  ; xStoUsersIt < xStoUsers.end( )
	  ; xStoUsersIt++ )
      {
	w = *ySelUsersIt; 
	z = *xStoUsersIt;

#ifdef ARR_VERB
	cout << "Arrow up   A: " << x << "   B: " << y << "   W(A,I,E): " << z << "   R(B,J): " << w << endl;
#endif

	// create new term R(W(a,i,e),j)
	Enode * s_z    = dynamicToStatic( z );
	Enode * s_w2nd = dynamicToStatic( w->get2nd( ) );
	Enode * select = mkSelect( s_z, s_w2nd );
#ifdef PRODUCE_PROOF
	if ( config.gconfig.print_inter > 0 )
	{
	  const uint64_t shared = getIPartitions( s_z ) 
	                        & getIPartitions( s_w2nd );
	  // Mixed can't be one at this point
	  assert( shared != 1 );
	  // Set AB-mixed partition if no intersection
	  if ( shared == 0 )
	    setIPartitions( select, 1 );
	  // Otherwise they share something
	  else
	    setIPartitions( select, shared );
	}
#endif
	handleArrayAssertedAtomTerm( select );
      }
    }
    //Case 3 reverse: y is a term a of type array, x is a term b of type array, exist z as W(a,i,e) and w as R(b,j)
    //scan all W(a,i,e) and R(b,j)
    for ( xSelUsersIt = xSelUsers.begin( )
	; xSelUsersIt < xSelUsers.end( )
	; xSelUsersIt++ )
    {
      for ( yStoUsersIt = yStoUsers.begin( )
	  ; yStoUsersIt < yStoUsers.end( )
	  ; yStoUsersIt++)
      {
	w = *xSelUsersIt; 
	z = *yStoUsersIt;
#ifdef ARR_VERB
	cout << "Arrow up   A: " << x << "   B: " << y << "   W(A,I,E): "<< z << "   R(B,J): " << w << endl;
#endif

	// create new term R(W(a,i,e),j)
	Enode * s_z    = dynamicToStatic( z );
	Enode * s_w2nd = dynamicToStatic( w->get2nd( ) );
	Enode * select = mkSelect( s_z, s_w2nd );
#ifdef PRODUCE_PROOF
	if ( config.gconfig.print_inter > 0 )
	{
	  const uint64_t shared = getIPartitions( s_z ) 
	                        & getIPartitions( s_w2nd );
	  // Mixed can't be one at this point
	  assert( shared != 1 );
	  // Set AB-mixed partition if no intersection
	  if ( shared == 0 )
	    setIPartitions( select, 1 );
	  // Otherwise they share something
	  else
	    setIPartitions( select, shared );
	}
#endif
	handleArrayAssertedAtomTerm( select );
      }
    }
  }

  /*//Case 4: x is a term e of type element, y is a Select R(b,j), exists z as W(a,i,e)
  //scan all W(a,i,e)
  if(y->isSelect())
  {
  for (xStoUsersIt=xStoUsers.begin(); xStoUsersIt<xStoUsers.end(); xStoUsersIt++)
  {
  z=*xStoUsersIt;
  zArray=z->get1st();
  zIndex=z->get2nd();
  // create new term W(a,i,R(b,j))
  newSto=mkStore(zArray,zIndex,y);

  // TODO check if term already seen in a previous assertion on the current path
  // deduce clauses for the new store
  newArrayDed(newSto);
  }
  }
  //Case 4 reverse: y is a term e of type element, x is a Select R(b,j), exists z as W(a,i,e)
  //scan all W(a,i,e)
  if(x->isSelect())
  {
  for (yStoUsersIt=yStoUsers.begin(); yStoUsersIt<yStoUsers.end(); yStoUsersIt++)
  {
  z=*yStoUsersIt;
  zArray=z->get1st();
  zIndex=z->get2nd();
  // create new term W(a,i,R(b,j))
  newSto=mkStore(zArray,zIndex,x);

  // TODO check if term already seen in a previous assertion on the current path
  // deduce clauses for the new store
  newArrayDed(newSto);
  }
  }*/
}

//
// Given a term, returns two vectors:
// the first one contains pointers to the select terms having a term equivalent to the input term as an argument
// the second one contains pointers to the store terms having a term equivalent to the input term as an argument
// NB: everything is done modulo equivalence, so users of the equivalence class of the term are returned
//
void Egraph::getUsers( Enode * x
                     , vector< Enode * > & sel
                     , vector< Enode * > & sto )
{
  assert( isDynamic( x ) );
  //
  // Case 1: x is a term a of type array
  //
  if( x->isDTypeArray( ) )
  {
    Enode * p, * gp;
    Enode * aux1, * aux2;

    // Find repeatedly a R(a,j) or a W(a,i,e)
    // scan the grandparents of a looking for a select or a store
    // NB: a is car of (a,j), (a,j) is cdr of R(a,j)
    // NB: a is car of (a,i,e), (a,i,e) is cdr of W(a,i,e)

    p = x->getParent( );
    aux1 = p;
    if ( aux1 != NULL && aux1->getCar( )->isDTypeArray( ) )
    {
      do {
	gp = aux1->getParent();
	aux2 = gp;
	if( aux2 != NULL && aux2->getCar( )->isSymb( ) )
	{
	  do {
	    if( aux2->isTerm( ) && aux2->isSelect( ) ) sel.push_back( aux2 );
	    if( aux2->isTerm( ) && aux2->isStore( ) ) sto.push_back( aux2 );
	    aux2 = aux2->getSameCdr( );
	  } while( aux2 != gp );
	}
	aux1 = aux1->getSameCar( );
      } while( aux1 != p );
    }
  }
  //
  // Case 2: x is a term i of type index
  //
  if( x->isDTypeArrayIndex( ) )
  {
    Enode * p, *gp, *ggp;
    Enode * aux1, *aux2, *aux3;

    // Find repeatedly a R(a,i) or a W(b,i,e)
    // scan the grandgrandparents of i looking for a select or a store
    // NB: i is car of (i), (i) is cdr of (a,i), which is cdr of R(a,i)
    // NB: i is car of (i,e), (i,e) is cdr of (b,i,e), which is cdr of W(b,i,e)

    p = x->getParent( );
    aux1 = p;
    if( aux1 != NULL && aux1->getCar( )->isDTypeArrayIndex( ) )
    {
      do {
	gp = aux1->getParent( );
	aux2 = gp;
	if( aux2 != NULL && aux2->getCar( )->isDTypeArray( ) )
	{
	  do {
	    ggp = aux2->getParent( );
	    aux3 = ggp;
	    if( aux3 != NULL && aux3->getCar( )->isSymb( ) )
	    {
	      do {
		if( aux3->isTerm( ) && aux3->isSelect( ) ) sel.push_back( aux3 );
		if( aux3->isTerm( ) && aux3->isStore( ) ) sto.push_back( aux3 );
		aux3 = aux3->getSameCdr( );
	      } while( aux3 != ggp );
	    }
	    aux2 = aux2->getSameCdr( );
	  } while( aux2 != gp );
	}
	aux1 = aux1->getSameCar( );
      } while( aux1 != p );
    }
  }

  //case 3: x is a term e of type element
  if( x->isDTypeArrayElement( ) )
  {
    Enode * p, *gp, *ggp, *gggp;
    Enode * aux1, *aux2, *aux3, *aux4;

    // Find repeatedly a W(a,i,e)
    // scan the grandgrandparents of e looking for a store
    // NB: e is car of (e), (e) is cdr of (i,e), which is cdr of (a,i,e)
    // and again cdr of W(a,i,e)

    p = x->getParent( );
    // cerr << "X: " << x << endl;
    aux1 = p;
    if( aux1 != NULL && aux1->getCar( )->isDTypeArrayElement( ) )
    {
      do {
	// cerr << "AUX1: " << aux1 << endl;
	gp = aux1->getParent( );
	aux2 = gp;
	if( aux2 != NULL && aux2->getCar( )->isDTypeArrayIndex( ) )
	{
	  do {
	    // cerr << "AUX2: " << aux2 << endl;
	    ggp = aux2->getParent( );
	    aux3 = ggp;
	    if( aux3 != NULL && aux3->getCar( )->isDTypeArray( ) )
	    {
	      do {
		// cerr << "AUX3: " << aux3 << endl;
		gggp = aux3->getParent();
		aux4 = gggp;
		if( aux4 != NULL && aux4->getCar( )->isSymb( ) )
		{
		  do {
		    // cerr << "AUX4: " << aux4 << endl;
		    if( aux4->isTerm( ) && aux4->isStore( ) ) sto.push_back(aux4);
		    aux4 = aux4->getSameCdr( );
		    assert( aux4 );
		  } while( aux4 != gggp );
		}
		aux3 = aux3->getSameCdr( );
	      } while( aux3 != ggp );
	    }
	    aux2 = aux2->getSameCdr( );
	  } while( aux2 != gp );
	}
	aux1 = aux1->getSameCar( );
      } while( aux1 != p );
    }
  }
}

//∀a, i, e, j, f 		i != j → W (W (a, i, e), j, f ) = W (W (a, j, f ), i, e)
void Egraph::WoWNeqAxiom( Enode * wow )
{
  assert( false );
  Enode * wowArray = wow->get1st( );
  Enode * a = wowArray->get1st( );
  Enode * i = wowArray->get2nd( );
  Enode * e = wowArray->get3rd( );
  Enode * j = wow->get2nd( );
  Enode * f = wow->get3rd( );

  assert( wowArray->isDTypeArray( ) );
  assert( a->isDTypeArray( ) );
  assert( i->isDTypeArrayIndex( ) );
  assert( e->isDTypeArrayElement( ) );
  assert( j->isDTypeArrayIndex( ) );
  assert( f->isDTypeArrayElement( ) );

  // Case i, j not coincident
  if( i != j )
  {
    // create term W(W(a,j,f),i,e)
    Enode * store1 = mkStore(a,j,f);
    Enode * store2 = mkStore(store1,i,e);

    // add clause IF i!=j THEN W(W(a,i,e),j,f)=W(W(a,j,f),i,e)
    // that is (i=j OR W(W(a,i,e),j,f)=W(W(a,j,f),i,e))
    vector< Enode * > v;
    Enode * lit1 = mkEq(cons(i,cons(j)));
    Enode * lit2 = mkEq(cons(wow,cons(store2)));

    v.push_back( lit1 );
    v.push_back( lit2 );
#ifdef ARR_VERB
    cout << "Axiom WoW!= ->   " << "(or " << lit1 << " " << lit2 << " )" << endl;
#endif
    splitOnDemand( v, id );
    handleArrayAssertedAtomTerm(store2);
  }
}

// ∀a, i, b, j.	( a = b → i = j → W (a, i, R(b, j)) = a )
void Egraph::WoRAxiom( Enode * wor )
{
  assert( false );
  Enode * a = wor->get1st( );
  Enode * i = wor->get2nd( );
  Enode * worElement = wor->get3rd( );
  Enode * b = worElement->get1st( );
  Enode * j = worElement->get2nd( );

  assert( worElement->isDTypeArrayElement( ) );
  assert( a->isDTypeArray( ) );
  assert( i->isDTypeArrayIndex( ) );
  assert( b->isDTypeArray( ) );
  assert( j->isDTypeArrayIndex( ) );

  // create term W(a,i,R(b,j))
  Enode * select = mkSelect( b, j );
  Enode * store = mkStore(a,i,select);

  // add clause IF a=b THEN IF i=j THEN W(a,i,R(b,j))=a
  // that is (NOT(a=b) OR NOT(i=j) OR W(a,i,R(b,j))=a)
  vector< Enode * > v;
  Enode * lit1 = mkNot(cons(mkEq(cons(a,cons(b)))));
  Enode * lit2 = mkNot(cons(mkEq(cons(i,cons(j)))));
  Enode * lit3 = mkEq(cons(store,cons(a)));

  v.push_back( lit1 );
  v.push_back( lit2 );
  v.push_back( lit3 );
#ifdef ARR_VERB
  cout << "Axiom WoR ->   " << "(or " << lit1 << " " << lit2 << " " << lit3 << " )" << endl;
#endif
  splitOnDemand( v, id );
  handleArrayAssertedAtomTerm( a );
}

// ∀a, i, e, j, f. ( i = j → W ( W ( a, i, e ), j, f ) = W ( a, j, f ) )
void Egraph::WoWEqAxiom( Enode * wow )
{
  assert( false );
  Enode * wowArray = wow->get1st( );
  Enode * a = wowArray->get1st( );
  Enode * i = wowArray->get2nd( );
  Enode * e = wowArray->get3rd( );
  Enode * j = wow->get2nd( );
  Enode * f = wow->get3rd( );

  assert( wowArray->isDTypeArray( ) );
  assert( a->isDTypeArray( ) );
  assert( i->isDTypeArrayIndex( ) );
  assert( e->isDTypeArrayElement( ) );
  assert( j->isDTypeArrayIndex( ) );
  assert( f->isDTypeArrayElement( ) );

  //i,j not coincident
  if( i != j )
  {
    // create term W(a,j,f)
    Enode * store = mkStore( a, j, f );
#ifdef PRODUCE_PROOF
    if ( config.gconfig.print_inter > 0 )
    {
      const uint64_t shared = getIPartitions( a ) 
	                    & getIPartitions( j )
			    & getIPartitions( f );
      // Mixed can't be one at this point
      assert( shared != 1 );
      // Set AB-mixed partition if no intersection
      if ( shared == 0 )
	setIPartitions( store, 1 );
      // Otherwise they share something
      else
	setIPartitions( store, shared );
    }
#endif
    // add clause IF i=j THEN W(W(a,i,e),j,f)=W(a,j,f)
    // that is (NOT(i=j) OR W(W(a,i,e),j,f)=W(a,j,f))
    vector< Enode * > v;
    Enode * lit1_pos = mkEq( cons( i, cons( j ) ) );
    Enode * lit1 = mkNot( cons( lit1_pos ) );
#ifdef PRODUCE_PROOF
    if ( config.gconfig.print_inter > 0 )
    {
      const uint64_t shared = getIPartitions( i ) 
	                    & getIPartitions( j );
      // Mixed can't be one at this point
      assert( shared != 1 );
      // Set AB-mixed partition if no intersection
      if ( shared == 0 )
      {
	setIPartitions( lit1_pos, 1 );
	setIPartitions( lit1, 1 );
      }
      // Otherwise they share something
      else
      {
	setIPartitions( lit1_pos, shared );
	setIPartitions( lit1, shared );
      }
    }
#endif
    Enode * lit2 = mkEq( cons( wow, cons( store ) ) );
#ifdef PRODUCE_PROOF
    if ( config.gconfig.print_inter > 0 )
    {
      const uint64_t shared = getIPartitions( wow ) 
	                    & getIPartitions( store );
      // Mixed can't be one at this point
      assert( shared != 1 );
      // Set AB-mixed partition if no intersection
      if ( shared == 0 )
	setIPartitions( lit2, 1 );
      // Otherwise they share something
      else
	setIPartitions( lit2, shared );
    }
#endif
    v.push_back( lit1 );
    v.push_back( lit2 );
#ifdef ARR_VERB
    cout << "Axiom WoW= ->   " << "(or " << lit1 << " " << lit2 << " )" << endl;
#endif
    splitOnDemand( v, id );
    handleArrayAssertedAtomTerm( store );
  }
}

