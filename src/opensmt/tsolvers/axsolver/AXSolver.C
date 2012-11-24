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

#define ARR_VERB
#include "Egraph.h"

///////////////////////ARRAY SUPERTERMS AND INDICES DATA HANDLING/////////////////////////////////////////

#if 0
//Updates list of array superterms
void Egraph::addStoreSuperterm( Enode * term, Enode * superterm )
{
	pair< map< enodeid_t, list<Enode*> >::iterator, bool > ret;
	ret = storeSuperterms.insert( pair< enodeid_t, list<Enode*> >( term->getId( ), list<Enode*>() ) );
	(ret.first->second).push_back(superterm);
}

list<Enode*>& Egraph::getStoreSupertermsList( Enode * term )
{
	pair< map< enodeid_t, list<Enode*> >::iterator, bool > ret;
	ret = storeSuperterms.insert( pair< enodeid_t, list<Enode*> >( term->getId( ), list<Enode*>() ) );
	return ret.first->second;
}

void Egraph::printStoreSupertermsList( Enode * term )
{
	list<Enode*>listTemp=getStoreSupertermsList(term);
	list<Enode*>::iterator it;

	cout << endl << "Term:" << endl << term << endl;
	cout << "Store superterms list:" << endl;
	for(it=listTemp.begin();it!=listTemp.end(); it++) cout << (*it) << endl;
	cout << endl;
}

//Returns true if index was actually inserted in term set
bool Egraph::addArrayRelevantIndex( Enode * term, Enode *index)
{
	pair< map< enodeid_t, set<Enode*> >::iterator, bool > ret;
	//Get set associated to term
	ret = arrayRelevantIndicesSet.insert( pair< enodeid_t, set<Enode*> >( term->getId( ), set<Enode*>() ) );
	//Check if index already present in set, otherwise add it
	pair<set<Enode*>::iterator,bool> res=(ret.first->second).insert(index);
	return res.second;
}

//Returns true if index was find in term set
bool Egraph::findArrayRelevantIndex( Enode * term, Enode *index)
{
	pair< map< enodeid_t, set<Enode*> >::iterator, bool > ret;
	ret = arrayRelevantIndicesSet.insert( pair< enodeid_t, set<Enode*> >( term->getId( ), set<Enode*>() ) );
	bool found=((ret.first->second).find(index) != ret.first->second.end());
	return found;
}

set<Enode*>& Egraph::getArrayRelevantIndicesSet( Enode * term )
{
	pair< map< enodeid_t, set<Enode*> >::iterator, bool > ret;
	ret = arrayRelevantIndicesSet.insert( pair< enodeid_t, set<Enode*> >( term->getId( ), set<Enode*>() ) );
	return ret.first->second;
}

void Egraph::printArrayRelevantIndicesSets( Enode * term )
{
	set<Enode*>listTemp=getArrayRelevantIndicesSet(term);
	set<Enode*>::iterator it;

	cout << endl << "Term:" << endl << term << endl;
	cout << "Relevant indices set:" << endl;
	for(it=listTemp.begin();it!=listTemp.end(); it++) cout << (*it) << " ";
	cout << endl;
}

////////////////////////////////////////////////ASSERTIONS HANDLING///////////////////////////////////////////////////

//Handles assertion equality atoms
void Egraph::handleArrayAssertedEq( Enode * x, Enode * y )
{
	if( x->hasSortElem( ) || x->hasSortArray( ) )
	{
		//cout << endl << "Dynamic x: " << x << endl;
		//cout << "Dynamic y: " << y << endl;

		assert( isDynamic( x ) );
		assert( isDynamic( y ) );
		Enode * x1 = dynamicToStatic( x );
		Enode * y1 = dynamicToStatic( y );

		//cout << "Static x: " << x << endl;
		//cout << "Static y: " << y << endl << endl;

		assert( isStatic( x1 ) && isStatic( y1 ) );
		assert( (x1->hasSortArray( ) && y1->hasSortArray( )) 
		     || (x1->hasSortElem() && y1->hasSortElem( )) );

		//Call on potentially new terms
		handleArrayAssertedAtomTerm( x1 );
		handleArrayAssertedAtomTerm( y1 );
	}
}

//Handles assertion disequality atoms
void Egraph::handleArrayAssertedNEq( Enode * x, Enode * y )
{
	if( x->hasSortElem( ) || x->hasSortArray( ) )
	{
		assert( isDynamic( x ) );
		assert( isDynamic( y ) );

		Enode * x1 = dynamicToStatic( x );
		Enode * y1 = dynamicToStatic( y );

		assert( isStatic( x1 ) && isStatic( y1 ) );

		//Call on potentially new terms
		handleArrayAssertedAtomTerm( x1 );
		handleArrayAssertedAtomTerm( y1 );
		if( x->hasSortArray( ) )
		  ExtAxiom( x1 , y1 );
	}
}

////////////////////////////////////INDEX INFORMATION PROPAGATION////////////////////////////////////////////////

//Instantiate axioms after encountering a new term
//NB: relevance of index for an array term determined only after assertion atom
void Egraph::handleArrayAssertedAtomTerm( Enode * x )
{
	assert( isStatic( x ) );

	// Adjust vector size
	if ( x->getId( ) > static_cast< int >( arrayAtomTermDone.size( ) ) )
		arrayAtomTermDone.resize( x->getId( ) + 1, false );

	// Skip already seen nodes
	if ( arrayAtomTermDone[ x->getId( ) ] )
		return;

	// This node has been done
	arrayAtomTermDone[ x->getId( ) ] = true;

	//Case select
	if( x->isSelect() )
	{
		Enode * a = x->get1st();
		Enode * i = x->get2nd();

#ifdef ARR_VERB
		cout << endl << "Before addition index: " << i;
		printArrayRelevantIndicesSets(a);
		cout << endl;
#endif

		//Try to add i to set relevant indexes for x and check if it was already added
		bool added=addArrayRelevantIndex(a,i);
		//If the index is new then propagate it to sub and super array terms
		if(added)
		{
			propagateIndexToArraySubterm(x);
			propagateIndexToArraySuperterms(x);
			propagateIndexToArrayEquivalenceClass(a,i);
		}

#ifdef ARR_VERB
		if(added)
		{
			cout << endl << "After addition index: " << i;
			printArrayRelevantIndicesSets(a);
			cout << endl;
		}
#endif


	}

	//DONE IN PREPROCESSING
	//Cases simple write to be encapsulated into read
	//if ( x->isStore( ) ) WAxiom( x );
}

//Input: R(b,j)
//If b is W(a,i,e) then propagate j to subterm via axioms RoW: i!=j -> R(W(a,i,e),j)=R(a,j)
void Egraph::propagateIndexToArraySubterm(Enode * select)
{
	assert(select->isSelect());

	Enode * b = select->get1st();
	Enode * j = select->get2nd();

#ifdef ARR_VERB
	cout << endl << "Propagating index " << select->get2nd() << " to subterm from " << endl << select << endl;
#endif

	//Instantiate read over write
	//if b is W(a,i,e)
	if( b->isStore( ) )
	{
		Enode * a = b->get1st();
		Enode * i = b->get2nd();
		//We have to distinguish between two cases:
		//First: R(W(a,i,e),j) immediate application RoW
		if(i!=j)
		{
			RoWEqAxiom( select );
			RoWNeqAxiom( select );
		}
		//Second: R(W(a,j,e),j) must force read on a if a is store itself
		if(a->isStore())
		{
			//R(a,j)
			Enode * newSelect=mkSelect(a,j);
			RoWEqAxiom( newSelect );
			RoWNeqAxiom( newSelect );
		}
	}

}

//Input: R(b,j)
//If b is subterm of W(b,i,e) then propagate j to superterms via axioms RoW: i!=j -> R(b,j)=R(W(b,i,e),j)
void Egraph::propagateIndexToArraySuperterms( Enode * select )
{
	assert(select->isSelect());

	Enode * b = select->get1st();
	Enode * j = select->get2nd();
	Enode * newSelect;

#ifdef ARR_VERB
	cout << endl << "Propagating index " << select->get2nd() << " to superterms from " << endl << select << endl;
#endif

	//Retrieve list of array superterms
	list<Enode*> superterms = getStoreSupertermsList(b);
	//cout << "Term: " << select << endl;
	//Scan list
	for(list<Enode*>::iterator it=superterms.begin(); it!=superterms.end(); it++)
	{
		//Create term R(W(b,i,e),j)
		newSelect=mkSelect((*it),j);
		//cout << "Propagating to " << newSelect << endl;
		//TODO check if new or old terms!
		//Instantiate read over write
		RoWEqAxiom(newSelect);
		RoWEqAxiom(newSelect);
	}
}

//Input: b,j
//Propagate the existence of the index j to the equivalence class of b
//For each pair c,d add clause c=d->(R(c,j)=R(d,j))
void Egraph::propagateIndexToArrayEquivalenceClass( Enode * b, Enode * j )
{
	assert( b->hasSortArray( ) );
	assert(isStatic(b));
	assert( j->hasSortIndex( ) );
	assert(isStatic(j));

	Enode * staticTemp1, * staticTemp2, * dynamicb, * dynamicTemp1, *dynamicTemp2;
	dynamicb=staticToDynamic(b);

	//TODO crappy solution
	//NB risk that the index is propagated a lot of times!
	//Should be propagated only first time it is seen by a member x of the class, that is
	//first time an atom is asserted in which there is R(x,j)
	//So check if any member of the class has j
	//TODO can exploit class representant???
	dynamicTemp2=dynamicb;
	do
	{
		staticTemp2=dynamicToStatic(dynamicTemp2);
		//Index found in a class member
		if(findArrayRelevantIndex(staticTemp2,j)) return;

		dynamicTemp2=dynamicTemp2->getNext();
	}
	while(dynamicTemp2!=dynamicb);

	//Scan all pairs in the current equivalence class of b
	//and instantiate equality axiom over j
	dynamicTemp1=dynamicb;
	do
	{
		dynamicTemp2=dynamicb;
		do
		{
			staticTemp1=dynamicToStatic(dynamicTemp1);
			staticTemp2=dynamicToStatic(dynamicTemp2);

			if(staticTemp1!=staticTemp2)
				EqAxiomInst(staticTemp1,staticTemp2,j);

			dynamicTemp2=dynamicTemp2->getNext();
		}
		while(dynamicTemp2!=dynamicb);

		dynamicTemp1=dynamicTemp1->getNext();
	}
	while(dynamicTemp1!=dynamicb);

}

//TODO beginning must be like asserteq
void Egraph::handleArrayMerge( Enode * x, Enode * y )
{
	//Index equalities dealt with by EUF
	if( x->hasSortIndex( ) && y->hasSortIndex( ) ) return;

	assert( isDynamic( x ) );
	assert( isDynamic( y ) );
	Enode * a = dynamicToStatic( x );
	Enode * b = dynamicToStatic( y );

	//cout << "Static x: " << x << endl;
	//cout << "Static y: " << y << endl << endl;

	assert( isStatic( a ) && isStatic( b ) );
	assert( (a->hasSortArray( ) && b->hasSortArray( )) 
	     || (a->hasSortElem( ) && b->hasSortElem( )) );

	//Call on potentially new terms
	handleArrayAssertedAtomTerm( a );
	handleArrayAssertedAtomTerm( b );
	//Now we can be sure about the
	//invariant: an index found in a class has already been propagated to other members

	//Read/element equalities dealt with by EUF
	if( x->hasSortElem( ) && y->hasSortElem( ) ) return;

	//Array handling
	Enode * static1, * static2, * dyna, *dynb, * dyn1, *dyn2;
	dyna=staticToDynamic(a);
	dynb=staticToDynamic(b);

	set<Enode*> listRelevantIndices1;
	set<Enode*> listRelevantIndices2;
	set<Enode*> listRelevantIndiceTemp;
	set<Enode*> listRelevantIndicesGlobal;
	set<Enode*>::iterator it;

	//Strategy:
	//Determine I set indices relevant in first class
	//Determine J set indices relevant in second class
	//Propagate indices of I/J to second class
	//Propagate indices of J/I to first class
	//Propagate indices of I U J across classes
	//Don't worry about indices not found yet, they will be propagated naturally later

	//Determine I set indices relevant in first class
	dyn1=dyna;
	do
	{
		static1=dynamicToStatic(dyn1);
		//Collect local set of relevant indexes
		listRelevantIndiceTemp=getArrayRelevantIndicesSet(static1);
		for(it=listRelevantIndiceTemp.begin();it!=listRelevantIndiceTemp.end();it++)
			listRelevantIndices1.insert(*it);

		dyn1=dyn1->getNext();
	}
	while(dyn1!=dyna);

	//Determine J set indices relevant in second class
	dyn2=dynb;
	do
	{
		static2=dynamicToStatic(dyn2);
		//Collect local set of relevants indexes
		listRelevantIndiceTemp=getArrayRelevantIndicesSet(static2);
		for(it=listRelevantIndiceTemp.begin();it!=listRelevantIndiceTemp.end();it++)
			listRelevantIndices1.insert(*it);

		dyn2=dyn2->getNext();
	}
	while(dyn2!=dynb);

	//Propagate indices of I/J to second class
	for(it=listRelevantIndices1.begin();it!=listRelevantIndices1.end();it++)
	{
		if(listRelevantIndices2.find(*it)==listRelevantIndices2.end())
			propagateIndexToArrayEquivalenceClass(b,(*it));
		//Add to global set
		listRelevantIndicesGlobal.insert(*it);
	}

	//Propagate indices of J/I to first class
	for(it=listRelevantIndices2.begin();it!=listRelevantIndices2.end();it++)
	{
		if(listRelevantIndices1.find(*it)==listRelevantIndices1.end())
			propagateIndexToArrayEquivalenceClass(a,(*it));
		//Add to global set
		listRelevantIndicesGlobal.insert(*it);
	}

	//Propagate indices of I U J across the classes
	Enode* index;
	//Scan set I U J
	for(it=listRelevantIndicesGlobal.begin();it!=listRelevantIndicesGlobal.end();it++)
	{
		index=(*it);
		//For each index, scan all pairs across classes
		dyn1=dyna;
		do
		{
			dyn2=dynb;
			do
			{
				static1=dynamicToStatic(dyn1);
				static2=dynamicToStatic(dyn2);

				if(static1!=static2)
					EqAxiomInst(static1,static2,index);

				dyn2=dyn2->getNext();
			}
			while(dyn2!=dynb);

			dyn1=dyn1->getNext();
		}
		while(dyn1!=dyna);
	}
}

////////////////////////////////////////// ARRAY AXIOMS //////////////////////////////////////////////////

//DONE IN PREPROCESSING
// ∀a, i, e. R(W (a, i, e), i) = e
void Egraph::WAxiom( Enode * w )
{
	assert( w->hasSortArray( ) && w->isStore( ) );

	Enode * i = w->get2nd( );
	bool present;
	Enode * select = mkSelect( w, i, present );
	addArrayRelevantIndex(w,i);

#ifdef ARR_VERB
	cout << endl << "WAxiom:" << endl << w << endl << "->" << endl << select << endl;
#endif
}

// ∀a, i, e, j. i = j → R(W (a, i, e), j) = e
void Egraph::RoWEqAxiom( Enode * row )
{
	assert(row->isSelect());

	Enode * rowArray = row->get1st( );
#ifndef OPTIMIZE
	Enode * a = rowArray->get1st( );
#endif
	Enode * e = rowArray->get3rd( );
	Enode * i = rowArray->get2nd( );
	Enode * j = row->get2nd( );

	assert( rowArray->hasSortArray( ) );
	assert( a->hasSortArray( ) );
	assert( i->hasSortIndex( ) );
	assert( e->hasSortElem( ) );
	assert( j->hasSortIndex( ) );

	// i, j not coincident
	if( i != j )
	{
		//
		// Add clause IF i=j THEN R(W(a,i,e),j)=e
		// that is (NOT(i=j) OR R(W(a,i,e),j)=e)
		//
		vector< Enode * > v;
		Enode * lit1_pos = mkEq( cons( i, cons( j ) ) );
		Enode * lit1     = mkNot( cons( lit1_pos ) );
#ifdef PRODUCE_PROOF
		if ( config.gconfig.print_inter > 0 )
		{
			const uint64_t shared = getIPartitions( i ) & getIPartitions( j );
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
		Enode * lit2     = mkEq( cons( row, cons( e ) ) );
#ifdef PRODUCE_PROOF
		if ( config.gconfig.print_inter > 0 )
		{
			const uint64_t shared = getIPartitions( row ) & getIPartitions( e );
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
		cout << endl << "RoWEqAxiom:" << endl << row << endl << "->" << endl << "(or" << endl << lit1 << endl << lit2 << endl << ")" << endl;
#endif
		splitOnDemand( v, id );
	}
	// DONE IN PREPROCESSING FOR EACH WRITE TERM
	/*	else
		// i, j coincident
	{
		//
		// Add unit clause R(W(a,i,e),i)=e
		//
		Enode * lit = mkEq( cons( row, cons( e ) ) );
		cout << endl << "RoWEqAxiom:" << endl << row << endl << "->" << endl << lit << endl;
		splitOnDemand( lit, id );
		//Call on potentially new term
		existenceDeductions( e );
	}*/
}

// ∀a, i, e, j.	i != j → R(W (a, i, e), j) = R(a, j)
void Egraph::RoWNeqAxiom( Enode * row )
{
	assert(row->isSelect());
	assert(isStatic(row));

	Enode * rowArray = row->get1st( );
	Enode * a = rowArray->get1st( );
	Enode * i = rowArray->get2nd( );
#ifndef OPTIMIZE
	Enode * e = rowArray->get3rd( );
#endif
	Enode * j = row->get2nd( );

	assert( rowArray->hasSortArray( ) );
	assert( a->hasSortArray( ) );
	assert( i->hasSortIndex( ) );
	assert( e->hasSortElem( ) );
	assert( j->hasSortIndex( ) );

	// i,j not coincident
	if( i != j )
	{
		bool present;
		Enode * select = mkSelect( a, j, present );

#ifdef PRODUCE_PROOF
		if ( config.gconfig.print_inter > 0 )
		{
			const uint64_t shared = getIPartitions( a )
	                    																																																																																						& getIPartitions( j );
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
		//
		// Add clause IF i!=j THEN R(W(a,i,e),j)=R(a,j)
		// that is (i=j OR R(W(b,i,e),j)=R(b,j))
		//
		vector< Enode * > v;
		Enode * lit1 = mkEq( cons( i, cons( j ) ) );
#ifdef PRODUCE_PROOF
		if ( config.gconfig.print_inter > 0 )
		{
			const uint64_t shared = getIPartitions( i )
	                    																																																																																						& getIPartitions( j );
			// Mixed can't be one at this point
			assert( shared != 1 );
			// Set AB-mixed partition if no intersection
			if ( shared == 0 )
				setIPartitions( lit1, 1 );
			// Otherwise they share something
			else
				setIPartitions( lit1, shared );
		}
#endif
		Enode * lit2 = mkEq( cons( row, cons( select ) ) );
#ifdef PRODUCE_PROOF
		if ( config.gconfig.print_inter > 0 )
		{
			const uint64_t shared = getIPartitions( row )
	                    																																																																																						& getIPartitions( select );
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
		cout << endl << "RoWNEqAxiom:" << endl << row << endl << "->" << endl << "(or" << endl << lit1 << endl << lit2 << endl << ")" << endl;
#endif
		splitOnDemand( v, id );
	}
}

// a != b → R( a, i_{a,b} ) = R( b, i_{a,b} )
void Egraph::ExtAxiom( Enode * as, Enode * bs )
{
	assert( as->hasSortArray( ) );
	assert( bs->hasSortArray( ) );

	assert(isStatic(as));
	assert(isStatic(bs));

	// create fresh index i_a,b for pair a,b
	char def_name[ 48 ];
	sprintf( def_name, IND_STR, as->getId( ), bs->getId( ) );
	Snode * s = sort_store.mkIndex( );
	// Adds only if it does not exist
	if ( lookupSymbol( def_name ) == NULL )
	  newSymbol( def_name, s );
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
	//
	// Add clause IF a!=b THEN R(a,inew)!=R(b,inew)
	// that is (a=b OR R(a,inew)!=R(b,inew))
	//
	vector< Enode * > v;
	v.push_back( lit1 );
	v.push_back( lit2 );
#ifdef ARR_VERB
	cout << endl << "ExtAxiom:" << endl << as << endl << bs << endl << "->" << endl << "(or" << endl << lit1 << endl << lit2 << endl << ")" << endl;
#endif
	splitOnDemand( v, id );
}

// a = b → R( a, i ) = R( b, i ) for a certain i
void Egraph::EqAxiomInst( Enode * a, Enode * b, Enode * i )
{
	assert( a->hasSortArray( ) );
	assert( b->hasSortArray( ) );
	assert( i->hasSortIndex( ) );
	assert(isStatic(a) && isStatic(b) && isStatic(i));

	// Create reads R(a,i) R(b,i)
	Enode * select1=mkSelect( a, i );
	Enode * select2=mkSelect( b, i );

	// Create inequality a!=b
	Enode * lit1=mkNot( cons( mkEq( cons( a, cons( b ) ) ) ) );

	// Create equality R(a,i)=R(b,i)
	Enode * lit2=mkEq( cons( select1, cons( select2 ) ) );

	vector<Enode*>v;
	// Add axiom a=b -> R(a,i)=R(b,i)
	v.push_back( lit1 );
	v.push_back( lit2 );
#ifdef ARR_VERB
	cout << endl << "EqAxiom over " << i << endl << a << endl << b << endl << "->" << endl << "(or" << endl << lit1 << endl << lit2 << endl << ")" << endl;
#endif
	splitOnDemand( v, id );
}
#endif
