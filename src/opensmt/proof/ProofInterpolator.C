/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

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

#include "ProofGraph.h"

//#define INTVERB

//Input: empty vector, flag for using symmetric or McMillan's system
//Output: sequence of interpolants
void ProofGraph::produceSequenceInterpolants(vector<Enode*> & sequence_of_interpolants, bool symmetric)
{
  assert(sequence_of_interpolants.size()==0);

  //Clause and partial interpolant
  ProofNode* n;
  Enode* partial_interp;

  //Vector for topological ordering
  vector<clauseid_t> DFSv;
  //Compute topological sorting of graph
  topolSorting(DFSv);
  size_t proof_size=DFSv.size();

  //Determine number of partitions
  unsigned num_partitions = egraph.getNofPartitions();
  //Interpolant partition masks
  uint64_t A_mask=0;
  uint64_t B_mask=0;

  //Compute sequence of interpolants (m with m partitions)
  for( unsigned curr_interp = 0 
     ; curr_interp < num_partitions + 1
     ; curr_interp ++ )
  {
    //Update current interpolant partition mask
    //Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
    if(curr_interp!=0) A_mask = A_mask | (uint64_t)(SETBIT(curr_interp));
    //Determine mask corresponding to B
    B_mask= ~A_mask;
    //Reset bit 0 to 0
    B_mask= B_mask & (~((uint64_t)SETBIT(0)));

#ifdef INTVERB
    cout << "Generating interpolant " << curr_interp << " with A mask" << endl;
    printBits(A_mask);
    cout << "and B mask" << endl;
    printBits(B_mask);
    cout << endl;
#endif

    // Traverse proof and compute current interpolant
    for( size_t i = 0 ; i < proof_size ; i++ )
    {
      n = graph[ DFSv[ i ] ];

      // Generate partial interpolant for clause i
      partial_interp = genPartialInterp( n, curr_interp, A_mask, B_mask, symmetric );
#ifdef INTVERB
      cout << "Partial interpolant: " << partial_interp << endl << endl;
#endif
    }
#ifdef INTVERB
    cout << "*****************************************" << endl << endl;
#endif

    // Last clause visited is the empty clause with total interpolant
    sequence_of_interpolants.push_back( partial_interp );
  }
}

//Input: clause, current interpolant partition masks for A and B, flag for using symmetric or McMillan's system
//Output: partial interpolant for the clause
Enode * ProofGraph::genPartialInterp( ProofNode * n, int curr_interp, uint64_t A_mask, uint64_t B_mask, bool symmetric)
{
  assert(n!=NULL);

  // Partial interpolants
  Enode* partial_interp=NULL;
  Enode* partial_interp_ant1=NULL;
  Enode* partial_interp_ant2=NULL;

#ifdef INTVERB
  cout << "Clause " ; printClause(n);
  cout << "of type " << n->type;
  cout << " and partition mask "  << endl;
  printBits(n->partition_mask);
#endif

  // Node is leaf
  if(n->ant1==NULL && n->ant2==NULL)
  {
    // Theory lemma
    if(n->type==CLALEMMA)
    {
      // Retrieve partial interpolant for current division into A,B
      partial_interp = getPartialInterp(n,curr_interp);
    }
    //Original clauses
    else if(n->type==CLAORIG)
    {
      // cerr << "CLAORIG" << endl;
      //Determine clause color
      opensmt::CGCOLOR clause_color= getClauseColor(n, A_mask, B_mask);
      //Original leaves can be only A or B colored
      assert(clause_color==CG_A || clause_color==CG_B);

      //Compute interpolant
      if(!symmetric)
	//McMillan's system
      {
	//Leaf belongs to A -> interpolant = leaf clause restricted to B
	if(clause_color==CG_A)
	{
	  //Compute clause restricted to B
	  vector<Lit> restricted_clause;
	  restrictClauseToB(n,A_mask,B_mask,restricted_clause);
	  size_t clause_size=restricted_clause.size();

	  //Create enode for the restricted clause
	  if(clause_size==0)
	    //Partial interpolant is false in case of empty clause left
	    partial_interp=egraph.mkFalse();
	  else
	  {
	    //Initialize with first literal
	    partial_interp = thandler->varToEnode(var(restricted_clause[0]));
	    //Check polarity literal
	    if(sign(restricted_clause[0])) partial_interp = egraph.mkNot(egraph.cons(partial_interp));

	    Enode * lit;
	    for(size_t i=1;i<clause_size;i++)
	    {
	      lit = thandler->varToEnode(var(restricted_clause[i]));
	      //Check polarity literal
	      if(sign(restricted_clause[i])) lit = egraph.mkNot(egraph.cons(lit));
	      //Build adding literals progressively
	      partial_interp = egraph.mkOr(egraph.cons(partial_interp, egraph.cons(lit)));
	    }
	  }
	}
	//Leaf belongs to B -> interpolant = true
	else if(clause_color==CG_B)
	  partial_interp=egraph.mkTrue();
	else
	  assert(false);
      }
      else
	//Symmetric system
      {
	//Leaf belongs to A -> interpolant = false
	if(clause_color==CG_A)
	  partial_interp=egraph.mkFalse();
	//Leaf belongs to B -> interpolant = true
	else if(clause_color==CG_B)
	  partial_interp=egraph.mkTrue();
	else
	  assert(false);
      }
      //Set clause partial interpolant
      n->partial_interp = partial_interp;
    }
    assert( partial_interp );
  }
  //Node is derived
  else
  {
    //Get antecedents partial interpolants
    partial_interp_ant1=getPartialInterp(n->ant1,curr_interp);
    partial_interp_ant2=getPartialInterp(n->ant2,curr_interp);
    assert(partial_interp_ant1);
    assert(partial_interp_ant2);

    //Determine color pivot
    opensmt::CGCOLOR pivot_color= getVarColor(n->pivot,A_mask,B_mask);

    //Compute interpolant
    if(!symmetric)
      //McMillan's system
    {
      //Pivot colored A -> interpolant = interpolant of ant1 AND interpolant of ant2
      if(pivot_color==CG_A)
	partial_interp=egraph.mkOr(egraph.cons(partial_interp_ant1, egraph.cons(partial_interp_ant2)));
      //Pivot colored B or AB -> interpolant = interpolant of ant1 OR interpolant of ant2
      else if(pivot_color==CG_B || pivot_color==CG_AB)
	partial_interp=egraph.mkAnd(egraph.cons(partial_interp_ant1, egraph.cons(partial_interp_ant2)));
    }
    else
      //Symmetric system
    {
      //Pivot colored A -> interpolant = interpolant of ant1 AND interpolant of ant2
      if(pivot_color==CG_A)
	partial_interp=egraph.mkOr(egraph.cons(partial_interp_ant1, egraph.cons(partial_interp_ant2)));
      //Pivot colored B -> interpolant = interpolant of ant1 OR interpolant of ant2
      else if (pivot_color==CG_B)
	partial_interp=egraph.mkAnd(egraph.cons(partial_interp_ant1, egraph.cons(partial_interp_ant2)));
      //Pivot colored AB -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
      else if (pivot_color==CG_AB)
      {
	//Find pivot occurrences in ant1 and ant2 and create enodes
	Var piv=n->pivot;
	Lit l1, l2;
	Enode* piv_1, * piv_2;
	size_t size;
	size=n->ant1->clause.size();
	for(size_t i=0;i<size;i++)
	{
	  l1=n->ant1->clause[i];
	  if(var(l1)==piv)
	  {
	    piv_1 = thandler->varToEnode(var(l1));
	    //Check polarity occurrence
	    if(sign(l1)) piv_1 = egraph.mkNot(egraph.cons(piv_1));
	    break;
	  }
	}
	size=n->ant2->clause.size();
	for(size_t i=0;i<size;i++)
	{
	  l2=n->ant2->clause[i];
	  if(var(l2)==piv)
	  {
	    piv_2 = thandler->varToEnode(var(l2));
	    //Check polarity occurrence
	    if(sign(l2)) piv_2 = egraph.mkNot(egraph.cons(piv_2));
	    break;
	  }
	}
	assert(piv_1!=NULL); assert(piv_2!=NULL);

	Enode* or_1=egraph.mkOr(egraph.cons(partial_interp_ant1, egraph.cons(piv_1)));
	Enode* or_2=egraph.mkOr(egraph.cons(partial_interp_ant2, egraph.cons(piv_2)));
	partial_interp=egraph.mkAnd(egraph.cons(or_1, egraph.cons(or_2)));
      }
      else
	assert(false);
    }
    //Set clause partial interpolant
    n->partial_interp = partial_interp;
    assert( partial_interp );
  }
  return partial_interp;
}

//Input: variable, current interpolant partition masks for A and B
//e.g. 0---010 first partition in A
//Output: returns A-local , B-local or AB-common
opensmt::CGCOLOR ProofGraph::getVarColor(Var v, uint64_t A_mask, uint64_t B_mask)
{
  //Get enode corresponding to variable
  Enode* enode_var=thandler->varToEnode(v);

  //Get partition mask variable
  //e.g. 0---0110 variable in first and second partition
  uint64_t enode_mask = egraph.getIPartitions(enode_var);

#ifdef INTVERB
  //cout << "Pivot " << v << " has partition mask " << enode_mask << endl;
  //printBits(enode_mask);
#endif

  //Check if variable present in A or B
  bool var_in_A = ((enode_mask & A_mask) !=0);
  bool var_in_B = ((enode_mask & B_mask) !=0);
  assert(var_in_A || var_in_B);

  opensmt::CGCOLOR var_color;

  //Determine if variable A-local, B-local or AB-common
  if(var_in_A && !var_in_B) var_color = CG_A;
  else if(!var_in_A && var_in_B) var_color = CG_B;
  else if(var_in_A && var_in_B) var_color = CG_AB;
  else assert(false);

#ifdef INTVERB
  cout << "Pivot " << v <<" has color " << var_color << endl;
#endif

  return var_color;
}

//Input: proof node, current interpolant partition masks for A and B
//e.g. 0---010 first partition in A
//Output: returns A or B
opensmt::CGCOLOR ProofGraph::getClauseColor(ProofNode* n, uint64_t A_mask, uint64_t B_mask)
{
  //Get partition mask clause
  //e.g. 0---0110 variable in first and second partition
  uint64_t clause_mask = n->partition_mask;
  
  //Check if belongs to A or B
  bool clause_in_A = ((clause_mask & A_mask) !=0);
  bool clause_in_B = ((clause_mask & B_mask) !=0);
  assert(clause_in_A || clause_in_B);

  opensmt::CGCOLOR clause_color;

  //Determine if clause belongs to A or B
  if(clause_in_A && !clause_in_B) clause_color = CG_A;
  else if(!clause_in_A && clause_in_B) clause_color = CG_B;
  else if(clause_in_A && clause_in_B) clause_color = CG_AB;
  else assert(false);
#ifdef INTVERB
  cout << "Clause has color " << clause_color << endl;
#endif
  return clause_color;
}

//Input: clause in A, current interpolant partition masks for A and B
//Output: restricted clause wrt B
void ProofGraph::restrictClauseToB(ProofNode* n, uint64_t A_mask, uint64_t B_mask, vector<Lit>& restricted_clause)
{
  opensmt::CGCOLOR var_color;
  vector<Lit>& cl=n->clause;
  size_t size=cl.size();
  assert(restricted_clause.size()==0);

  //cout << "Original clause "; printClause(n);
  for(size_t i=0;i<size;i++)
  {
    var_color=getVarColor(var(cl[i]), A_mask, B_mask);
    assert(var_color!=CG_B);
    //cout << "Variable " << var(cl[i]) << " has color " << var_color << endl;
    if(var_color == CG_AB) restricted_clause.push_back(cl[i]);
  }

  /*	cout << "Restricted clause " << endl;
	for(size_t k=0;k<restricted_clause.size();k++)
	{
	if(sign(restricted_clause[k])) cout << "~";
	cout << var(restricted_clause[k]) << " ";
	}
	cout << endl;*/
}

// Input: clause
// Output: partial interpolant for current division into A,B
Enode* ProofGraph::getPartialInterp( ProofNode* n, int curr_interp )
{
  assert( n->partial_interp );

  // Return single partial interpolant in case of non theory lemma
  if( n->type != CLALEMMA )
    return n->partial_interp;

  Enode * interp = n->partial_interp;

  // First interpolant is always true
  if ( curr_interp == 0 )
    return egraph.mkTrue( );

  assert( curr_interp <= interp->getArity( ) + 1 );

  // Last interpolant is always false
  if ( curr_interp == interp->getArity( ) + 1 )
    return egraph.mkFalse( );

  // Retrieve interpolant from list of partial interpolants in case 
  // of theory lemma

  // Scan list partial interpolants
  for( int i = 1 ; i < curr_interp ; i++ )
    interp = interp->getCdr( );

  assert( interp->getCar( ) );
  return interp->getCar( );
}

void ProofGraph::printBits(uint64_t a)
{
  int i  , k , mask;

  for( i =63 ; i >= 0 ; i--)
  {
    //mask = 1 << i;
    mask=(uint64_t)pow(2,i);
    k = a & mask;
    if( k == 0)
      cout<<"0 ";
    else
      cout<<"1 ";
  }
  cout << endl;
}

#endif
