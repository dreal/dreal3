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

void ProofGraph::printProofNode(clauseid_t vid)
{
  ProofNode* v=graph[vid];
  if(v==NULL)
  {
    cerr << vid << " removed"<< endl<<endl;
    return;
  }
  cerr << "Node id: " << v->id << "   Type: " << v->type;
  if(v->ant1!=NULL && v->ant2!=NULL)
  {
    cerr << "   Parents: " << v->ant1->id << " " << v->ant2->id << "   Pivot: " << v->pivot;
  }
  cerr << "   Clause: ";
  for(size_t i=0;i<v->clause.size();i++)
  {
    if(sign(v->clause[i])) cerr << "~";
    cerr << var(v->clause[i]) << " ";
  }
  cerr << endl;
  cerr << "Sons: ";
  if(v->res.size()!=0)
  {
    for(set<ProofNode*>::iterator it=v->res.begin();it!=v->res.end();it++)
      cerr << (*it)->id << " ";
    cerr << endl;
  }
  cerr << endl;
}

//Prints info to check rule application effects
void ProofGraph::printContext(RuleContext& ra)
{
  cerr << "Context: " << endl ;
  cerr << "v "<< ra.cv;
  cerr << " - w "<< ra.cw;
  cerr << " - v3 "<< ra.cv3;
  cerr << " - v1 " << ra.cv1;
  cerr << " - v2 " << ra.cv2;
  cerr << " - type " ;
  //rA1,rA2,rA2u,rB2k,rB3,rB1,rB2,rA1B,rA2B,rA1undo,rB,rNO,ru,ru2,rb,rp,rANY
  switch(ra.type)
  {
    case 0:cout << "A1"; break;
    case 1:cout << "A2"; break;
    case 2:cout << "A2u"; break;
    case 3:cout << "B2k"; break;
    case 4:cout << "B3"; break;
    case 5:cout << "B1"; break;
    case 6:cout << "B2"; break;
    case 7:cout << "A1B"; break;
    case 8:cout << "A2B"; break;
    case 9:cout << "A1undo"; break;
    case 10:cout << "B"; break;
    case 11:cout << "NO"; break;
    default: break;
  }
  cout << endl ;
}

void ProofGraph::printClause(ProofNode* n)
{
  assert(n!=NULL);
  vector<Lit>& cl=n->clause;
  cout << n->id << ": ";
  for(size_t k=0;k<cl.size();k++)
  {
    if(sign(cl[k])) cout << "~";
    cout << var(cl[k]) << " ";
  }
  cout << endl;
}

void ProofGraph::printSMTClause(ProofNode* n)
{
	assert(n!=NULL);
	vector<Lit>& c=n->clause;
	cout << n->id << ": ";

	if ( c.size( ) == 0 ) cout << "-";
	if ( c.size( ) > 1 ) cout << "(or ";
	for (int i = 0; i < c.size(); i++)
	{
		Var v = var(c[i]);
		if ( v <= 1 ) continue;
		Enode * e = thandler->varToEnode( v );
		cout << (sign(c[i])?"(not ":"") << e << (sign(c[i])?") ":" ");
	}
	if ( c.size( ) > 1 ) cout << ")";
	cout << endl;
}

//TODO update
//Prints global info
void ProofGraph::printStatus()
{
  cerr 	<< "Rules applications - A1: "
    << A1 << "  A2: "
    << A2 << "  A2unary: "
    << A2U << "  B1: "
    << B1 << "  B2: "
    << B2 << "  B2killer: "
    << B2K << "  B3: "
    << B3
    << endl ;
  cerr 	<< "Duplications: "<< num_dup
    << "   Vector dimension: " << graph.size()
    << endl << endl;
}

void ProofGraph::checkClauseSorting(clauseid_t nid)
{
  ProofNode* n=graph[nid];
  assert(n!=NULL);
  assert(n->id==nid);

  if(n->clause.size()==0)return;

  for(size_t i=0;i<n->clause.size()-1;i++)
  {
    if(var(n->clause[i])>
	var(n->clause[i+1]))
    {
      cerr << "Bad clause sorting for clause " << n->id << " of type " << n->type << endl;
      printClause(n);
      assert(false);
    }
    if(var(n->clause[i])==var(n->clause[i+1]) && sign(n->clause[i])==sign(n->clause[i+1]))
    {
      cerr << "Repetition of var " << var(n->clause[i]) << " in clause " << n->id << " of type " << n->type << endl;
      printClause(n);
      assert(false);
    }
    if(var(n->clause[i])==var(n->clause[i+1]) && sign(n->clause[i])!=sign(n->clause[i+1]))
    {
      cerr << "Inconsistency on var " << var(n->clause[i]) << " in clause " << n->id << " of type " << n->type << endl;
      printClause(n);
      assert(false);
    }
  }
}

//Checks for various issues
//return false if issues present
void ProofGraph::checkClause(clauseid_t nid)
{
  ProofNode* n=graph[nid];
  assert(n!=NULL);
  assert(n->id==nid);

  //Check if empty clause
  if(n->id==root)
  {
    if(n->clause.size()!=0)
    {
      cerr << n->id << " is the sink but not an empty clause" << endl;
      printClause(n);
      assert(false);
    }
  }
  if(n->clause.size()==0)
  {
    if(n->id!=root)
    {
      cerr << n->id << " is an empty clause not sink" << endl;
      printClause(n);
      assert(false);
    }
  }
  else
  {
    checkClauseSorting(nid);
  }

  if(n->ant1==NULL && n->ant2!=NULL)
  {
    cerr << "Antecedent 1 null" << endl;
    assert(false);
  }
  if(n->ant1!=NULL && n->ant2==NULL)
  {
    cerr << "Antecedent 2 null" << endl;
    assert(false);
  }

  if(n->ant1!=NULL && n->ant2!=NULL)
  {
    assert(n->id != n->ant1->id && n->id !=n->ant2->id);

    vector<Lit> v;
    mergeClauses(n->ant1->clause,n->ant2->clause,v,n->pivot);
    if(v.size()!=n->clause.size())
    {
      cerr << "Clause " << nid << " does not correctly derive from antecedents "
	<< n->ant1->id << " " << n->ant2->id << " wrong size" << endl;
      cerr << "It is:     ";
      for(size_t i=0;i<n->clause.size();i++) cerr << var(n->clause[i]) << " ";
      cerr << endl;
      cerr << "Should be: ";
      for(size_t i=0;i<v.size();i++) cerr << var(v[i]) << " ";
      cerr << endl;
      assert(false);
    }
    for(size_t i=0;i<n->clause.size();i++)
      if(!litEq(n->clause[i],v[i]))
      {
	cerr << "Clause " << nid << " does not correctly derive from antecedents "
	  << n->ant1->id << " " << n->ant2->id << " wrong literal" << endl;
	cerr << "It is:     ";
	for(size_t i=0;i<n->clause.size();i++) cerr << var(n->clause[i]) << " ";
	cerr << endl;
	cerr << "Should be: ";
	for(size_t i=0;i<v.size();i++) cerr << var(v[i]) << " ";
	cerr << endl;
	assert(false);
      }
    assert(graph[n->ant1->id]!=NULL);
    assert(graph[n->ant2->id]!=NULL);
  }

  set<ProofNode*>::iterator it;
  ProofNode* r;
  for(it=n->res.begin();it!=n->res.end();it++)
  {
    r=(*it);
    if(graph[r->id]==NULL)
    {
      cerr << "Clause " << nid << " resolvent " << r->id << " does not exist anymore " << endl;
      assert(false);
    }
    assert(r->ant1==n || r->ant2==n);
  }
}

//Checks that the proof graph has no issues
void ProofGraph::checkProof()
{
  //Visit graph from sink keeping track of edges and nodes
  std::deque<ProofNode*> q;
  ProofNode* n;

  q.push_back(graph[root]);
  do
  {
    n=q.front();
    q.pop_front();
    //End current level, change level and set new end
    if(!visited[n->id])
    {
      checkClause(n->id);
      if(n->ant1!=NULL || n->ant2!=NULL)
      {
	if(n->ant1!=NULL)
	  q.push_back(n->ant1);
	if(n->ant2!=NULL)
	  q.push_back(n->ant2);
      }
      visited[n->id]=true;
    }
  }
  while(!q.empty());
  visited.reset();
}

//Checks if during transformations we come up with nodes with equal clauses
void ProofGraph::checkClauseDuplicates()
{
  int count=0;
  bool succ;

  cout << "# Checking for duplicates and subsumptions" << endl;

  for(size_t i=0;i<graph.size();i++)
    for(size_t j=i+1;j<graph.size();j++)
      if(graph[i]!=NULL && graph[j]!=NULL)
      {
	if(graph[i]->clause.size()==graph[j]->clause.size())
	{
	  succ=true;
	  for(size_t k=0;k<graph[i]->clause.size();k++)
	    if(!litEq(graph[i]->clause[k],graph[j]->clause[k]))
	    { succ=false; break;}
	  if(succ)
	  {
	    cerr << "Clause " << i << " of type " << graph[i]->type << " is equal to clause "
	      << j << " of type " << graph[j]->type << endl;
	    printClause(graph[i]);
	    printClause(graph[j]);
	    count++;
	  }
	}
      }
}

//Check if at each resolution step ant 1 has the positive occurrence of the pivot and ant2 the negative
void ProofGraph::checkNormality()
{
  bool signPivAnt1=false;
  bool signPivAnt2=true;
  Var pivot;

  for(size_t i=0; i<graph.size(); i++)
    if(graph[i]!=NULL && (graph[i]->ant1!=NULL || graph[i]->ant2!=NULL))
    {
      pivot=graph[i]->pivot;
      //Look for sign of pivots in antecedents
      if(graph[i]->ant1!=NULL)
      {
	for(size_t j=0; j< graph[i]->ant1->clause.size(); j++)
	  if(var(graph[i]->ant1->clause[j])==pivot)
	  {
	    signPivAnt1=sign(graph[i]->ant1->clause[j]);
	    //Ant 1, negative sign
	    if(signPivAnt1) assert(false);
	    break;
	  }
      }
      if(graph[i]->ant2!=NULL)
      {
	for(size_t j=0; j< graph[i]->ant2->clause.size(); j++)
	  if(var(graph[i]->ant2->clause[j])==pivot)
	  {
	    signPivAnt2=sign(graph[i]->ant2->clause[j]);
	    //Ant 2, positive sign
	    if(!signPivAnt2) assert(false);
	    break;
	  }
      }
    }
}

//Checks that the pivots are ordered in the right way along each path according to a pairwise ordering criterion
void ProofGraph::checkPivotOrdering(bool(ProofGraph::*ordered)(RuleContext& ra))
{
  //Visit graph from sink keeping track of edges and nodes
  std::deque<ProofNode*> q;
  ProofNode* n;
  set< pair<clauseid_t,clauseid_t> >::iterator it;
  RuleContext ra;

  q.push_back(graph[root]);
  do
  {
    n=q.front();
    q.pop_front();
    //End current level, change level and set new end
    if(!visited[n->id])
    {
      if(n->ant1!=NULL || n->ant2!=NULL)
      {
	//Look for edges in sets
	//Remember that v1 and v2 must be present for a rule to be applied
	if(getApplContext(n->ant1->id,n->id,ra))
	{
	  if(!(*this.*ordered)(ra))
	  {
	    assert(graph[ra.cw]==graph[ra.cv]->ant1 || graph[ra.cw]==graph[ra.cv]->ant2);
	    cerr << "Wrong ordering pivots: bottom clause " << ra.cv <<"(" << graph[ra.cv]->pivot
	      << ") \ttop clause " << ra.cw << "(" <<graph[ra.cw]->pivot << ")"<<endl;
	  }
	}

	//Remember that v1 and v2 must be present for a rule to be applied
	if(getApplContext(n->ant2->id,n->id,ra))
	{
	  if(!(*this.*ordered)(ra))
	  {
	    assert(graph[ra.cw]==graph[ra.cv]->ant1 || graph[ra.cw]==graph[ra.cv]->ant2);
	    cerr << "Wrong ordering pivots: bottom clause " << ra.cv <<"(" << graph[ra.cv]->pivot
	      << ") \ttop clause " << ra.cw << "(" <<graph[ra.cw]->pivot << ")"<<endl;
	  }
	}

	if(n->ant1!=NULL)
	  q.push_back(n->ant1);
	if(n->ant2!=NULL)
	  q.push_back(n->ant2);
      }
      visited[n->id]=true;
    }
  }
  while(!q.empty());
  visited.reset();
}

//Returns true if pivots in context are ordered according to the given criterion
bool ProofGraph::pushUpLightVarCriterionWeakOrdered(RuleContext& ra)
{
  Var t0=graph[ra.cw]->pivot;
  Var t1=graph[ra.cv]->pivot;
  bool t0Light=(lightVars.find(t0)!=lightVars.end());
  bool t1Light=(lightVars.find(t1)!=lightVars.end());

  if(!t0Light && t1Light) return false;
  else return true;
}

//Checks soundness of magentification
void ProofGraph::checkMagentification()
{
  cerr << "Set of light variables: ";
  for(set<Var>::iterator it=lightVars.begin();it!=lightVars.end(); it++)
    cerr << (*it) << " ";
  cerr << endl;
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL)
    {
      if(graph[i]->ant1==NULL && graph[i]->ant2==NULL)
      {
	if(graph[i]->type!=CLAMAGENTA && graph[i]->type!=CLAORIG)
	{
	  cerr << "Leaf " << i << " should be magenta" << endl;
	  assert(false);
	}
	if(graph[i]->type==CLAORIG)
	{
	  for(size_t j=0; j<graph[i]->clause.size(); j++)
	  {
	    if(lightVars.find(var(graph[i]->clause[j]))!=lightVars.end())
	    {
	      cerr << "Blue clause " << i << " contains light var " << var(graph[i]->clause[j]) << endl;
	      assert(false);
	    }
	  }
	}
      }
      else if(graph[i]->type!=CLALEARNT)
      {
	cerr << "Internal node " << i << " should be orange" << endl;
	assert(false);
      }
    }
}

#endif
