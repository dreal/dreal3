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

// Resolution proof builder
void
ProofGraph::buildProofGraph( Proof & proof
			   , set< int >& axioms_ids
			   , int final_root_id
			   , clauseid_t goal
			   , int nVars )
{
  const double initTime=cpuTime();

  A1=0;A2=0;A2U=0;B1=0;B2=0;B2K=0;B3=0;A1B=0;A2B=0;A1Undo=0;
  av_cla_size=0; max_cla_size=0;
  dim_unsat_core=0;
  num_edges=0;
  num_nodes=0;
  diameter=0;
  num_dup=0;
  num_leaves=0;
  num_node_add_A1=0;
  building_time=0;

  // Resolution tree for clause id; pairs <clause,pivot>
  // Structure:
  // a -
  // b c
  // ...
  // a,b resolved over c...
  map< Clause *, ProofDer * > & clause_to_proof_der = proof.getProof( );
  map< Clause *, ProofDer * >::iterator it;

  //To map clauses to graph id
  //An id is associated when the node is created
  map< Clause*, int> clauseToIDMap;

  //To keep track of visited nodes
  set<Clause*> visitedSet;

  //Queue to build proof graph from sink
  std::deque<Clause*> q;

  int currId,lastInternalId,id,id1,id2;
  ProofNode* n;

  //Start from empty clause
  q.push_back(NULL);
  do
  {
    //Get current clause
    Clause* currClause=q.back();
    q.pop_back();

    //Clause not visited yet
    if(visitedSet.find(currClause)==visitedSet.end())
    {
      //Get clause derivation tree
      ProofDer &           proofder = *(clause_to_proof_der[currClause]);
      vector< Clause * > & chaincla = (*(proofder.chain_cla));            // Clauses chain
      vector< Var > &      chainvar = (*(proofder.chain_var));            // Pivot chain
      clause_type_t        ctype    = proofder.type;

      // No derivation tree: theory lemma or original clause
      // Non empty clause
      if ( ctype==CLA_ORIG || ctype==CLA_THEORY )
      {
	assert(chaincla.size()==0 || chaincla.size()==1);
	assert(currClause!=NULL);

	//Strange case clause with link
	if(chaincla.size()>0)
	{
	  if(produceInterpolants()>0)
	    solver.setInterpolant( currClause, solver.getInterpolants( chaincla[0] ) ); 
	  // cout << "Clause with link, type " << proofder.type << endl;
	  // solver.printSMTClause(cout,*currClause);
	  // cout << endl;
	  // cout << "Link, type " << (*(clause_to_proof_der[chaincla[0]])).type << endl;
	  // solver.printSMTClause(cout,*(chaincla[0]));
	  // cout << chaincla[0] << endl;
	  // cout << endl;
	  //q.push_back(chaincla[0]);
	  //continue;
	}
	//Clause not processed yet
	if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
	{
	  n=new ProofNode();
	  for(int k=0;k<(*currClause).size();k++)
	    n->clause.push_back((*currClause)[k]);
	  //Add node to graph vector
	  currId=(int)graph.size();
	  n->id=currId;
	  graph.push_back(n);
	  assert(graph[currId]==n);
	  //Update map clause->id
	  clauseToIDMap[currClause]=currId;
	  //Sort clause literals
	  std::sort(n->clause.begin(),n->clause.end());

	  checkClauseSorting(n->id);
	}
	// NB: internal derived clauses not considered here
	//Original clause
	if(ctype==CLA_ORIG)
	{
	  graph[clauseToIDMap[currClause]]->type=CLAORIG;
	  //Determine partition mask in case of interpolation
	  if(produceInterpolants()>0)
	  {
	    graph[clauseToIDMap[currClause]]->partition_mask = solver.getIPartitions(currClause);
	    // cout << "Associating mask " << graph[clauseToIDMap[currClause]]->partition_mask << " to clause "; printClause(graph[clauseToIDMap[currClause]]);
	  }
	}
	//Theory clause
	else if (ctype==CLA_THEORY)
	{
	  graph[clauseToIDMap[currClause]]->type=CLALEMMA;
	  //Determine list of partial interpolants in case of theory lemma
	  if(produceInterpolants()>0)
	  {
	    // cout << "Associating partial interpolants list to clause "; printClause(graph[clauseToIDMap[currClause]]);
	    Enode* partial_interp_list = solver.getInterpolants(currClause);
	    assert(partial_interp_list);
	    graph[clauseToIDMap[currClause]]->partial_interp = partial_interp_list;
	  }
	}
	//TODO: how to distinguish between green and red???

      }
      // Learnt clause
      // Resolution tree present
      else if(ctype==CLA_LEARNT)
      {
	assert(chaincla.size() >= 2);
	// No internal deduced nodes
	if ( chaincla.size( ) == 2 )
	{
	  assert(chainvar.size()==1);
	  // First clause not yet processed
	  if(clauseToIDMap.find(chaincla[0])==clauseToIDMap.end())
	  {
	    n=new ProofNode();
	    for(int k=0;k<(*chaincla[0]).size();k++)
	      n->clause.push_back((*chaincla[0])[k]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->id=currId;
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[chaincla[0]]=currId;
	    //Add clause to queue
	    q.push_back(chaincla[0]);
	    //Sort clause literals
	    std::sort(n->clause.begin(),n->clause.end());

	    checkClauseSorting(n->id);
	  }
	  if(clauseToIDMap.find(chaincla[1])==clauseToIDMap.end())
	  {
	    ProofNode* n=new ProofNode();
	    for(int k=0;k<(*chaincla[1]).size();k++)
	      n->clause.push_back((*chaincla[1])[k]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->id=currId;
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[chaincla[1]]=currId;
	    //Add clause to queue
	    q.push_back(chaincla[1]);
	    //Sort clause literals
	    std::sort(n->clause.begin(),n->clause.end());

	    checkClauseSorting(n->id);
	  }

	  id1=clauseToIDMap[chaincla[0]];
	  id2=clauseToIDMap[chaincla[1]];
	  // Clause not yet processed
	  if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
	  {
	    ProofNode* n=new ProofNode();
	    mergeClauses(graph[id1]->clause,graph[id2]->clause,n->clause,chainvar[0]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->id=currId;
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[currClause]=currId;

	    checkClauseSorting(n->id);
	  }
	  id=clauseToIDMap[currClause];
	  // Setting edges, pivot, type
	  graph[id1]->res.insert(graph[id]);
	  graph[id2]->res.insert(graph[id]);
	  graph[id]->ant1=graph[id1];
	  graph[id]->ant2=graph[id2];
	  graph[id]->pivot=chainvar[0];
	  graph[id]->type=CLALEARNT;
	  //Sink check
	  if(currClause==NULL)
	    root=id;
	}
	else
	  // Yes internal deduced clauses
	{
	  if(clauseToIDMap.find(chaincla[0])==clauseToIDMap.end())
	  {
	    n=new ProofNode();
	    for(int k=0;k<(*chaincla[0]).size();k++)
	      n->clause.push_back((*chaincla[0])[k]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->id=currId;
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[chaincla[0]]=currId;
	    //Add clause to queue
	    q.push_back(chaincla[0]);
	    //Sort clause literals
	    std::sort(n->clause.begin(),n->clause.end());

	    checkClauseSorting(n->id);
	  }
	  for ( size_t i = 1 ; i < chaincla.size() ; i ++ )
	  {
	    if(clauseToIDMap.find(chaincla[i])==clauseToIDMap.end())
	    {
	      ProofNode* n=new ProofNode();
	      for(int k=0;k<(*chaincla[i]).size();k++)
		n->clause.push_back((*chaincla[i])[k]);
	      //Add node to graph vector
	      currId=(int)graph.size();
	      n->id=currId;
	      graph.push_back(n);
	      assert(graph[currId]==n);
	      //Update map clause->id
	      clauseToIDMap[chaincla[i]]=currId;
	      //Add clause to queue
	      q.push_back(chaincla[i]);
	      //Sort clause literals
	      std::sort(n->clause.begin(),n->clause.end());

	      checkClauseSorting(n->id);
	    }

	    if(i<chaincla.size()-1)
	    {
	      // Creation new internal deduced node
	      n=new ProofNode();
	      //Add node to graph vector
	      currId=(int)graph.size();
	      n->id=currId;
	      n->type=CLADERIVED;
	      n->pivot=chainvar[i-1];
	      graph.push_back(n);
	      assert(graph[currId]==n);

	      // Edges creation
	      if(i==1)
		// First internal node deduced from first clauses 0 and 1
	      {
		id1=clauseToIDMap[chaincla[0]];
		id2=clauseToIDMap[chaincla[1]];
		// Setting edges, type
		graph[id1]->res.insert(graph[currId]);
		graph[id2]->res.insert(graph[currId]);
		graph[currId]->ant1=graph[id1];
		graph[currId]->ant2=graph[id2];
		mergeClauses(graph[id1]->clause,graph[id2]->clause,n->clause,chainvar[0]);
		lastInternalId=currId;

		checkClauseSorting(n->id);
	      }
	      else
		// Other internal nodes deduced from clause i and last internal node
	      {
		id2=clauseToIDMap[chaincla[i]];
		graph[lastInternalId]->res.insert(graph[currId]);
		graph[id2]->res.insert(graph[currId]);
		graph[currId]->ant1=graph[lastInternalId];
		graph[currId]->ant2=graph[id2];
		mergeClauses(graph[id2]->clause,graph[lastInternalId]->clause,n->clause,chainvar[i-1]);
		lastInternalId=currId;

		checkClauseSorting(n->id);
	      }
	    }
	    // End tree reached: examining currClause
	    else
	    {
	      id2=clauseToIDMap[chaincla[i]];
	      if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
	      {
		n=new ProofNode();
		mergeClauses(graph[id2]->clause,graph[lastInternalId]->clause,n->clause,chainvar[i-1]);
		//Add node to graph vector
		currId=(int)graph.size();
		n->id=currId;
		graph.push_back(n);
		assert(graph[currId]==n);
		//Update map clause->id
		clauseToIDMap[currClause]=currId;

		checkClauseSorting(n->id);
	      }
	      id=clauseToIDMap[currClause];
	      // Setting edges, pivot, type
	      // Edges from last clause and last internal node
	      (graph[lastInternalId]->res).insert(graph[id]);
	      (graph[id2]->res).insert(graph[id]);
	      graph[id]->ant1=graph[lastInternalId];
	      graph[id]->ant2=graph[id2];
	      graph[id]->pivot=chainvar[i-1];
	      graph[id]->type=CLALEARNT;
	      //Sink check
	      if(currClause==NULL)
		root=id;
	    }
	  }
	}
      }
      //Mark clause as visited
      visitedSet.insert(currClause);
    }
  }
  while(!q.empty());

  if(graph.size()>SIZE_BIT_VECTOR)
  {
    cerr << "# Error: Number of nodes too large: " << graph.size() << " but limit is " << SIZE_BIT_VECTOR <<  endl;
    cerr << "# Error: Increase SIZE_BIT_VECTOR to " << graph.size() <<  endl;
    exit( 1 );
  }

  numVarsLimit=nVars;

  //Keep track of visited nodes
  visited.reset();

  building_time=cpuTime()-initTime;
  //checkClauseDuplicates();
}

//TODO Resolution proof destructor
ProofGraph::~ProofGraph()
{
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL)removeNode(i);
}

// Remove redundant pieces of the proof graph
//TODO implement destructor for ProofNodeFly
//returns number of redundant nodes removed
int ProofGraph::cleanProofGraph()
{
  // Visit proof graph from root via DFS
  vector<ProofNode*> q;
  q.push_back(graph[root]);
  int counter=0;

  // Determine the reachable part of the graph
  while(!(q.empty()))
  {
    ProofNode* node=q.back();
    // Remove node
    q.pop_back();
    // Node not yet visited
    if(!(visited[node->id]))
    {
      if(node->ant1!=NULL || node->ant2!=NULL)
      {
	//Enqueue antecedents
	if(node->ant1!=NULL)
	  q.push_back(node->ant1);
	if(node->ant2!=NULL)
	  q.push_back(node->ant2);
      }
      //Mark node as visited
      visited[node->id]=true;
    }
  }

  // Remove the unreachable part of the graph
  for(size_t i=0;i<graph.size();i++)
  {
#ifdef CHECK
    assert(!(visited[i] && graph[i]==NULL));
#endif
    if(!visited[i])
      if(graph[i]!=NULL)
      {
	removeNode(i);
	counter++;
	//cout << "Node " << i << " not reachable anymore has been removed" << endl;
	//assert(false);
      }
  }
  // Visited nodes vector
  visited.reset();
  return counter;
}

//Remove a node from the graph
void ProofGraph::removeNode(clauseid_t vid)
{
  ProofNode* v=graph[vid];
  assert(v!=NULL);

  //Remove v from the list of its antecedents resolvents
  ProofNode* ant1=v->ant1;
  ProofNode* ant2=v->ant2;
  if(ant1!=NULL || ant2!=NULL)
  {
    if(ant1!=NULL)
    {
      //cout << ant1->res.size() << endl;
      ant1->res.erase(v);
    }
    if(ant2!=NULL)
    {
      //cout << ant2->res.size() << endl;
      ant2->res.erase(v);
    }
  }
  //Remove v from its resolvents antecedents
  for(set<ProofNode*>::iterator it=v->res.begin();it!=v->res.end(); it++)
  {
    if((*it)->ant1==v) (*it)->ant1=NULL;
    if((*it)->ant2==v) (*it)->ant2=NULL;
  }
  v->ant1=NULL;
  v->ant2=NULL;
  //Remove interpolant, if any
  if(v->partial_interp!=NULL)
  {
    //delete(v->partial_interp);
    v->partial_interp=NULL;
  }
  //Free memory
  delete v;
  //Remove v
  graph[vid]=NULL;
}

//Remove a subtree radicated in a node v from the graph
void ProofGraph::removeTree(clauseid_t vid)
{
#ifdef CHECK
  assert(graph[vid]!=NULL);
  assert(graph[vid]->res.size()==0);
#endif
  //Go on removing nodes with 0 resolvents
  //Visit graph from root keeping track of edges and nodes
  std::deque<clauseid_t> q;

  ProofNode* n;
  clauseid_t c;

  q.push_back(vid);
  do
  {
    c=q.front();
    q.pop_front();
#ifdef CHECK
    assert((size_t)c<graph.size());
#endif
    //Node not visited yet
    if(!visited2[c])
    {
      n=graph[c];
#ifdef CHECK
      assert(n!=NULL);
#endif
      //Mark node as visited
      visited2[c]=true;
      //remove node if no more resolvents present
      if(n->res.size()==0)
      {
	if(n->ant1!=NULL)
	  q.push_back(n->ant2->id);
	if(n->ant2!=NULL)
	  q.push_back(n->ant1->id);

	removeNode(n->id);
      }
    }
  }
  while(!q.empty());
  visited2.reset();
}

//Collapses a deduced node with its red/green/magenta antecedents into a magenta node
//returns true if the node has been magentified
bool ProofGraph::magentification(clauseid_t nid)
{
  ProofNode* n=graph[nid];
#ifdef CHECK
  assert(n!=NULL);
#endif
  //Red and green nodes become magenta
  if(n->type==CLAAXIOM || n->type==CLALEMMA)
  {
    n->type=CLAMAGENTA;
    return true;
  }
  //NB We can have blu nodes containing light variables, due to preprocessing: they become magenta
  else if(n->type==CLAORIG)
  {
    for(size_t i=0; i<n->clause.size(); i++)
    {
      if(lightVars.find(var(n->clause[i]))!=lightVars.end())
      {
	n->type=CLAMAGENTA;
	return true;
      }
    }
  }
  //Orange nodes become magenta and antecedents are removed
  else if(n->ant1!=NULL && n->ant2!=NULL)
  {
    clause_type ty1=n->ant1->type;
    clause_type ty2=n->ant2->type;

    //Both antecedents are leaves
    if((ty1==CLALEMMA || ty1==CLAAXIOM || ty1==CLAMAGENTA) && (ty2==CLALEMMA || ty2==CLAAXIOM || ty2==CLAMAGENTA))
    {
      //Remove resolution step
      n->ant1->res.erase(n);
      n->ant2->res.erase(n);
      //If an antecedent has no more resolvents, remove it
      if(n->ant1->res.size()==0)
	removeNode(n->ant1->id);
      if(n->ant2->res.size()==0)
	removeNode(n->ant2->id);
      //cout << "Collapsing " << n->ant1->id << " and "<< n->ant2->id<< " into "<< n->id <<endl<<endl;
      //TODO: calculate removed leaves/nodes??

      //Update n
      n->type=CLAMAGENTA;
      n->ant1=NULL;
      n->ant2=NULL;
      return true;
    }
  }
  return false;
}

//Magentifies the graph iteratively
//TODO find better algorithm
void ProofGraph::systematicMagentification()
{
  bool done;
  do
  {
    done=false;
    for(size_t i=0;i<graph.size();i++)
      if(graph[i]!=NULL)
	done=done || magentification(i);
  }
  while(done);
}

#endif
