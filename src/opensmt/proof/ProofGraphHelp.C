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

// Linear merge for resolution
bool ProofGraph::mergeClauses(vector<Lit>& A, vector<Lit>& B, vector<Lit>& res, Var pivot)
{
  res.clear();
  size_t i, j;
  i = 0;
  j = 0;
  bool rep;
  size_t Asize= A.size();
  size_t Bsize= B.size();
  size_t ressize=0;

  //Insert first element
  if(var(A[i])==pivot) i++;
  if(var(B[j])==pivot) j++;
  if(i < Asize && j < Bsize) {
    if (litLess(A[i],B[j])) {
      if(var(A[i])!=pivot){ res.push_back(A[i]); ressize++; }
      i++;
    }
    else {
      if(var(B[j])!=pivot){ res.push_back(B[j]); ressize++; }
      j++;
    }
  }
  else if (i < Asize) {
    if(var(A[i])!=pivot){ res.push_back(A[i]); ressize++; }
    i++;
  }
  else if (j< Bsize) {
    if(var(B[j])!=pivot){ res.push_back(B[j]); ressize++; }
    j++;
  }

  //Insert further elements avoiding repetitions
  while (i < Asize && j < Bsize) {
    if (litLess(A[i],B[j])) {
      rep=(var(A[i])==var(res[ressize-1]) && sign(A[i])==sign(res[ressize-1]));
      if(var(A[i])!=pivot && !rep){ res.push_back(A[i]); ressize++; }
      i++;
    } else {
      rep=(var(B[j])==var(res[ressize-1]) && sign(B[j])==sign(res[ressize-1]));
      if(var(B[j])!=pivot && !rep){ res.push_back(B[j]); ressize++; }
      j++;
    }
  }
  if (i < Asize)
    for (size_t p = i; p < Asize; p++)
    {
      rep=(var(A[p])==var(res[ressize-1]) && sign(A[p])==sign(res[ressize-1]));
      if(var(A[p])!=pivot && !rep){ res.push_back(A[p]); ressize++; }
    }
  else if(j < Bsize)
    for (size_t p = j; p < Bsize; p++)
    {
      rep=(var(B[p])==var(res[ressize-1]) && sign(B[p])==sign(res[ressize-1]));
      if(var(B[p])!=pivot && !rep){ res.push_back(B[p]); ressize++; }
    }
#ifdef CHECK
  assert(ressize==res.size());
#endif
  return true;
}


//Transform proof so to have at each resolution step the positive occurrence of the pivot
//in ant1 and the negative in ant2
void ProofGraph::normalizeProof()
{
  ProofNode* aux;
  bool signPivAnt1=false;
  bool signPivAnt2=false;
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
	    break;
	  }
      }
      if(graph[i]->ant2!=NULL)
      {
	for(size_t j=0; j< graph[i]->ant2->clause.size(); j++)
	  if(var(graph[i]->ant2->clause[j])==pivot)
	  {
	    signPivAnt2=sign(graph[i]->ant2->clause[j]);
	    break;
	  }
      }
      //Ant 1 negative while ant 2 positive
      if(signPivAnt1 && !signPivAnt2)
      {
	aux=graph[i]->ant1;
	graph[i]->ant1=graph[i]->ant2;
	graph[i]->ant2=aux;
      }
    }
}

//
// Prints resolution proof graph to a dot file,
// with proper colors
//
void ProofGraph::printProofAsDotty( ostream & out )
{
  // Visited nodes vector
  vector< bool > visited( graph.size( ), false );
  // Visit proof graph from sink via DFS
  vector< ProofNode * > q;
  q.push_back(graph[root]);

  out << "digraph proof {" << endl;

  while( !q.empty( ) )
  {
    ProofNode * node = q.back( );
    // Remove node
    q.pop_back( );
    // Node not yet visited
    if( !visited.at( node->id ) )
    {
      //Clean
      //clauseSort(node->clause);
      // Print node
      //0 if original, 1 if lemma, 2 if axiom inst, 3 if deduced, 4 if magenta
      string typ;
      string color="";
      switch( node->type )
      {
	case 0:
	  {
	    typ = "cls_";
	    out << typ << node->id << "[shape=plaintext, label=\"c" << node->id <<"  :  ";
	    solver.printSMTClause( out, node->clause, true );
	    out << "\", color=\"blue\", fontcolor=\"white\", style=\"filled\"]" << endl;
	  }
	  break;
	case 1:
	  {
	    typ = "lem_";
	    out << typ << node->id << " [shape=plaintext, label=\"c"<< node->id <<"  :  ";
	    solver.printSMTClause( out, node->clause, true );
	    out << "\", color=\"green\"";
	    out << ", style=\"filled\"]" << endl;
	  }
	  break;
	case 2:
	  {
	    typ = "axi_";
	    out << typ << node->id << " [shape=plaintext, label=\"c"<< node->id <<"  :  ";
	    solver.printSMTClause( out, node->clause, true );
	    out << "\", color=\"red\"";
	    out << ", style=\"filled\"]" << endl;
	  }
	  break;
	case 3:
	  {
	    typ = "ded_";
	    out << typ << node->id << " [shape=plaintext, label=\"c"<< node->id <<"  :  ";
	    if( !node->clause.empty( ) )
	      solver.printSMTClause( out, node->clause, true );
	    else out << "+"; // learnt clause
	    //out << "\", color=\"grey\"";
	    out << "\", color=\"orange\"";
	    out << ", style=\"filled\"]" << endl;
	  }
	  break;
	case 4:
	  {
	    typ = "mag_";
	    out << typ << node->id << " [shape=plaintext, label=\"c"<< node->id <<"  :  ";
	    if( !node->clause.empty( ) )
	      solver.printSMTClause( out, node->clause, true );
	    else out << "+"; // magenta clause
	    out << "\", color=\"purple\"";
	    out << ", style=\"filled\"]" << endl;
	  }
	  break;
	case 5:
	  {
	    typ = "der_";
	    out << typ << node->id << " [shape=plaintext, label=\"c"<< node->id <<"  :  ";
	    if( !node->clause.empty( ) )
	      solver.printSMTClause( out, node->clause, true );
	    else out << "+"; // internal ded clause clause
	    out << "\", color=\"orange\"";
	    out << ", style=\"filled\"]" << endl;
	  }
	  break;
	default: typ=""; break;
      }

      // Print edges from parents (if existing)
      string t1,t2;
      ProofNode * r1 = node->ant1;
      ProofNode * r2 = node->ant2;
      if( r1 != NULL && r2 != NULL)
      {
	switch( r1->type )
	{
	  case 0: t1 = "cls_"; break;
	  case 1: t1 = "lem_"; break;
	  case 2: t1 = "axi_"; break;
	  case 3: t1 = "ded_"; break;
	  case 4: t1 = "mag_"; break;
	  case 5: t1 = "der_"; break;
	  default: t1 = ""; break;
	}
	switch(r2->type)
	{
	  case 0: t2 = "cls_"; break;
	  case 1: t2 = "lem_"; break;
	  case 2: t2 = "axi_"; break;
	  case 3: t2 = "ded_"; break;
	  case 4: t2 = "mag_"; break;
	  case 5: t2 = "der_"; break;
	  default: t2 = ""; break;
	}

	out << t1 << r1->id << " -> " << typ << node->id;
	out << " [label=\"(" << node->pivot << ")\", fontsize=10]" << endl;
	out << t2 << r2->id << " -> " << typ << node->id;
	out << " [label=\"(" << node->pivot << ")\", fontsize=10]" << endl;

	// Enqueue parents
	q.push_back( r1 );
	q.push_back( r2 );
      }
      //Mark node as visited
      visited[ node->id ] = true;
    }
  }
  out << "}" << endl;
}

//Look for a variable in a clause
//If found, return true and sign of variable
//clause is assumed to be consistent
bool ProofGraph::binSearch(vector<Lit>& clause, Var piv, bool& sig)
{
  int mid,low,high;
  low=0; high=clause.size()-1;
  Lit l; Var v;

  while(low<=high)
  {
    mid=(low+high)/2;
    l=clause[mid];
    v=var(l);

    if( v == piv ){
      sig=sign(l);
      return true;
    }
    else if ( v > piv )
      high=mid-1;
    else
      low=mid+1;
  }
  return false;
}


//Calculate graph info
void ProofGraph::getGraphInfo()
{
  //Visit graph from sink keeping track of edges and nodes
  std::deque<ProofNode*> q;
  ProofNode* n;

  av_cla_size=0;
  max_cla_size=0;
  var_cla_size=0;
  avg_num_res=0;
  var_num_res=0;
  max_num_res=0;
  dim_unsat_core=0;
  num_nodes=0;
  num_edges=0;
  diameter=0;
  num_unary=0;
  avg_num_res_unary=0;
  num_leaves=0;


  q.push_back(graph[root]);
  graph[root]->min_dist_sink=0;
  do
  {
    n=q.front();
    q.pop_front();

    //Update info on parents, given info on node
    if(n->ant1!=NULL || n->ant2!=NULL)
    {
      if(n->ant1!=NULL)
      {
	if(n->ant1->min_dist_sink > n->min_dist_sink + 1)
	  n->ant1->min_dist_sink = n->min_dist_sink + 1;
	if(n->ant1->max_dist_sink < n->max_dist_sink + 1)
	  n->ant1->max_dist_sink = n->max_dist_sink + 1;
      }
      if(n->ant2!=NULL)
      {
	if(n->ant2->min_dist_sink > n->min_dist_sink + 1)
	  n->ant2->min_dist_sink = n->min_dist_sink + 1;
	if(n->ant2->max_dist_sink < n->max_dist_sink + 1)
	  n->ant2->max_dist_sink = n->max_dist_sink + 1;
      }
    }
    //Leaf reached; update global info
    else
    {
      if (diameter < n->min_dist_sink)
	diameter=n->min_dist_sink;
    }

    //Node not visited yet
    if(!visited[n->id])
    {
      if(n->ant1!=NULL || n->ant2!=NULL)
      {
	if(n->ant1!=NULL)
	{
	  q.push_back(n->ant1);
	  num_edges++;
	}
	if(n->ant2!=NULL)
	{
	  q.push_back(n->ant2);
	  num_edges++;
	}
      }
      else
	num_leaves++;

      //Mark node as visited
      visited[n->id]=true;
      num_nodes++;
      av_cla_size+=n->clause.size();
      avg_num_res+=n->res.size();
      if(n->clause.size() > (size_t)max_cla_size) max_cla_size=n->clause.size();
      if(n->res.size() > (size_t)max_num_res) max_num_res=n->res.size();
      if(n->type==CLAORIG) dim_unsat_core++;
      if(n->clause.size()==1) {
	num_unary++;
	avg_num_res_unary+=n->res.size();
      }

    }
  }
  while(!q.empty());

  if(num_unary>0)avg_num_res_unary/=num_unary;
  avg_num_res/=num_nodes;
  av_cla_size/=num_nodes;
  //Calculate sample variance for num resolvents and clause size
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL)
    {
      var_num_res+=pow(graph[i]->res.size()-avg_num_res,2);
      var_cla_size+=pow(graph[i]->clause.size()-av_cla_size,2);
    }
  var_num_res/=(num_nodes-1);
  var_cla_size/=(num_nodes-1);
  //Calculate sample variance for clause size
  visited.reset();

  // Determine actual set of variables
  set<Var> ps;
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL && graph[i]->ant1!=NULL && graph[i]->ant2!=NULL)
      ps.insert(graph[i]->pivot);
  numVars=ps.size();

}

void ProofGraph::topolSorting(vector<clauseid_t>& DFS)
{
  vector<clauseid_t>q;
  ProofNode* n;
  DFS.clear();
  clauseid_t c;

  q.push_back(root);
  do
  {
    c=q.back();
    n=graph[c];
    assert(n!=NULL);
    //Node not visited yet
    if(!visited2[c])
    {
      //Enqueue antecedents
      if(n->ant1!=NULL && !visited2[n->ant1->id])q.push_back(n->ant1->id);
      else if(n->ant2!=NULL && !visited2[n->ant2->id])q.push_back(n->ant2->id);
      //Mark node as visited if both antecedents visited
      else
      {
	visited2[c]=true;
	q.pop_back();
	DFS.push_back(c);
      }
    }
    else
      q.pop_back();
  }
  while(!q.empty());

  visited2.reset();
}

#endif
