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

//************************* RECYCLE PIVOTS AND RECYCLE UNITS ***************************

double ProofGraph::recyclePivotsIter()
{
  double initTime=cpuTime();
  clauseid_t c;
  vector<clauseid_t> q;

  int currPosition;
  Var targetPiv,curPiv;
  ProofNode *targetNode,*curNode,*curNodeOtherAnt;
  bool curNodeOtherAntPol,targetNodeAnt1Pol,cutAnt1,replaced;
  bool found1,found2;

  q.push_back(root);
  do
  {
    c=q.back();
    targetNode=graph[c];
    assert(targetNode!=NULL);
    replaced=false;

    //Node not visited yet
    //NB nodes visited only once on a single incoming path from sink
    if(!visited[c])
    {
      visited[c]=true;

      //Both antecedents present
      //Target node can be substituted only if it has one resolvent
      if(targetNode->ant1!=NULL && targetNode->ant2!=NULL && targetNode->res.size()==1)
      {
#ifdef CHECK
	assert(graph[targetNode->ant1->id]!=NULL);
	assert(graph[targetNode->ant2->id]!=NULL);
#endif
	//Look for current node pivot along the path to the sink
	//stop if found node with same pivot or multiple resolvents
	targetPiv=targetNode->pivot;
	//Start from node before the current one
	currPosition=q.size()-2;
	while(currPosition>=0 && !replaced)
	{
	  curNode=graph[q[currPosition]];
	  assert(curNode!=NULL);
	  assert( (curNode->ant1==graph[q[currPosition+1]]) || (curNode->ant2==graph[q[currPosition+1]]) );
	  curPiv=curNode->pivot;
	  //Found pivot redundancy
	  if(curPiv==targetPiv)
	  {
	    found1=false;
	    //Check polarity pivot in target node antecedents
	    for(size_t k=0;k<targetNode->ant1->clause.size();k++)
	      if(var(targetNode->ant1->clause[k])==curPiv)
	      {
		if(sign(targetNode->ant1->clause[k]))
		  targetNodeAnt1Pol=false;
		else if(!(sign(targetNode->ant1->clause[k])))
		  targetNodeAnt1Pol=true;
		else assert(false);
		found1=true;
		break;
	      }
	    if(!found1)assert(false);

	    //Determine current node antecedent not in current path
	    if(curNode->ant1 == graph[q[currPosition+1]])
	      curNodeOtherAnt=curNode->ant2;
	    else if(curNode->ant2 == graph[q[currPosition+1]])
	      curNodeOtherAnt=curNode->ant1;
	    else assert(false);
#ifdef CHECK
	    assert(curNode->ant1!=NULL);
	    assert(curNode->ant2!=NULL);
	    assert(graph[curNodeOtherAnt->id]!=NULL);
#endif

	    found2=false;
	    //Check polarity pivot in current node antecedent not in current path
	    for(size_t k=0;k<curNodeOtherAnt->clause.size();k++)
	      if(var(curNodeOtherAnt->clause[k])==curPiv)
	      {
		if(sign(curNodeOtherAnt->clause[k]))
		  curNodeOtherAntPol=false;
		else if(!(sign(curNodeOtherAnt->clause[k])))
		  curNodeOtherAntPol=true;
		else assert(false);
		found2=true;
		break;
	      }
	    if(!found2)
	    {
	      cout << "No more pivot for " << curNodeOtherAnt->id << " antecedent of "<< curNode->id << endl;
	      assert(false);
	    }

	    //NB a node st not both antecedents have its pivot
	    //is doomed to be substituted by the antecedent without pivot!
	    if(true/*found1 && found2*/)
	    {
	      replaced=true;

	      //Cut the proper target node antecedent
	      if(targetNodeAnt1Pol==curNodeOtherAntPol)
		cutAnt1=true;
	      else
		cutAnt1=false;

	      //ant1 loses n
	      targetNode->ant1->res.erase(targetNode);
	      //ant2 loses n
	      targetNode->ant2->res.erase(targetNode);
	      if(cutAnt1)
	      {
		//Ant2 substitutes node
		for(set<ProofNode*>::iterator it=targetNode->res.begin(); it!=targetNode->res.end(); it++)
		{
		  //Ant2 gains n resolvents
		  targetNode->ant2->res.insert((*it));

		  //Remove n from n resolvents antecedents, add ant2
		  if((*it)->ant1==targetNode) (*it)->ant1=targetNode->ant2;
		  else if((*it)->ant2==targetNode) (*it)->ant2=targetNode->ant2;
		  else assert(false);
		}
		targetNode->res.clear();
		//Remove ant1 if it has no more resolvents
		if(targetNode->ant1->res.size()==0) { removeTree(targetNode->ant1->id); targetNode->ant1=NULL; }

	      }
	      else
	      {
		//Ant1 substitutes node
		for(set<ProofNode*>::iterator it=targetNode->res.begin(); it!=targetNode->res.end(); it++)
		{
		  //ant1 gains n resolvents
		  targetNode->ant1->res.insert((*it));

		  //Remove n from n resolvents antecedents, add ant1
		  if((*it)->ant1==targetNode) (*it)->ant1=targetNode->ant1;
		  else if((*it)->ant2==targetNode) (*it)->ant2=targetNode->ant1;
		  else assert(false);
		}
		targetNode->res.clear();
		//Remove ant2 if it has no more resolvents
		if(targetNode->ant2->res.size()==0) { removeTree(targetNode->ant2->id); targetNode->ant2=NULL; }

	      }
	    }
	  }
	  //Stop loop if current node has multiple resolvents
	  if(graph[q[currPosition]]->res.size()>1)
	    break;
	  else currPosition--;
	}
      }
    }

    //If node visited, pivot found and cut done, replace current node on stack with the substituting antecedent
    if(replaced)
    {
      q.pop_back();
      if(cutAnt1)
	q.push_back(targetNode->ant2->id);
      else
	q.push_back(targetNode->ant1->id);
      removeNode(targetNode->id);
    }
    //Otherwise visit antecedents
    else
    {
      //If pivot not found enqueue antecedents if not visited
      if(targetNode->ant1!=NULL && !visited[targetNode->ant1->id])
	q.push_back(targetNode->ant1->id);
      else if(targetNode->ant2!=NULL && !visited[targetNode->ant2->id])
	q.push_back(targetNode->ant2->id);
      //Remove node if no antecedents or both antecedents already visited
      else
	q.pop_back();
    }
  }
  while(!q.empty());

  double endTime=cpuTime();

  if ( verbose() )
  {
    cout << "# " << "Recycle pivots done" << endl;
  }
  return (endTime-initTime);
}


//TODO
/*bool ProofGraph::recycleUnit(clauseid_t cid)
  {
#ifdef CHECK
assert(graph[cid]!=NULL);
assert(graph[cid]->clause.size()==1);
#endif

ProofNode* v;
clauseid_t c;
Var unaryVar;
bool signUnary;
std::deque<clauseid_t> q;
bool succ=false;

//Mark recursive antecedents of this derived unary
q.push_back(cid);
do
{
c=q.front();
v=graph[c];
q.pop_front();
if(!visited3[c])
{
visited3[c]=true;
if(v->ant1!=NULL && v->ant2!=NULL)
{
q.push_back(v->ant1->id);
q.push_back(v->ant2->id);
}
}
}
while(!q.empty());

unaryVar=var(graph[cid]->clause[0]);
signUnary=sign(graph[cid]->clause[0]);

//cout << "Working with unary clause " << cid << " with variable " << unaryVar << endl;

//Modify all the non marked non leaf nodes st pivot is the unary
//Bottom up strategy to cut as soon as possible
q.push_back(sink);
do
{
c=q.front();
v=graph[c];
q.pop_front();
#ifdef CHECK
assert(v!=NULL);
#endif
if(!visited4[c])
{
visited4[c]=true;
//Node is not antecedent of cid, has pivot=cid and does not derive from cid
if(!visited3[c] && v->ant1!=NULL && v->ant2!=NULL)
{
//cout << "Visiting " << c << " with pivot " << v->pivot << endl;

if(v->pivot==unaryVar && v->ant1->id!=cid && v->ant2->id!=cid)
{
//Modify antecedents
if(signUnary==true)
{
//cout << "Substituting " << v->ant1->id << " with " << cid << endl;
//Remove j from ant 1 resolvents
v->ant1->res.erase(v);
//Check if ant1 has no more resolvents
if(v->ant1->res.size()==0) removeTree(v->ant1->id);
//Update j antecedent
v->ant1=graph[cid];
//Add j to cid resolvents
graph[cid]->res.insert(v);
succ=true;
}
else if(signUnary==false)
{
  //cout << "Substituting " << v->ant2->id << " with " << cid << endl;
  //Remove j from ant2 resolvents
  v->ant2->res.erase(v);
  //Check if ant2 has no more resolvents
  if(v->ant2->res.size()==0) removeTree(v->ant2->id);
  //Update j antecedent
  v->ant2=graph[cid];
  //Add j to cid resolvents
  graph[cid]->res.insert(v);
  succ=true;
}
#ifdef CHECK
assert(v->ant1!=NULL);
assert(v->ant2!=NULL);
#endif
//Update clause
#ifdef TRACK_UNARY
if(v->clause.size()==1) unary.erase(v->id);
#endif
mergeClauses(v->ant1->clause, v->ant2->clause, v->clause, v->pivot);
#ifdef TRACK_UNARY
if(v->clause.size()==1) unary.insert(v->id);
#endif
//Propagate changes towards the bottom
//NB this call affects the bitset visited1/2 and reachable
subsumProp(v->id);
}
//If c is antecedent of cid, his antecedents are antecedent of cid themselves
q.push_back(v->ant1->id);
q.push_back(v->ant2->id);
}
}
}
while(!q.empty());

visited3.reset();
visited4.reset();
#ifdef CHECK
checkProof();
#endif
return succ;
}

//TODO improve strategy
void ProofGraph::recycleChainUnits()
{
  set<clauseid_t>::iterator it=unary.begin();
  clauseid_t c;

  do
  {
    c=(*it);
    if(graph[c]!=NULL)
    {
#ifdef CHECK
      assert(graph[c]->clause.size()==1);
#endif
      //TODO at the moment we go back to the start if the recycling is successful
      if(recycleUnitMine(c))
	it=unary.begin();
      else
	it++;
    }
  }
  while(it!=unary.end());
}

*/

//************************ REDUCTION AND PIVOT REORDERING *******************************

//Initializes the lightVar set with a set of light variables lightV
void ProofGraph::initializeLightVarSet(set<Var>& lightV)
{
  lightVars.swap(lightV);
  lightV.clear();
}

//Determine whether to apply a swap rule or not
bool ProofGraph::redOntheFlyCriterion(RuleContext& ra, bool duplAllowed)
{
  rul_type t=ra.type;
  bool dupl=(graph[ra.cw]->res.size()>1);

  if((dupl && duplAllowed) || (!dupl))
  {
    //Always allow rB2k
    if(t==rB2k) return true;
    //Allow A1 undo if no duplications
    if(t==rA1undo && !dupl) return true;
    //Allow A2 if no duplications
    if(t==rA2B && !dupl) return true;
    if((t==rA2 || t==rA2u) && !dupl) return true;
    //if(t==rA1B && !dupl) return true;
  }
  //Don't allow the rest
  return false;
}

//Given a set of light variables to be pushed up and a rule context, returns true if t1 is light and t0 heavy
//(which means that we are pushing up t1), false otherwise
bool ProofGraph::pushUpLightVarCriterionWeak(RuleContext& ra, bool duplAllowed)
{
  Var t0=graph[ra.cw]->pivot;
  Var t1=graph[ra.cv]->pivot;
  bool t0Light=(lightVars.find(t0)!=lightVars.end());
  bool t1Light=(lightVars.find(t1)!=lightVars.end());
  bool dupl=(graph[ra.cw]->res.size()>1);
  rul_type t=ra.type;

  if((dupl && duplAllowed) || (!dupl))
  {
    //Conditions added 30/07

    //Try to exploit A1undo in case pivots same partition
    if(t0Light && t1Light && t==rA1undo) return true;
    if(!t0Light && !t1Light && t==rA1undo) return true;

    //Try to delay A1s
    if(!duplAllowed && (t==rA1 || t==rA1B)) return false;

    if(!t0Light && t1Light) return true;
  }
  return false;
}

//Given a set of light variables to be pushed up and a rule context, returns true if t1 is light and t0 heavy
//or if both t0 and t1 are light/heavy (which means that we are pushing up t1), false otherwise
//NB This criterion is useful for B2 application, can cause loop for A2
bool ProofGraph::pushUpLightVarCriterionStrong(RuleContext& ra, bool duplAllowed)
{
  Var t0=graph[ra.cw]->pivot;
  Var t1=graph[ra.cv]->pivot;
  bool t0Light=(lightVars.find(t0)!=lightVars.end());
  bool t1Light=(lightVars.find(t1)!=lightVars.end());
  bool dupl=(graph[ra.cw]->res.size()>1);

  if((dupl && duplAllowed) || (!dupl))
  {
    if((!t0Light && t1Light) || (t0Light && t1Light) || (!t0Light && !t1Light)) return true;
  }
  return false;

}

//For pivot reordering
//Input: a pair of contexts
//Output: 0,1,2 to apply no rule, rule1, rule2
short ProofGraph::chooseTransfEdgeOnTheFly(RuleContext& ra1,RuleContext& ra2,bool(ProofGraph::*allowed)(RuleContext& ra, bool duplAll), bool duplAllowed)
{
  short choose=-1;
  rul_type t1=ra1.type;
  rul_type t2=ra2.type;
  bool all1,all2;
  bool is1cut=(t1==rB1 || t1==rB2 || t1==rB3);
  bool is2cut=(t2==rB1 || t2==rB2 || t2==rB3);
  bool is1swap=(t1==rA1 || t1==rA1B || t1==rA1undo || t1==rA2 || t1==rA2B || t1==rA2u || t1==rB2k);
  bool is2swap=(t2==rA1 || t2==rA1B || t2==rA1undo || t2==rA2 || t2==rA2B || t2==rA2u || t2==rB2k);

  //rA1,rA2,rA2u,rA1B,rA2B,rA1undo,rB2k,rB3,rB1,rB2

  //At least one is not applicable
  if(t1==rNO && t2==rNO) choose=0;
  else if(t1==rNO && t2!=rNO)
  {
    if(is2swap)
    {
      //Check ordering criterion
      if((*this.*allowed)(ra2,duplAllowed))
	choose=2;
      else choose=0;
    }
    else if(is2cut)
      choose=2;
    else
      assert(false);
  }
  else if(t1!=rNO && t2==rNO)
  {
    //Check ordering criterion
    if(is1swap)
    {
      if((*this.*allowed)(ra1,duplAllowed))
	choose=1;
      else choose=0;
    }
    else if(is1cut)
      choose=1;
    else
      assert(false);
  }
  if(choose!=-1) return choose;

  //Both are applicable
  bool dupl1=graph[ra1.cw]->res.size() > 1;
  bool dupl2=graph[ra2.cw]->res.size() > 1;

  //Case one cuts, the other swaps
  if(is1cut && is2swap)
    choose=1;
  else if(is2cut && is1swap)
    choose=2;
  //Case both cut
  else if(is1cut && is2cut)
  {
    //Privilege the one not duplicating
    if(dupl1 && !dupl2) choose=2;
    else if(!dupl1 && dupl2) choose=1;
    //Privilege B3
    else if(t1==rB3 && t2!=rB3) choose=1;
    else if(t1!=rB3 && t2==rB3) choose=2;
    //Break ties somehow
    else choose=1;
  }
  //Case both swap
  else if(is2swap && is1swap)
  {
    all1=(*this.*allowed)(ra1,duplAllowed);
    all2=(*this.*allowed)(ra2,duplAllowed);
    //At least one not allowed
    if(all1 && !all2) choose=1;
    else if(!all1 && all2) choose=2;
    else if(!all1 && !all2) choose=0;
    //Both allowed
    else
    {
      //Privilege the one not duplicating
      if(dupl1 && !dupl2) choose=2;
      else if(!dupl1 && dupl2) choose=1;
      //Privilege A1undo, then B2k, then A2 over A1
      else if(t1==rA1undo && t2!=rA1undo) choose=1;
      else if(t1!=rA1undo && t2==rA1undo) choose=2;
      else if(t1==rB2k && t2!=rB2k) choose=1;
      else if(t1!=rB2k && t2==rB2k) choose=2;
      else if((t1==rA2 || t1==rA2u || t1==rA2B) && (t2==rA1 || t2==rA1B)) choose=1;
      else if((t2==rA2 || t2==rA2u || t2==rA2B) && (t1==rA1 || t1==rA1B)) choose=2;
      //Privilege A2B over A2 and A1B over A1
      else if((t1==rA2B && (t2==rA2 || t2==rA2u)) || (t1==rA1B && t2==rA1)) choose=1;
      else if((t2==rA2B && (t1==rA2 || t1==rA2u)) || (t2==rA1B && t1==rA1)) choose=2;
      //Break ties somehow
      //else choose=1;
      else
      {
	//Give priority to push down leaves...can help linearize proof?
	bool pushDownLeaf1=false, pushDownLeaf2=false;

	if(graph[ra1.cv2]->ant1==NULL && graph[ra1.cv3]->ant1!=NULL) pushDownLeaf1=true;
	if(graph[ra2.cv2]->ant1==NULL && graph[ra2.cv3]->ant1!=NULL) pushDownLeaf2=true;
	if(pushDownLeaf1 && !pushDownLeaf2) choose=1;
	else if(pushDownLeaf2 && !pushDownLeaf1) choose=2;

	//Break ties randomly
	else
	  if(rand()%2==0)choose=1; else choose=2;
      }
    }
  }
  assert(choose!=-1);
  return choose;
}

//Iterative process:
// 1)Topological visit
// 2)Trasformations and restructuring top-down
void ProofGraph::transformAndRestructureOnTheFly(const double leftTime, const bool transf, const int maxnumloops, const bool lessDuplMode)
{
  //Queue for visit and propagation
  std::deque<clauseid_t> q;
  ProofNode* n;
  bool chooseLeft;
  set<ProofNode*>::iterator it;
  //Vector for topological ordering
  vector<clauseid_t> DFSv;
  //Flag to check if in a loop at least a transformation has been applied
  bool someTransfDone;
  long numLoops=0;
  RuleContext ra1,ra2;

  //Flag for the modality "no duplications until necessary" in reordering for interpolation
  bool duplAllowed;

  //Try to avoid duplications for swap rules until possible
  if(lessDuplMode)
    duplAllowed=false;
  else
    duplAllowed=true;

  //Swap rules application criterion
  bool (ProofGraph::*swapCriterion)(RuleContext&, bool);
  if ( reorderPivots() )
  {
    swapCriterion=&ProofGraph::pushUpLightVarCriterionWeak;
  }
  if ( reduceProof() )
  {
    swapCriterion=&ProofGraph::redOntheFlyCriterion;
  }
  double startTime=cpuTime();
  //Main loop: topological sorting followed by rule applications
  do
  {
    numLoops++;
    //Compute topological sorting of graph
    topolSorting(DFSv);

    /*		cout << "Topological " << DFSv.size() << endl;
		for(size_t k=0; k<DFSv.size(); k++)
		cout << DFSv[k] << " ";
		cout << endl;*/

#ifdef CHECK
    for(size_t i=0;i<DFSv.size();i++)
    {
      //Check that it is topological: antecedents do not appear after a node in sorting
      for(size_t j=i+1;j<DFSv.size();j++)
	assert((graph[DFSv[i]]->ant1==NULL || graph[DFSv[i]]->ant1->id!=DFSv[j])
	    && (graph[DFSv[i]]->ant2==NULL || graph[DFSv[i]]->ant2->id!=DFSv[j]));
    }
#endif

    someTransfDone=false;
    //Visit in topological order (while applying transformations)
    for(size_t i=0;i<DFSv.size();i++)
    {
      n=graph[DFSv[i]];

      //A node can have been removed before visit
      if(n!=NULL && n->ant1!=NULL && n->ant2!=NULL)
      {
	//Look for pivot in antecedents
	bool piv_in_ant1=false, piv_in_ant2=false;

	for(size_t i=0;i<n->ant1->clause.size();i++)
	  if(var(n->ant1->clause[i])==n->pivot)
	  { piv_in_ant1=true; break; }
	for(size_t i=0;i<n->ant2->clause.size();i++)
	  if(var(n->ant2->clause[i])==n->pivot)
	  { piv_in_ant2=true; break; }

	//Easy case: pivot still in both antecedents
	//Sufficient to propagate modifications via merge
	if(piv_in_ant1 && piv_in_ant2)
	{
	  //Update clause
	  mergeClauses(n->ant1->clause,n->ant2->clause,n->clause,n->pivot);
#ifdef CHECK
	  checkClause(n->id);
#endif
	  //This block is done only if transformations are enabled
	  if(transf)
	  {

	    //Look for rules applicability
	    getApplContext(n->ant1->id,n->id,ra1);
	    getApplContext(n->ant2->id,n->id,ra2);

	    //Decide which one to apply
	    short which=chooseTransfEdgeOnTheFly(ra1,ra2,swapCriterion,duplAllowed);
	    if(which!=0)
	    {
	      if(which==1)ruleApply(ra1,true);
	      else if(which==2)ruleApply(ra2,true);
	      someTransfDone=true;
	    }
	  }
	}
	//Intermediate case: pivot not in ant1(2) but in ant2(1)
	//Remove resolution step, remove n, ant1(2) gains n resolvents
	else if((!piv_in_ant1 && piv_in_ant2) || (piv_in_ant1 && !piv_in_ant2))
	{
	  //ant1 loses n
	  n->ant1->res.erase(n);
	  //ant2 loses n
	  n->ant2->res.erase(n);

	  if(!piv_in_ant1)
	  {
	    //cout << "Substituting ";printClause(n);
	    //cout << "with ";printClause(n->ant1);

	    for(it=n->res.begin(); it!=n->res.end(); it++)
	    {
	      //ant1 gains n resolvents
	      n->ant1->res.insert((*it));

	      //Remove n from n resolvents antecedents, add ant1
	      if((*it)->ant1==n) (*it)->ant1=n->ant1;
	      else if((*it)->ant2==n) (*it)->ant2=n->ant1;
	      else assert(false);
	    }
	    n->res.clear();
	  }
	  else if(!piv_in_ant2)
	  {
	    //cout << "Substituting ";printClause(n);
	    //cout << "with ";printClause(n->ant2);

	    for(it=n->res.begin(); it!=n->res.end(); it++)
	    {
	      //ant2 gains n resolvents
	      n->ant2->res.insert((*it));

	      //Remove n from n resolvents antecedents, add ant1
	      if((*it)->ant1==n) (*it)->ant1=n->ant2;
	      else if((*it)->ant2==n) (*it)->ant2=n->ant2;
	      else assert(false);
	    }
	    n->res.clear();
	  }

	  //Cut away trees not contributing anymore
	  //Remove ant2 if it has no more resolvents
	  if(!piv_in_ant1 && n->ant2->res.size()==0)
	  {removeTree(n->ant2->id); n->ant2=NULL;}
	  //Remove ant1 if it has no more resolvents
	  if(!piv_in_ant2 && n->ant1->res.size()==0)
	  {removeTree(n->ant1->id); n->ant1=NULL;}

	  //Substitute old sink with new
	  if(n->id==root)
	  {
	    if(!piv_in_ant1 && n->ant1->clause.size()==0) root=n->ant1->id;
	    if(!piv_in_ant2 && n->ant2->clause.size()==0) root=n->ant2->id;
	  }

	  //remove n
	  removeNode(n->id);
	}
	else if(!piv_in_ant1 && !piv_in_ant2)
	{
	  //Define heuristic to choose one of the two antecedents
	  //1) If an antecedent has only one resolvent, choose the other
	  //2) If both have only one resolvent, choose the smaller clause

	  if(n->ant1->res.size()==1 && n->ant2->res.size()>1) chooseLeft=false;
	  else if(n->ant1->res.size()>1 && n->ant2->res.size()==1) chooseLeft=true;
	  else
	  {
	    if(n->ant1->clause.size()>=n->ant2->clause.size()) chooseLeft=false;
	    else chooseLeft=true;
	  }

	  //ant1 loses n
	  n->ant1->res.erase(n);
	  //ant2 loses n
	  n->ant2->res.erase(n);

	  if(chooseLeft)
	  {
	    for(it=n->res.begin(); it!=n->res.end(); it++)
	    {
	      //ant1 gains n resolvents
	      n->ant1->res.insert((*it));

	      //Remove n from n resolvents antecedents, add ant1
	      if((*it)->ant1==n) (*it)->ant1=n->ant1;
	      else if((*it)->ant2==n) (*it)->ant2=n->ant1;
	      else assert(false);
	    }
	    n->res.clear();
	  }
	  else if(!chooseLeft)
	  {
	    for(it=n->res.begin(); it!=n->res.end(); it++)
	    {
	      //ant2 gains n resolvents
	      n->ant2->res.insert((*it));

	      //Remove n from n resolvents antecedents, add ant2
	      if((*it)->ant1==n) (*it)->ant1=n->ant2;
	      else if((*it)->ant2==n) (*it)->ant2=n->ant2;
	      else assert(false);
	    }
	    n->res.clear();
	  }
	  //We might have reached old sink
	  //Case legal only if we have produced another empty clause

	  //Cut away not contributing trees
	  //Remove ant2 if it has no more resolvents
	  if(chooseLeft && n->ant2->res.size()==0) { removeTree(n->ant2->id); n->ant2=NULL; }
	  //Remove ant1 if it has no more resolvents
	  if(!chooseLeft && n->ant1->res.size()==0) { removeTree(n->ant1->id); n->ant1=NULL; }
	  //Substitute old sink with new
	  if(n->id==root)
	  {
	    if(chooseLeft && n->ant1->clause.size()==0) root=n->ant1->id;
	    if(!chooseLeft && n->ant2->clause.size()==0) root=n->ant2->id;
	  }
	  //remove n
	  //NB: removed nodes can still be in the queue!
	  removeNode(n->id);
	}
      }
    }

    if(lessDuplMode)
    {
      //Flag for the modality "no duplications until necessary" in reordering for interpolation
      //If no transformations done without duplications, try enabling duplications
      if(!duplAllowed && !someTransfDone){ someTransfDone=true; duplAllowed=true; }
      //If transformations done with duplications, try disabling duplications
      else if(duplAllowed && someTransfDone){ duplAllowed=false; }
    }

  }
  //Continue until max number of loops reached or timeout or no more transformations done
  while((maxnumloops==-1? true:numLoops<maxnumloops) && (leftTime==-1? true:(cpuTime()-startTime)<=leftTime) && someTransfDone);

  if ( verbose() )
  {
    if(transf)
      cout << "# " << "Transformation loops done: " << numLoops << endl;
    else
      cout << "# " << "Restructuring done" << endl;
  }
}

#endif
