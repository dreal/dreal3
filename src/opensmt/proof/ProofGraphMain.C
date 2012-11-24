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

void ProofGraph::handleProof( )
{
#ifndef OPTIMIZE
  checkProof();
  cleanProofGraph();
  checkProof();
#endif

  if( produceProof() )
  {
    //Print original proof
    ofstream dotty( "proof.dot" );
    printProofAsDotty( dotty );

    if( reduceProof() > 0 )
    {
      //Reduce proof
      transfProof();

      //Print reduced proof
      ofstream dottyred( "proof_reduced.dot" );
      printProofAsDotty( dottyred );
    }
  }
  else if ( produceInterpolants() > 0 )
  {
    //Make sense to transform proof only if there are AB-mixed predicates
    if (!lightVars.empty())
    {
      transfProof();

      //Print reordered proof
      ofstream dottyre( "proof_reordered.dot" );
      printProofAsDotty( dottyre );
    }
  }
}

void ProofGraph::transfProof( )
{
  // Time left for transformation
  double leftTime = cpuTime( );

  size_t size=0;
  int numnodes=0;
  int numedges=0;
  int numleaves=0;
  int numvars=0;
  double avgdeg=0;
  int dia=0;
  int maxclasize=0;
  double avgclasize=0;
  int unsatcoredim=0;
  int numunary=0;
  double avgnumresunary=0;
  double avgnumres=0;
  int maxnumres=0;
  double varnumres=0;
  double varclasize=0;

  if ( verbose() )
  {
    getGraphInfo( );

    size = graph.size( );
    numnodes=num_nodes;
    numedges=num_edges;
    numleaves=num_leaves;
    numvars=numVars;
    avgdeg=(double)numedges / (double)numnodes;
    dia=diameter;
    maxclasize=max_cla_size;
    avgclasize=av_cla_size;
    unsatcoredim=dim_unsat_core;
    numunary=num_unary;
    avgnumresunary=avg_num_res_unary;
    avgnumres=avg_num_res;
    maxnumres=max_num_res;
    varnumres=var_num_res;
    varclasize=var_cla_size;
  }

  double time=0;

  if( produceProof() )
  {
    if ( reduceProof() > 0 )
    {
      time = doIt( leftTime );
    }
  }
  else if( produceInterpolants() > 0 )
  {
    //No need to transform proof if no AB-mixed predicate is present!
    assert(!lightVars.empty());

    if ( reorderPivots() > 0)
      time = doIt( leftTime );
    else
    {
      opensmt_error( "Cannot produce interpolants because of AB-mixed predicates. Please enable pivot reordering in config file" );
    }
  }

#ifndef OPTIMIZE
  checkProof();
  cleanProofGraph( );
  checkProof();
#endif
  if ( verbose() > 0 )
  {
    getGraphInfo( );

    double perc_nodes=(((double)num_nodes-(double)numnodes)/(double)numnodes)*100;
    double perc_edges=(((double)num_edges-(double)numedges)/(double)numedges)*100;
    double perc_leaves=(((double)num_leaves-(double)numleaves)/(double)numleaves)*100;
    double perc_unsatcore=(((double)dim_unsat_core-(double)unsatcoredim)/(double)unsatcoredim)*100;
    cerr << "#" << endl;
    cerr << "# ------------------------------------" << endl;
    cerr << "# PROOF GRAPH TRASFORMATION STATISTICS    " << endl;
    cerr << "# ------------------------------------" << endl;
    cerr << "# Structural properties" << endl;
    cerr << "# ---------------------" << endl;
    cerr << "# Light variables............: ";
    fprintf( stderr, "%-10ld\n", lightVars.size( ) );
    cerr << "# Nominal num proof variables: ";
    fprintf( stderr, "%-10ld\n", numVarsLimit );
    cerr << "# Actual num proof variables.: ";
    fprintf( stderr, "%-10d %-10d\n", numvars, numVars );
    cerr << "# Nodes......................: ";
    fprintf( stderr, "%-10d %-10d\n", numnodes, num_nodes );
    cerr << "# Nodes variation............: ";
    fprintf( stderr, "%-9.2f %%\n", perc_nodes );
    cerr << "# Leaves.....................: ";
    fprintf( stderr, "%-10d %-10d\n", numleaves, num_leaves );
    cerr << "# Leaves variation...........: ";
    fprintf( stderr, "%-9.2f %%\n", perc_leaves );
    cerr << "# Unsat core.................: ";
    fprintf( stderr, "%-10d %-10d\n", unsatcoredim, dim_unsat_core );
    cerr << "# Unsat core variation.......: ";
    fprintf( stderr, "%-9.2f %%\n", perc_unsatcore );
    cerr << "# Edges......................: ";
    fprintf( stderr, "%-10d %-10d\n", numedges, num_edges );
    cerr << "# Edges variation............: ";
    fprintf( stderr, "%-9.2f %%\n", perc_edges );
    cerr << "# Graph vector size..........: ";
    fprintf( stderr, "%-10ld %-10ld\n", size, graph.size( ) );
    cerr << "# Average degree.............: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgdeg, (double)num_edges / (double)num_nodes );
    cerr << "# Diameter...................: ";
    fprintf( stderr, "%-10d %-10d\n", dia, diameter );
    cerr << "# Unary clauses..............: ";
    fprintf( stderr, "%-10d %-10d\n", numunary, num_unary );
    cerr << "# Max clause size............: ";
    fprintf( stderr, "%-10d %-10d\n", maxclasize, max_cla_size );
    cerr << "# Average clause size........: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgclasize, av_cla_size );
    cerr << "# Variance clause size.......: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", varclasize, var_cla_size );
    cerr << "# Max num res................: ";
    fprintf( stderr, "%-10d %-10d\n", maxnumres, max_num_res );
    cerr << "# Average num res............: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgnumres, avg_num_res );
    cerr << "# Avg num res unary clauses..: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgnumresunary, avg_num_res_unary );
    cerr << "# Variance num res...........: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", varnumres, var_num_res );
    cerr << "# -------------------------" << endl;
    cerr << "# Transformation statistics" << endl;
    cerr << "# -------------------------" << endl;
    cerr << "# Graph building time........: " << building_time << " s" << endl;
    cerr << "# Transformation time........: " << time << " s" << endl;
    cerr << "# Duplications...............: " << num_dup << endl;
    cerr << "# Node additions due to A1...: " << num_node_add_A1 << endl;
    cerr << "# ---------------------------" << endl;
    cerr << "# Rules application statistics" << endl;
    cerr << "# ---------------------------" << endl;
    cerr << "# A1.........................: " << A1 << endl;
    cerr << "# A1 undo....................: " << A1Undo << endl;
    cerr << "# A1 to B....................: " << A1B << endl;
    cerr << "# A2.........................: " << A2 << endl;
    cerr << "# A2 to B....................: " << A2B << endl;
    cerr << "# A2 unary...................: " << A2U << endl;
    cerr << "# B1.........................: " << B1 << endl;
    cerr << "# B2.........................: " << B2 << endl;
    cerr << "# B2 killer..................: " << B2K << endl;
    cerr << "# B3.........................: " << B3 << endl;
    cerr << "# ---------------------------" << endl;
  }
}

double ProofGraph::doIt(double leftTime)
{
  size_t num_non_null;

  if ( verbose() > 0 )
  {
    num_non_null=0;
    for(size_t i=0;i<graph.size();i++)
      if(graph[i]!=NULL) num_non_null++;

    cerr << "#" << endl << "# Estimate of memory used before transformation" << endl;
    cerr << "# Size graph vector:" << graph.size() << " Memory for vector:" <<
      (graph.size()*sizeof(ProofNode*)) << endl;
    cerr << "# Nonnull nodes:" << num_non_null
      << " Memory for nodes: " << (num_non_null*sizeof(ProofNode))<< endl;
    cerr << "# Memory for visit vectors (preallocated):" << sizeof(std::bitset<SIZE_BIT_VECTOR>)*2 << endl << "#" << endl;
  }
  //Transformation time calculation
  double timeInit=0;
  double timeEnd=0;

  //Number of inner transformation loops
  //-1 for exhaustiveness
  int numTransfLoops;
  //Number of outer transformation loops
  //useful for alternation with recycle pivots
  int numGlobalLoops;
  // Time available for transformations
  // -1 for exhaustiveness
  double ratio;
  //Flag to be enabled (in case) for interpolation reordering
  //Postpones node duplications in swap rules until possible
  bool lessDuplMode;
  //Flag to enable transformations
  //Set to false in reduction if doing only recycle pivots and reconstruction
  bool doTransf;

  if(produceProof())
  {
    if ( reduceProof() > 0 )
    {
      if( ( ratioReductionSolvingTime() > 0 && reductionTime() > 0) ||
	  ( ratioReductionSolvingTime() == 0 && reductionTime() == 0)   )
      {
	cerr << "Please choose either ratio or time for reduction in config file" << endl;
	assert(false);
      }

      if( ratioReductionSolvingTime() > 0)
      {
	// Ratio transformation time/solving time
	ratio=ratioReductionSolvingTime();
	leftTime*=ratio;
      }
      if( reductionTime() > 0)
      {
	leftTime=reductionTime();
      }

      doTransf=true;
      numTransfLoops=-1;
      if (reductionLoops() == 0 )
      {
	cerr << "Please set number of reduction loops to at least 1 in config file" << endl;
	assert(false);
      }
      numGlobalLoops=reductionLoops();
      lessDuplMode=false;
      double recyTime=0,initTime=0;

      if ( verbose() > 0 )
      {
	cerr << "# Compressing proof, " << numGlobalLoops << " iteration(s) ->" << endl;
	cerr << "#" << endl;
      }

      //For each outer loop, recycle pivots algorithm is executed, followed by a certain
      //number of transformation loops, or by a single restructuring loop

      //Each global loop is given an equal fraction of available time
      const double share=leftTime/numGlobalLoops;
      timeInit=cpuTime();
      for(int k=0;k<numGlobalLoops;k++)
      {
	initTime=cpuTime();
	recyclePivotsIter();
	recyTime=cpuTime()-initTime;

	//Restructure graph, in case do also transformations
	transformAndRestructureOnTheFly(share-recyTime,doTransf,numTransfLoops,true);
      }
      timeEnd=cpuTime();
    }
  }
  else if( produceInterpolants() > 0 )
  {
    if ( verbose() > 0 )
    {
      cerr << "# Reordering pivots for interpolation ->" << endl;
      cerr << "#" << endl;
    }
    leftTime=-1;
    doTransf=true;
    numTransfLoops=-1;
    numGlobalLoops=2;
    lessDuplMode=false;

    timeInit=cpuTime();
    for(int k=0;k<numGlobalLoops;k++)
    {
      recyclePivotsIter();
      transformAndRestructureOnTheFly(leftTime,doTransf,numTransfLoops,lessDuplMode);
    }
    timeEnd=cpuTime();

#ifdef CHECK
    bool (ProofGraph::*ordering)(RuleContext&)=&ProofGraph::pushUpLightVarCriterionWeakOrdered;
    checkPivotOrdering(ordering);
#endif

    if ( removeMixedPredicates() > 0 )
    {
      cout << "MAGENTIFICATION" << endl;
      systematicMagentification();
      timeEnd=cpuTime();
#ifdef CHECK
      checkMagentification();
#endif
    }
  }

  if ( verbose() > 0 )
  {
    num_non_null=0;
    for(size_t i=0;i<graph.size();i++)
      if(graph[i]!=NULL) num_non_null++;

    cerr << "#" << endl << "# Estimate of memory used after transformation" << endl;
    cerr << "# Size graph vector:" << graph.size() << " Memory for vector:" <<
      (graph.size()*sizeof(ProofNode*)) << endl;
    cerr << "# Nonnull nodes:" << num_non_null
      << " Memory for nodes: " << (num_non_null*sizeof(ProofNode))<< endl;
    cerr << "# Memory for visit vectors (preallocated):" << sizeof(std::bitset<SIZE_BIT_VECTOR>)*2 << endl;
  }

  return (timeEnd-timeInit);
}

#endif
