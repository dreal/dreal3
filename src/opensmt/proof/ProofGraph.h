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

#ifndef PROOFGRAPH_H
#define PROOFGRAPH_H

#include "ProofGlobal.h"
#include "Proof.h"
#include "Enode.h"
#include "CoreSMTSolver.h"
#include <deque>
#include <algorithm>
#include <limits>
#include <bitset>

//#define CHECK //For general checking

//Predetermined max size of visit vectors
#define SIZE_BIT_VECTOR 7000000

//Types of clauses
//NB: CLADERIVED are distinct from CLALEARNED during solving, that are the root of the initial subproofs
enum clause_type {CLAORIG,CLALEMMA,CLAAXIOM,CLALEARNT,CLAMAGENTA,CLADERIVED};

//Types of rules
//ru is specific for pushing down unit clauses
//rb is specific for pushing down original clauses
//rp is specific for good/bad pivot rule
enum rul_type {rA1,rA2,rA2u,rB2k,rB3,rB1,rB2,rA1B,rA2B,rA1undo,rB,rNO,ru,ru2,rb,rp,rANY};

//Rules applicability info
//Five nodes context plus type of applicable rule
class RuleContext {
public:
	rul_type type;
	clauseid_t cv1;
	clauseid_t cv2;
	clauseid_t cw;
	clauseid_t cv3;
	clauseid_t cv;
	RuleContext(): type(rNO),cv1(-1),cv2(-1),cw(-1),cv3(-1),cv(-1){};
	~RuleContext(){};
	void reset(){type=rNO;cv1=-1;cv2=-1;cw=-1;cv3=-1;cv=-1;}
};


// Resolution proof graph element
class ProofNode {
public:
	clauseid_t id;
	vector<Lit> clause;
	Var pivot;
	// Edges outgoing
	set<ProofNode *> res;
	// Set of pivots in its subtree
	// Edges to parents
	ProofNode * ant1;
	ProofNode * ant2;
	clause_type type; //BLU,GRE,RED,ORA,MAG
	//Can be useful: maximal and minimal length of paths to sink
	int max_dist_sink;
	int min_dist_sink;
	//Enode to store partial interpolant
	Enode * partial_interp;
	//Partition mask for interpolation
	uint64_t partition_mask;

	ProofNode(): id(),clause(),pivot(),res(),ant1(NULL),ant2(NULL),max_dist_sink(0),min_dist_sink(std::numeric_limits<int>::max()),partial_interp(NULL),partition_mask(0){};
	~ProofNode(){};

	inline void addResolvent(ProofNode* resol){ res.insert(resol);}
	inline void remResolvent(ProofNode* resol){ res.erase(resol); }
	inline void setAnt1(ProofNode * a1){ ant1=a1; }
	inline void setAnt2(ProofNode * a2){ ant2=a2; }
	inline void setType(clause_type t){ type=t; }
	inline void setPivot(Var v){ pivot=v; }
	inline bool isLeaf(){ assert((ant1==NULL && ant2==NULL) || (ant1!=NULL && ant2!=NULL)); return ant1==NULL;}
};

class CoreSMTSolver;
class Proof;

class ProofGraph
{
public:

	ProofGraph  ( SMTConfig &     c
			, CoreSMTSolver & s
			, THandler * th
			, Egraph & e
			, Proof &        t
			, set< int > &    a
			, int             f
			, clauseid_t      g = clause_id_null
			, int             n = -1 )
	: config ( c )
	, solver ( s )
	, thandler ( th )
	, egraph ( e )
	{
		buildProofGraph( t, a, f, g, n );
	}

	~ProofGraph ( );

	void handleProof					 ( );
	void transfProof           ( );
	void printProofAsDotty     ( ostream & );
	void initializeLightVarSet ( set< Var > & );
	void produceSequenceInterpolants( vector<Enode*> &, bool);
	Enode * genPartialInterp( ProofNode*, int, uint64_t, uint64_t , bool );
	Enode * getPartialInterp( ProofNode*, int );
	void restrictClauseToB(ProofNode*, uint64_t, uint64_t, vector<Lit>& );
	opensmt::CGCOLOR getVarColor(Var, uint64_t, uint64_t);
	opensmt::CGCOLOR getClauseColor(ProofNode *, uint64_t, uint64_t);
	void systematicMagentification();

	//Various auxiliary functions
	inline int verbose(){ return config.verbosity; }
	inline int reorderPivots(){ return config.proof_reorder_pivots; }
	inline int reduceProof() { return config.proof_reduce; }
	inline int produceInterpolants() { return config.produce_inter; }
	inline int produceProof() { return config.produce_proofs; }
	inline double ratioReductionSolvingTime() { return config.proof_ratio_red_solv; }
	inline double reductionTime() { return config.proof_red_time; }
	inline double reductionLoops() { return config.proof_red_trans; }
	inline int removeMixedPredicates() { return config.proof_remove_mixed; }
	inline int numABMixedPredicates() { return lightVars.size(); }
	inline size_t graphSize( ) { return graph.size( ); }

private:

	void buildProofGraph   (
			Proof &
			, set< int > &, int, clauseid_t, int );

	int cleanProofGraph       ( );
	bool magentification(clauseid_t);
	//TODO turn into node destructor
	void removeNode(clauseid_t);
	void removeTree(clauseid_t);
	void dupliClause(clauseid_t,clauseid_t);

	//Literal comparisons functions
	inline bool litLess(Lit& l1, Lit& l2){if(var(l1)<=var(l2))return true; else return false;};
	inline bool litEq(Lit& l1, Lit& l2){if(var(l1)==var(l2) && sign(l1)==sign(l2) )return true; else return false;};

	bool ruleApply(RuleContext&,bool);
	bool getApplContext(clauseid_t,clauseid_t,RuleContext&);
	bool binSearch(vector<Lit>&, Var, bool&);
	void restoreAntPolarity(clauseid_t, Var);

	bool pushUpLightVarCriterionWeak(RuleContext&,bool);
	bool pushUpLightVarCriterionStrong(RuleContext&,bool);

	bool mergeClauses(vector<Lit>&, vector<Lit>&, vector<Lit>&, Var);

	void printProofNode(clauseid_t);
	void printContext(RuleContext&);
	void printStatus();
	void checkClause(clauseid_t);
	void checkClauseSorting(clauseid_t);
	void checkProof();
	void checkClauseDuplicates();
	void getGraphInfo();
	void printClause(ProofNode*);
	void printSMTClause(ProofNode*);
	void printBits(uint64_t);
	void topolSorting(vector<clauseid_t>&);

	void checkPivotOrdering(bool(ProofGraph::*ordered)(RuleContext&));
	bool pushUpLightVarCriterionWeakOrdered(RuleContext&);
	void checkMagentification();

	void normalizeProof();
	void checkNormality();

	//Transformations on the fly via topological sorting
	void transformAndRestructureOnTheFly(double,bool,int,bool);
	short chooseTransfEdgeOnTheFly(RuleContext&,RuleContext&,bool(ProofGraph::*allowed)(RuleContext&, bool),bool);
	short chooseOnTheFlyRed(RuleContext&,RuleContext&,bool(ProofGraph::*allowed)(RuleContext&, bool));
	bool redOntheFlyCriterion(RuleContext&, bool);
	double recyclePivotsIter();

	double doIt(double);

	//Interface objects
	SMTConfig &     config;
	CoreSMTSolver & solver;
	THandler * thandler;
	Egraph & egraph;

	//Graph
	vector< ProofNode * > graph;
	//Time spent building graph
	double building_time;
	//Bitsets used for graph visits
	std::bitset<SIZE_BIT_VECTOR> visited;
	std::bitset<SIZE_BIT_VECTOR> visited2;
	//Set of light variables that can be pushed up
	set<Var> lightVars;
	//Proof root
	clauseid_t root;
	//Number of variables nominal
	int numVarsLimit;
	//Number of variables actual
	int numVars;
	//Info on number of applied rules
	int A1,A2,A2U,B1,B2,B2K,B3,A1B,A2B,A1Undo;
	//Info on graph dimension
	int num_nodes;
	int num_edges;
	int num_unary;
	double avg_num_res_unary;
	int num_leaves;
	//Info on graph structure
	int diameter;     // Max length over min paths leaf->root
	//Info on clauses
	double av_cla_size;
	double var_cla_size;
	int max_cla_size;
	double avg_num_res;
	double var_num_res;
	int max_num_res;
	int dim_unsat_core;
	//Count node duplications made while applying rules
	int num_dup;
	//Count addition of nodes due to A1 applications
	int num_node_add_A1;
};

#endif

#endif
