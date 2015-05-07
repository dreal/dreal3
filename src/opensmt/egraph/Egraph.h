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

#ifndef EGRAPH_H
#define EGRAPH_H

#include <unordered_map>
#include "egraph/Enode.h"
#include "sorts/SStore.h"
#include "tsolvers/TSolver.h"
#include "egraph/SigTab.h"
#include "common/SplayTree.h"
#include "util/flow.h"
#include "util/logging.h"

#ifdef PRODUCE_PROOF
#include "proof/UFInterpolator.h"
#endif

class Egraph : public CoreTSolver
{
public:

  Egraph( SMTConfig & c
        , SStore & s )
      : CoreTSolver       ( 0, "EUF Solver", c )
      , enil              ( new Enode )
      , sort_store        ( s )
      , active_dup1       ( false )
      , active_dup2       ( false )
      , dup_count1        ( 0 )
      , dup_count2        ( 0 )
      , active_dup_map1   ( false )
      , active_dup_map2   ( false )
      , dup_map_count1    ( 0 )
      , dup_map_count2    ( 0 )
      , has_ites          ( false )
      , congruence_running( false )
#ifdef PRODUCE_PROOF
      , iformula          ( 1 )
      , cgraph_           ( new CGraph( *this, config ) )
      , cgraph            ( *cgraph_ )
#endif
      , theoryInitialized ( false )
      , time_stamp        ( 0 )
      , use_gmp           ( false )
  {
    //
    // Initialize nil key for splay tree
    //
    Enode * nilKey = const_cast< Enode * >( enil );
    store.setNil( nilKey );
    id_to_enode.push_back( const_cast< Enode * >( enil ) );
    precision = c.nra_precision;
  }

  ~Egraph( )
  {
    backtrackToStackSize( 0 );
#ifdef STATISTICS
    if ( config.produce_stats && tsolvers_stats.size( ) > 0 )
    {
      config.getStatsOut( ) << "# -------------------------" << endl;
      config.getStatsOut( ) << "# STATISTICS FOR EUF SOLVER" << endl;
      config.getStatsOut( ) << "# -------------------------" << endl;
      tsolvers_stats[ 0 ]->printStatistics( config.getStatsOut( ) );
      delete tsolvers_stats[ 0 ];
    }
#endif
    //
    // Delete Ordinary Theory Solvers
    //
#ifdef STATISTICS
    assert( tsolvers.size( ) == tsolvers_stats.size( ) );
#endif
    for ( unsigned i = 1 ; config.produce_stats && i < tsolvers.size( ) ; i ++ )
    {
#ifdef STATISTICS
      config.getStatsOut( ) << "# -------------------------" << endl;
      config.getStatsOut( ) << "# STATISTICS FOR " << tsolvers[ i ]->getName( ) << endl;
      config.getStatsOut( ) << "# -------------------------" << endl;
      assert( tsolvers_stats[ i ] );
      tsolvers_stats[ i ]->printStatistics( config.getStatsOut( ) );
      delete tsolvers_stats[ i ];
#endif
      assert( tsolvers[ i ] );
      delete tsolvers[ i ];
    }
    //
    // Delete enodes
    //
    while ( !id_to_enode.empty( ) )
    {
      if ( id_to_enode.back( ) != NULL )
        delete id_to_enode.back( );
      id_to_enode.pop_back( );
    }
#ifdef PRODUCE_PROOF
    assert( cgraph_ );
    delete cgraph_;
#endif
  }

  //
  // Predefined constants nil, true, false
  // TODO: turn etrue efalse into constants
  //
  const Enode * const enil;
  Enode * etrue;
  Enode * efalse;

  //===========================================================================
  // Public APIs for enode construction/destruction

  Enode *  newSymbol           ( const char *, Snode * );                                        // Creates a new symbol
  Enode *  cons                ( list< Enode * > & );                                            // Shortcut, but not efficient
  Enode *  cons                ( Enode *, Enode * );                                             // Create Lists/Terms
  Enode *  cons                ( Enode *, Enode *, bool & );                                     // Create Lists/Terms; notifies if already existent
  Enode *  cons                ( Enode * e ) { return cons( e, const_cast< Enode * >(enil) ); }  // Shortcut for singleton
  //
  // Specialized functions
  //
  inline Enode * mkLt          ( Enode * args ) { return mkNot( cons( mkLeq( swapList( args ) ) ) ); }
  inline Enode * mkGeq         ( Enode * args ) { return              mkLeq( swapList( args ) ); }
  inline Enode * mkGt          ( Enode * args ) { return mkNot( cons( mkLeq(           args ) ) ); }

  inline Enode * mkTrue        ( )              { return etrue; }
  inline Enode * mkFalse       ( )              { return efalse; }

  /*
  inline Enode * mkBvslt       ( Enode * args, bool simp = true ) { return simp ? mkNot( cons( mkBvsle( swapList( args ) ) ) ) : cons( id_to_enode[ ENODE_ID_BVSLT ], args ); }
  inline Enode * mkBvsge       ( Enode * args )                   { return              mkBvsle( swapList( args ) ); }
  inline Enode * mkBvsgt       ( Enode * args )                   { return mkNot( cons( mkBvsle( args ) ) ); }

  inline Enode * mkBvult       ( Enode * args, bool simp = true ) { return simp ? mkNot( cons( mkBvule( swapList( args ) ) ) ) : cons( id_to_enode[ ENODE_ID_BVULT ], args ); }
  inline Enode * mkBvuge       ( Enode * args )                   { return              mkBvule( swapList( args ) ); }
  inline Enode * mkBvugt       ( Enode * args )                   { return mkNot( cons( mkBvule( args ) ) ); }

  inline Enode * mkBvurem      ( Enode * args ) { return cons( id_to_enode[ ENODE_ID_BVUREM ], args ); }
  inline Enode * mkBvudiv      ( Enode * args ) { return cons( id_to_enode[ ENODE_ID_BVUDIV ], args ); }
  */

  //
  // Implemented in EgraphStore.C
  // Semantic of mk* functions: they use
  // the concrete cons, and they store the
  // node permanently inside the term bank
  //
  Enode * mkPlus             ( Enode * );
  Enode * mkMinus            ( Enode * );
  Enode * mkTimes            ( Enode * );
  Enode * mkDiv              ( Enode * );
  Enode * mkUminus           ( Enode * );
  Enode * mkDistinct         ( Enode * );
  Enode * mkNot              ( Enode * );
  Enode * mkAnd              ( Enode * );
  Enode * mkIff              ( Enode * );
  Enode * mkOr               ( Enode * );
  Enode * mkIte              ( Enode * );
  Enode * mkIte              ( Enode *, Enode *, Enode * );
  Enode * mkEq               ( Enode * );
  Enode * mkImplies          ( Enode * );
  Enode * mkXor              ( Enode * );

  /* added for dReal2 */
  Enode * mkAbs              ( Enode * );
  Enode * mkSin              ( Enode * );
  Enode * mkCos              ( Enode * );
  Enode * mkTan              ( Enode * );
  Enode * mkAsin             ( Enode * );
  Enode * mkAcos             ( Enode * );
  Enode * mkAtan             ( Enode * );
  Enode * mkSinh             ( Enode * );
  Enode * mkCosh             ( Enode * );
  Enode * mkTanh             ( Enode * );
  Enode * mkAtan2            ( Enode * );
  Enode * mkMin              ( Enode * );
  Enode * mkMax              ( Enode * );
  Enode * mkMatan            ( Enode * );
  Enode * mkSafeSqrt         ( Enode * );
  Enode * mkSqrt             ( Enode * );
  Enode * mkExp              ( Enode * );
  Enode * mkLog              ( Enode * );
  Enode * mkPow              ( Enode * );
  Enode * mkForallT          ( Enode *, Enode *, Enode *, Enode * );
  Enode * mkIntegral         ( Enode * time_0, Enode * time_t, Enode * vec_0, Enode * vec_t, char * flowname );
  Enode * mkForall ( vector<pair<string, Snode *>*>* sorted_var_list, Enode * e);
  Enode * mkExists ( vector<pair<string, Snode *>*>* sorted_var_list, Enode * e);

  /* ----------------- */

  Enode * mkSelect           ( Enode *, Enode * );
  Enode * mkStore            ( Enode *, Enode *, Enode * );

  /* commented out for dReal2 */
//  Enode * mkCostIncur        ( Enode * );
//  Enode * mkCostBound        ( Enode * );

  Enode * mkLeq              ( Enode * );

  Enode * mkBvand            ( Enode * );
  Enode * mkBvor             ( Enode * );
  Enode * mkBvnot            ( Enode * );
  Enode * mkBvxor            ( Enode * );
  Enode * mkConcat           ( Enode * );
  Enode * mkCbe              ( Enode * );
  Enode * mkBvlshr           ( Enode * );
  Enode * mkBvashr           ( Enode * );
  Enode * mkBvshl            ( Enode * );
  Enode * mkBvneg            ( Enode * );
  Enode * mkBvmul            ( Enode * );
  Enode * mkBvadd            ( Enode * );
  Enode * mkBvsub            ( Enode * );
  Enode * mkBvsdiv           ( Enode * );
  Enode * mkBvsrem           ( Enode * );

  Enode * mkBvsle            ( Enode * );
  Enode * mkBvule            ( Enode * );
  Enode * mkZeroExtend       ( int, Enode * );
  Enode * mkSignExtend       ( int, Enode * );
  Enode * mkRotateLeft       ( int, Enode * );
  Enode * mkRotateRight      ( int, Enode * );
  Enode * mkExtract          ( int, int, Enode * );
  Enode * mkRepeat           ( int, Enode * );
  Enode * mkWord1cast        ( Enode * );
  Enode * mkBoolcast         ( Enode * );

  Enode * allocTrue          ( );
  Enode * allocFalse         ( );

  Enode * mkVar              ( const char *, bool = false );
  Enode * mkNum              ( const char * );
  Enode * mkNum              ( const char *, const char * );
  Enode * mkNum              ( const double );
  Enode * mkFun              ( const char *, Enode * );

  void    mkDefine           ( const char *, Enode * );
  Enode * mkLet              ( Enode * );
  Enode * getDefine          ( const char * );

  //Enode * makeNumberFromGmp  ( mpz_class &, const int );

  Enode * getUncheckedAssertions  ( );
#ifdef PRODUCE_PROOF
  Enode * getNextAssertion        ( );
#endif
  void    setDistinctEnodes       ( vector< Enode * > & );

  void    printEnodeList          ( ostream & );
  void    addAssertion            ( Enode * );

  void    evaluateTerm            ( Enode *, double& );

  void          initializeStore   ( );
#ifndef SMTCOMP
  inline void   addSubstitution   ( Enode * s, Enode * t ) { top_level_substs.push_back( make_pair( s, t ) ); }
  inline vector< Pair( Enode * ) >&  getSubstitutions  ( ) { return top_level_substs; }
#endif
  inline void   setTopEnode       ( Enode * e )            { assert( e ); top = e; }
  inline size_t nofEnodes         ( )                      { return id_to_enode.size( ); }

  inline Enode * indexToDistReas ( unsigned index ) const
  {
    assert( index < index_to_dist.size( ) );
    return index_to_dist[ index ];
  }

#ifdef PRODUCE_PROOF
  void            addIFormula      ( );
  inline uint64_t getIPartitions   ( Enode * e )             { assert( e->getId( ) < static_cast< int >( id_to_iformula.size( ) ) ); return id_to_iformula[ e->getId( ) ]; }
  inline void     setIPartitions   ( Enode * e, uint64_t p ) { if ( e->getId( ) >= static_cast< int >( id_to_iformula.size( ) ) ) id_to_iformula.resize( e->getId( ) + 1, 0 ); id_to_iformula[ e->getId( ) ] |= p; }
  inline unsigned getNofPartitions ( )                       { return iformula - 1; }
  inline void     formulaToTag     ( Enode * e )             { formulae_to_tag.push_back( e ); }
  void            tagIFormulae     ( const uint64_t );
  void            tagIFormulae     ( const uint64_t, vector< Enode * > & );
  void            tagIFormula      ( Enode *, const uint64_t );
#endif

  Enode * copyEnodeEtypeTermWithCache   ( Enode *, bool = false );
  Enode * copyEnodeEtypeListWithCache   ( Enode *, bool = false );

 /* commented out for dReal2 */
  //  inline void         setRescale        ( Real & r ) {} //rescale_factor = r; rescale_factor_l = atol( r.get_str( ).c_str( ) ); }
  //  inline const Real & getRescale        ( Real & p ) { (void)p; return rescale_factor; }
  //  inline const long & getRescale        ( long & p ) { (void)p; return rescale_factor_l; }

  inline bool hasItes                   ( ) { return has_ites; }

  Enode * canonize                      ( Enode *, bool = false );

#ifdef STATISTICS
  void        printMemStats             ( ostream & );
#endif
  //
  // Fast duplicates checking. Cannot be nested !
  //
  inline void initDup1  ( )           { assert( !active_dup1 ); active_dup1 = true; duplicates1.resize( id_to_enode.size( ), dup_count1 ); dup_count1 ++; }
  inline void storeDup1 ( Enode * e ) { assert(  active_dup1 ); assert( e->getId( ) < (enodeid_t)duplicates1.size( ) ); duplicates1[ e->getId( ) ] = dup_count1; }
  inline bool isDup1    ( Enode * e ) { assert(  active_dup1 ); assert( e->getId( ) < (enodeid_t)duplicates1.size( ) ); return duplicates1[ e->getId( ) ] == dup_count1; }
  inline void doneDup1  ( )           { assert(  active_dup1 ); active_dup1 = false; }
  //
  // Fast duplicates checking. Cannot be nested !
  //
  inline void initDup2  ( )           { assert( !active_dup2 ); active_dup2 = true; duplicates2.resize( id_to_enode.size( ), dup_count2 ); dup_count2 ++; }
  inline void storeDup2 ( Enode * e ) { assert(  active_dup2 ); assert( e->getId( ) < (enodeid_t)duplicates2.size( ) ); duplicates2[ e->getId( ) ] = dup_count2; }
  inline bool isDup2    ( Enode * e ) { assert(  active_dup2 ); assert( e->getId( ) < (enodeid_t)duplicates2.size( ) ); return duplicates2[ e->getId( ) ] == dup_count2; }
  inline void doneDup2  ( )           { assert(  active_dup2 ); active_dup2 = false; }
  //
  // Fast duplicates checking. Cannot be nested !
  //
  void    initDupMap1  ( );
  void    storeDupMap1 ( Enode *, Enode * );
  Enode * valDupMap1   ( Enode * );
  void    doneDupMap1  ( );

  void    initDupMap2  ( );
  void    storeDupMap2 ( Enode *, Enode * );
  Enode * valDupMap2   ( Enode * );
  void    doneDupMap2  ( );

  void    computePolarities ( Enode * );

  void dumpHeaderToFile  ( ostream & );
  void dumpFormulaToFile ( ostream &, Enode *, bool = false );
  void dumpToFile        ( const char *, Enode * );

  //===========================================================================
  // Public APIs for Theory Combination with DTC

  void    gatherInterfaceTerms     ( Enode * );
  int     getInterfaceTermsNumber  ( );
  Enode * getInterfaceTerm         ( const int );
  bool    isRootUF                 ( Enode * );
  Enode * canonizeDTC              ( Enode *, bool = false );
  // Not used but left there
  bool    isPureUF                 ( Enode * );
  bool    isPureLA                 ( Enode * );

  /* added for dReal */
  std::unordered_map<string, dreal::flow> flow_maps;
  bool                                    stepped_flows; //Does flow name have step index?

private:

  vector< Enode * > interface_terms;
  // Cache for interface terms
  set< Enode * >    interface_terms_cache;
  // Cache for uf terms and la terms
  set< Enode * > it_uf, it_la;
  static constexpr double      default_precision = 0.001;
  double            precision;     /* added for dReal */

public:

  //===========================================================================
  // Public APIs for Egraph Core Solver

  void                initializeTheorySolvers ( SimpSMTSolver * );          // Attaches ordinary theory solvers
  lbool               inform                  ( Enode * );                  // Inform the solver about the existence of a theory atom
  bool                assertLit               ( Enode *, bool = false );    // Assert a theory literal
  void                pushBacktrackPoint      ( );                          // Push a backtrack point
  void                popBacktrackPoint       ( );                          // Backtrack to last saved point
  Enode *             getDeduction            ( );                          // Return an implied node based on the current state
  Enode *             getSuggestion           ( );                          // Return a suggested literal based on the current state
  vector< Enode * > & getConflict             ( bool = false );             // Get explanation
#ifdef PRODUCE_PROOF
  Enode *             getInterpolants         ( );                          // Get interpolant
#endif
  bool                check                   ( bool );                     // Check satisfiability
  void                initializeCong          ( Enode * );                  // Initialize congruence structures for a node
#ifndef SMTCOMP
  void                computeModel            ( );
  void                printModel              ( ostream & );                // Computes and print the model
#endif
  inline void         setUseGmp               ( ) { use_gmp = true; }
  inline bool         getUseGmp               ( ) { return use_gmp; }
  void                splitOnDemand           ( vector< Enode * > &, int ); // Splitting on demand modulo equality
  void                splitOnDemand           ( Enode *, int );             // Splitting on demand
  bool                checkDupClause          ( Enode *, Enode * );         // Check if a clause is duplicate

  void                setPrecision            ( double );
  double              getPrecision            ( ) const;
  const vector<OrdinaryTSolver*>     getTSolvers             ( ) const { return tsolvers; }
private:

  //===========================================================================
  // Private Routines for enode construction/destruction

  SStore & sort_store;
  Snode *  sarith0;

  //
  // Defines the set of operations that can be performed and that should be undone
  //
  typedef enum {      // These constants are stored on undo_stack_oper when
      SYMB            // A new symbol is created
    , NUMB            // A new number is created
    , CONS            // An undoable cons is done
    , MERGE           // A merge is done
    , INITCONG        // Congruence initialized
    , FAKE_MERGE      // A fake merge for incrementality
    , FAKE_INSERT     // A fake insert for incrementality
    , DISEQ           // A negated equality is asserted
    , DIST            // A distinction is asserted
    , INSERT_STORE    // Inserted in store
    , EXPL            // Explanation added
    , SET_DYNAMIC     // Dynamic info was set
  } oper_t;
  //
  // Handy function to swap two arguments of a list
  //
  inline Enode * swapList ( Enode * args )
  {
    assert( args );
    assert( args->isList( ) );
    assert( args->getArity( ) == 2 );
    return cons( args->getCdr( )->getCar( ), cons( args->getCar( ) ) );
  }
  //
  // Related to term creation
  //
  Enode * insertNumber ( Enode * );                             // Inserts a number
  void    removeNumber ( Enode * );                             // Remove a number
  void    insertSymbol ( Enode * );                             // Inserts a symbol
  void    removeSymbol ( Enode * );                             // Remove a symbol
  Enode * lookupSymbol ( const char * name );                   // Retrieve a symbol
  void    insertDefine ( const char *, Enode * );               // Insert a define
  Enode * lookupDefine ( const char * );                        // Retrieve a define
  Enode * insertStore  ( const enodeid_t, Enode *, Enode * );   // Insert node into the global store
  void    removeStore  ( Enode * );                             // Remove a node from the global store
#ifndef SMTCOMP
  void    evaluateTermRec ( Enode *, double& );                  // Evaluate node
#endif
  //
  // Related to congruence closure
  //
  Enode * insertSigTab ( const enodeid_t, Enode *, Enode * );   // For undoable cons only
  Enode * insertSigTab ( Enode * );                             // For for terms that go in the congruence
  Enode * lookupSigTab ( Enode * );                             // Retrieve Enode
  void    removeSigTab ( Enode * );                             // Remove Enode from sig_tab

  bool                        active_dup1;                      // To prevent nested usage
  bool                        active_dup2;                      // To prevent nested usage
  vector< int >               duplicates1;                      // Fast duplicate checking
  vector< int >               duplicates2;                      // Fast duplicate checking
  int                         dup_count1;                       // Current dup token
  int                         dup_count2;                       // Current dup token
  bool                        active_dup_map1;                  // To prevent nested usage
  bool                        active_dup_map2;                  // To prevent nested usage
  vector< Enode * >           dup_map1;                         // Fast duplicate checking
  vector< int >               dup_set1;                         // Fast duplicate checking
  vector< Enode * >           dup_map2;                         // Fast duplicate checking
  vector< int >               dup_set2;                         // Fast duplicate checking
  int                         dup_map_count1;                   // Current dup token
  int                         dup_map_count2;                   // Current dup token
  map< string, Enode * >      name_to_number;                   // Store for numbers
  map< string, Enode * >      name_to_symbol;                   // Store for symbols
  map< string, Enode * >      name_to_define;                   // Store for defines

  SplayTree< Enode *, Enode::idLessThan > store;                // The actual store
  SigTab                                  sig_tab;		// (Supposely) Efficient Signature table for congruence closure

  vector< Enode * >              id_to_enode;                   // Table ENODE_ID --> ENODE
  vector< int >                  id_to_belong_mask;             // Table ENODE_ID --> ENODE
  vector< int >                  id_to_fan_in;                  // Table ENODE_ID --> fan in
  vector< Enode * >              index_to_dist;                 // Table distinction index --> enode
  list< Enode * >                assertions;                    // List of assertions
  vector< Enode * >              cache;                         // Cache simplifications
  Enode *                        top;                           // Top node of the formula
  map< Pair( int ), Enode * >    ext_store;                     // For fast extraction handling
  vector< Enode * >              se_store;                      // For fast sign extension
  vector< int >                  id_to_inc_edges;               // Keeps track of how many edges enter an enode
  bool                           has_ites;                      // True if there is at least one ite
  set< Enode * >                 variables;                     // List of variables
#ifndef SMTCOMP
  vector< Pair( Enode * ) >      top_level_substs;              // Keep track of substitutuions in TopLevelProp.C
  bool                           model_computed;                // Has model been computed lately ?
#endif
  bool                           congruence_running;            // True if congruence is running

#ifdef PRODUCE_PROOF
  unsigned                iformula;                             // Current formula id
  vector< Enode * >       formulae_to_tag;                      // Formulae to be tagged
  vector< uint64_t >      id_to_iformula;                       // From enode to iformula it belongs to
  CGraph *                cgraph_;                              // Holds congrunce graph and compute interpolant
  CGraph &                cgraph;                               // Holds congrunce graph and compute interpolant
#endif

  //===========================================================================
  // Private Routines for Core Theory Solver

  bool    assertLit_      ( Enode * );                          // Assert a theory literal
  //
  // Asserting literals
  //
  bool    assertEq        ( Enode *, Enode *, Enode * );        // Asserts an equality
  bool    assertNEq       ( Enode *, Enode *, Enode * );        // Asserts a negated equality
  bool    assertDist      ( Enode *, Enode * );                 // Asserts a distinction
  //
  // Backtracking
  //
  void backtrackToStackSize ( size_t );                         // Backtrack to a certain operation
  //
  // Congruence closure main routines
  //
  bool    unmergable      ( Enode *, Enode *, Enode ** );       // Can two nodes be merged ?
  void    merge           ( Enode *, Enode * );                 // Merge two nodes
  bool    mergeLoop       ( Enode * );                          // Merge loop
  void    deduce          ( Enode *, Enode * );                 // Deduce from merging of two nodes
  void    undoMerge       ( Enode * );                          // Undoes a merge
  void    undoDisequality ( Enode * );                          // Undoes a disequality
  void    undoDistinction ( Enode * );                          // Undoes a distinction
  //
  // Explanation routines and data
  //
  void     expExplain           ( );                            // Main routine for explanation
  void     expExplain           ( Enode *, Enode *, Enode * );  // Enqueue equality and explain
  void     expStoreExplanation  ( Enode *, Enode *, Enode * );  // Store the explanation for the merge
  void     expExplainAlongPath  ( Enode *, Enode * );           // Store explanation in explanation
  void     expEnqueueArguments  ( Enode *, Enode * );           // Enqueue arguments to be explained
  void     expReRootOn          ( Enode * );                    // Reroot the proof tree on x
  void     expUnion             ( Enode *, Enode * );           // Union of x and y in the explanation
  Enode *  expFind              ( Enode * );                    // Find for the eq classes of the explanation
  Enode *  expHighestNode       ( Enode * );                    // Returns the node of the eq class of x that is closes to the root of the explanation tree
  Enode *  expNCA               ( Enode *, Enode * );           // Return the nearest common ancestor of x and y
  void     expRemoveExplanation ( );                            // Undoes the effect of expStoreExplanation
  void     expCleanup           ( );                            // Undoes the effect of expExplain

  inline const char * logicStr ( logic_t l )
  {
         if ( l == EMPTY )    return "EMPTY";
    else if ( l == QF_UF )    return "QF_UF";
    else if ( l == QF_BV )    return "QF_BV";
    else if ( l == QF_RDL )   return "QF_RDL";
    else if ( l == QF_IDL )   return "QF_IDL";
    else if ( l == QF_LRA )   return "QF_LRA";
    else if ( l == QF_LIA )   return "QF_LIA";
    else if ( l == QF_UFRDL ) return "QF_UFRDL";
    else if ( l == QF_UFIDL ) return "QF_UFIDL";
    else if ( l == QF_UFLRA ) return "QF_UFLRA";
    else if ( l == QF_UFLIA ) return "QF_UFLIA";
    else if ( l == QF_UFBV )  return "QF_UFBV";
    else if ( l == QF_AX )    return "QF_AX";
    return "";
  }

  bool                        theoryInitialized;                // True if theory solvers are initialized
  bool                        state;                            // the hell is this ?
  set< enodeid_t >            initialized;                      // Keep track of initialized nodes
  map< enodeid_t, lbool >     informed;                         // Keep track of informed nodes
  vector< Enode * >           pending;                          // Pending merges
  vector< Enode * >           undo_stack_term;                  // Keeps track of terms involved in operations
  vector< oper_t >            undo_stack_oper;                  // Keeps track of operations
  vector< Enode * >           explanation;                      // Stores explanation

  vector< Enode * >           exp_pending;                      // Pending explanations
  vector< Enode * >           exp_undo_stack;                   // Keep track of exp_parent merges
  vector< Enode * >           exp_cleanup;                      // List of nodes to be restored
  int                         time_stamp;                       // Need for finding NCA
  int                         conf_index;                       // Index of theory solver that caused conflict

  /* commented out for dReal2 */
  /* Real                        rescale_factor;                   // Rescale factor for DL */
  /* long                        rescale_factor_l;                 // Rescale factor for DL */
  bool                        use_gmp;                          // Do we have to use gmp?

  void    initializeCongInc ( Enode * );                        // Initialize a node in the congruence at runtime
  void    initializeAndMerge( Enode * );                        // Initialize a node in the congruence at runtime
  Enode * uCons             ( Enode *, Enode * );               // Undoable cons - To create dynamic terms
  void    undoCons          ( Enode * );                        // Undoes a cons

  //===========================================================================
  // Array Handling routines - Implemented in src/tsolvers/axsolver/AXSolver.C

  void              WAxiom                                ( Enode * );
  void              RoWEqAxiom                            ( Enode * );
  void              RoWNeqAxiom                           ( Enode * );
  void              WoWEqAxiom                            ( Enode * );
  void              WoWNeqAxiom                           ( Enode * );
  void              WoRAxiom                              ( Enode * );
  void              ExtAxiom                              ( Enode *, Enode * );
  void              EqAxiomInst                           ( Enode *, Enode *, Enode * );
  void              handleArrayAssertedEq                 ( Enode *, Enode * );
  void              handleArrayAssertedNEq                ( Enode *, Enode * );
  void              handleArrayAssertedAtomTerm           ( Enode * );
  void              propagateIndexToArraySubterm          ( Enode * );
  void              propagateIndexToArraySuperterms       ( Enode * );
  void              propagateIndexToArrayEquivalenceClass ( Enode *, Enode * );
  void              handleArrayMerge                      ( Enode *, Enode * );
  void              addStoreSuperterm                     ( Enode *, Enode * );
  void              printStoreSupertermsList              ( Enode * );
  bool              addArrayRelevantIndex                 ( Enode *, Enode *);
  bool              findArrayRelevantIndex                ( Enode *, Enode *);
  list< Enode * > & getStoreSupertermsList                ( Enode * );
  set< Enode * > &  getArrayRelevantIndicesSet            ( Enode * );
  void              printArrayRelevantIndicesSets         ( Enode * );

  map< enodeid_t, list< Enode * > > storeSuperterms;
  map< enodeid_t, set< Enode * > >  arrayRelevantIndicesSet;

  //============================================================================

  vector< bool >                 arrayAtomTermDone;

#ifdef BUILD_64
  hash_set< enodeid_pair_t >     clauses_sent;
#else
  hash_set< Pair( enodeid_t ) >  clauses_sent;
#endif

  //===========================================================================
  // Debugging routines - Implemented in EgraphDebug.C

  void printEqClass              ( ostream &, Enode * );
  void printExplanation          ( ostream & );
  void printExplanationTree      ( ostream &, Enode * );
  void printExplanationTreeDotty ( ostream &, Enode * );
  void printDistinctionList      ( ostream &, Enode * );
  void printCbeStructure         ( );
  void printCbeStructure         ( ostream &, Enode *, set< int > & );
  void printParents              ( ostream &, Enode * );
#if PEDANTIC_DEBUG
  bool checkParents              ( Enode * );
  bool checkInvariants           ( );
  bool checkInvariantFLS         ( );
  bool checkInvariantSTC         ( );
  bool checkExp                  ( );
  bool checkExpTree              ( Enode * );
  bool checkExpReachable         ( Enode *, Enode * );
#endif
  bool checkStaticDynamicTable   ( );

#ifdef STATISTICS
  void printStatistics ( ofstream & );
#endif
};

inline void Egraph::initDupMap1( )
{
  assert( !active_dup_map1 );
  active_dup_map1 = true;
  dup_map1.resize( id_to_enode.size( ), NULL );
  dup_set1.resize( id_to_enode.size( ), dup_map_count1 );
  dup_map_count1 ++;
}

inline void Egraph::initDupMap2( )
{
  assert( !active_dup_map2 );
  active_dup_map2 = true;
  dup_map2.resize( id_to_enode.size( ), NULL );
  dup_set2.resize( id_to_enode.size( ), dup_map_count2 );
  dup_map_count2 ++;
}

inline void Egraph::storeDupMap1( Enode * k, Enode * e )
{
  assert(  active_dup_map1 );
  dup_map1.resize( id_to_enode.size( ), NULL );
  dup_set1.resize( id_to_enode.size( ), dup_map_count1 - 1 );
  assert( k->getId( ) < (enodeid_t)dup_set1.size( ) );
  dup_set1[ k->getId( ) ] = dup_map_count1;
  dup_map1[ k->getId( ) ] = e;
}

inline void Egraph::storeDupMap2( Enode * k, Enode * e )
{
  assert(  active_dup_map2 );
  dup_map2.resize( id_to_enode.size( ), NULL );
  dup_set2.resize( id_to_enode.size( ), dup_map_count2 - 1 );
  assert( k->getId( ) < (enodeid_t)dup_set2.size( ) );
  dup_set2[ k->getId( ) ] = dup_map_count2;
  dup_map2[ k->getId( ) ] = e;
}

inline Enode * Egraph::valDupMap1( Enode * k )
{
  assert(  active_dup_map1 );
  dup_map1.resize( id_to_enode.size( ), NULL );
  dup_set1.resize( id_to_enode.size( ), dup_map_count1 - 1 );
  assert( k->getId( ) < (enodeid_t)dup_set1.size( ) );
  if ( dup_set1[ k->getId( ) ] == dup_map_count1 )
    return dup_map1[ k->getId( ) ];
  return NULL;
}

inline Enode * Egraph::valDupMap2( Enode * k )
{
  assert(  active_dup_map2 );
  dup_map2.resize( id_to_enode.size( ), NULL );
  dup_set2.resize( id_to_enode.size( ), dup_map_count2 - 1 );
  assert( k->getId( ) < (enodeid_t)dup_set2.size( ) );
  if ( dup_set2[ k->getId( ) ] == dup_map_count2 )
    return dup_map2[ k->getId( ) ];
  return NULL;
}

inline void Egraph::doneDupMap1( )
{
  assert(  active_dup_map1 );
  active_dup_map1 = false;
}

inline void Egraph::doneDupMap2( )
{
  assert(  active_dup_map2 );
  active_dup_map2 = false;
}

#endif
