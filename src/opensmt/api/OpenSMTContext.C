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

#include "OpenSMTContext.h"
#include "ExpandITEs.h"
#include "ArraySimplify.h"
#include "BVBooleanize.h"
#include "TopLevelProp.h"
#include "DLRescale.h"
#include "Ackermanize.h"
#include "Purify.h"

#include <csignal>

namespace opensmt {

bool stop;

} // namespace opensmt

void 
OpenSMTContext::SetLogic( logic_t l ) 
{ 
  config.logic = l; 

#ifdef SMTCOMP
  loadCustomSettings( );
#endif

  egraph.initializeStore( ); 
  solver.initialize( );
  // Also initialize theory solvers
  egraph.initializeTheorySolvers( &solver );
  init = true;
}

void
OpenSMTContext::SetLogic( const char * str )
{
       if ( strcmp( str, "EMPTY" )    == 0 ) config.logic = EMPTY;
  else if ( strcmp( str, "QF_UF" )    == 0 ) config.logic = QF_UF;
  else if ( strcmp( str, "QF_BV" )    == 0 ) config.logic = QF_BV;
  else if ( strcmp( str, "QF_RDL" )   == 0 ) config.logic = QF_RDL;
  else if ( strcmp( str, "QF_IDL" )   == 0 ) config.logic = QF_IDL;
  else if ( strcmp( str, "QF_LRA" )   == 0 ) config.logic = QF_LRA;
  else if ( strcmp( str, "QF_LIA" )   == 0 ) config.logic = QF_LIA;
  else if ( strcmp( str, "QF_UFRDL" ) == 0 ) config.logic = QF_UFRDL;
  else if ( strcmp( str, "QF_UFIDL" ) == 0 ) config.logic = QF_UFIDL;
  else if ( strcmp( str, "QF_UFLRA" ) == 0 ) config.logic = QF_UFLRA; 
  else if ( strcmp( str, "QF_UFLIA" ) == 0 ) config.logic = QF_UFLIA;
  else if ( strcmp( str, "QF_UFBV" )  == 0 ) config.logic = QF_UFBV;
  else if ( strcmp( str, "QF_AX" )    == 0 ) config.logic = QF_AX;
  else if ( strcmp( str, "QF_AUFBV" ) == 0 ) config.logic = QF_AUFBV;
  // DO NOT REMOVE THIS COMMENT !!
  // IT IS USED BY CREATE_THEORY.SH SCRIPT !!
  // NEW_THEORY_INIT

#ifdef SMTCOMP
   loadCustomSettings( );
#endif

  egraph.initializeStore( );
  solver.initialize( );
  init = true;
}

void
OpenSMTContext::SetInfo( const char * key )
{
  opensmt_error2( "command not supported (yet)", key );
}

void
OpenSMTContext::SetInfo( const char * key, const char * attr )
{
  assert( key );
  assert( attr );

  if ( strcmp( key, ":status" ) == 0 )
  {
    if ( strcmp( attr, "sat" ) == 0 )
      config.status = l_True;
    else if ( strcmp( attr, "unsat" ) == 0 )
      config.status = l_False;
    else if ( strcmp( attr, "unknown" ) == 0 )
      config.status = l_Undef;
    else
      opensmt_error2( "unrecognized attribute", attr );
  }
  else if ( strcmp( key, ":smt-lib-version" ) == 0 )
    ; // Do nothing
  else if ( strcmp( key, ":category" ) == 0 )
    ; // Do nothing
  else if ( strcmp( key, ":source" ) == 0 )
    ; // Do nothing
  else
    opensmt_error2( "unrecognized key", key );
}

void
OpenSMTContext::SetOption( const char * key )
{
  opensmt_error2( "command not supported (yet)", key );
}

void
OpenSMTContext::SetOption( const char * key, const char * attr )
{
  assert( key );
  assert( attr );

  if ( strcmp( key, ":print-success" ) == 0 )
  {
    if ( strcmp( attr, "true" ) == 0 )
      config.print_success = true;
  }
  else if ( strcmp( key, ":expand-definitions" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":interactive-mode" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":produce-proofs" ) == 0 )
  {
    if ( strcmp( attr, "true" ) == 0 )
    {
#ifndef PRODUCE_PROOF
      opensmt_error( "You must configure code with --enable-proof to produce proofs" );
#endif
      config.setProduceProofs( );
    }
  }
  else if ( strcmp( key, ":produce-unsat-cores" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":produce-models" ) == 0 )
  {
    if ( strcmp( attr, "true" ) == 0 )
      config.setProduceModels( );
  }
  else if ( strcmp( key, ":produce-assignments" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":regular-output-channel" ) == 0 )
    config.setRegularOutputChannel( attr );
  else if ( strcmp( key, ":diagnostic-output-channel" ) == 0 )
    config.setDiagnosticOutputChannel( attr );
  else if ( strcmp( key, ":random-seed" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":verbosity" ) == 0 )
    config.verbosity = atoi( attr );
  else
    opensmt_warning2( "skipping option ", key );
}

int
OpenSMTContext::executeCommands( )
{
  assert( init );

  int ret_val = 0;

  // Weird situation
  if ( nof_checksat <= 0 )
    return 2;

  // Trick for efficiency
  if ( nof_checksat == 1 )
    ret_val = executeStatic( );
  // Normal incremental solving
  else
  {
    config.incremental = 1;
    ret_val = executeIncremental( );
  }

  return ret_val;
}

//
// Execute a generic SMTLIB2 script
//
int OpenSMTContext::executeIncremental( )
{
  assert( init );
  assert( config.incremental == 1 );

  // Initialize theory solvers
  egraph.initializeTheorySolvers( &solver );

  lbool status = l_Undef;

  for ( size_t i = 0 ; i < command_list.size( ) ;  ++ i )
  {
    Command & c = command_list[ i ];

    // Commands blocked with assert( falase ) are issued from parser directly
    switch( c.command )
    {
      case SET_LOGIC:
	assert( false );
	break;
      case SET_OPTION:
	assert( false );
	break;
      case SET_INFO:
	assert( false );
	break;
      case DECLARE_SORT:
	DeclareSort( c.str, c.num );
	break;
      case DEFINE_SORT:
	opensmt_error( "construct define-sort not yet supported" );
	break;
      case DECLARE_FUN:
	DeclareFun( c.str, c.snode );
	break;
      case DEFINE_FUN:
	opensmt_error( "construct define-fun not yet supported" );
	break;
      case PUSH:
	Push( );
	break;
      case POP:
	Pop( );
	break;
      case ASSERT:
	Assert( c.enode );
	break;
      case CHECK_SAT:
	status = CheckSAT( );
	break;
      case GET_ASSERTIONS:
	opensmt_error( "construct get-assertions not yet supported" );
	break;
      case GET_PROOF:
	GetProof( );
	break;
      case GET_INTERPOLANTS:
	GetInterpolants( );
	break;
      case GET_UNSAT_CORE:
	opensmt_error( "construct get-unsat-core not yet supported" );
	break;
      case GET_VALUE:
	opensmt_error( "construct get-value not yet supported" );
	break;
      case GET_ASSIGNMENT:
	opensmt_error( "construct get-assignment not yet supported" );
	break;
      case GET_OPTION:
	opensmt_error( "construct get-option not yet supported" );
	break;
      case GET_INFO:
	opensmt_error( "construct get-info not yet supported" );
	break;
      case EXIT:
	Exit( );
	break;
      default:
	opensmt_error( "case not handled" );
    }
  }

  return 0;
}

//
// Execute a script in which there is only
// one check-sat. We can use specialized
// functions, such as preprocessing, to
// improve performance
//
int OpenSMTContext::executeStatic( )
{
  assert( init );
  assert( config.incremental == 0 );
  //
  // Hack for SMT-COMP 2010 for retrieving formula
  //
  for ( size_t i = 0 ; i < command_list.size( ) ; i ++ )
  {
    Command & c = command_list[ i ];
    if ( c.command == ASSERT )
      Assert( c.enode );
    else if ( c.command == CHECK_SAT )
    {
#ifdef PRODUCE_PROOF
      if ( config.produce_inter > 0 )
	staticCheckSATIterp( );
      else
#endif
	staticCheckSAT( ); 
    }
    else if ( c.command == EXIT )
      Exit( );
    else if ( c.command == GET_PROOF )
      GetProof( );
    else if ( c.command == GET_INTERPOLANTS )
      GetInterpolants( );
    else
      opensmt_error( "command not supported (yet)" );
  }

  return 0;
}

void OpenSMTContext::staticCheckSAT( ) 
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Statically Checking" << endl;

  // Retrieve the formula
  Enode * formula = egraph.getUncheckedAssertions( );

  if ( config.dump_formula != 0 )
    egraph.dumpToFile( "original.smt2", formula );

  if ( formula == NULL )
    opensmt_error( "formula undefined" );

  if ( config.logic == UNDEF )
    opensmt_error( "unable to determine logic" );

  // Removes ITEs if there is any
  if ( egraph.hasItes( ) )
  {
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      opensmt_error( "Interpolation not supported for ite construct" );
#endif
    ExpandITEs expander( egraph, config );
    formula = expander.doit( formula );

    if ( config.dump_formula != 0 )
      egraph.dumpToFile( "ite_expanded.smt2", formula );
  }

  // Gather interface terms for DTC
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    // Don't use with DTC of course
    && config.sat_lazy_dtc == 1
    // Don't use when dumping interpolants
    && config.sat_dump_rnd_inter == 0 )
  {
    Purify purifier( egraph, config );
    formula = purifier.doit( formula );

    if ( config.dump_formula != 0 )
      egraph.dumpToFile( "purified.smt2", formula );
  }

  // Ackermanize away functional symbols
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    // Don't use with DTC of course
    && config.sat_lazy_dtc == 0
    // Don't use when dumping interpolants
    && config.sat_dump_rnd_inter == 0 )
  {
    Ackermanize ackermanizer( egraph, config );
    formula = ackermanizer.doit( formula );

    if ( config.dump_formula != 0 )
      egraph.dumpToFile( "ackermanized.smt2", formula );
  }

  // Artificially create a boolean
  // abstraction, if necessary
  if ( config.logic == QF_BV )
  {
    BVBooleanize booleanizer( egraph, config );
    formula = booleanizer.doit( formula );
  }

  // Top-Level Propagator. It also canonize atoms
  TopLevelProp propagator( egraph, config );
  formula = propagator.doit( formula );

  // Applies array axioms where possible
  if( config.logic == QF_AX )
  {
    ArraySimplify simplifier( egraph, config );
    formula = simplifier.doit( formula );
  }

  // Convert RDL into IDL, also compute if GMP is needed
  if ( config.logic == QF_RDL )
  {
    DLRescale rescaler( egraph, config );
    rescaler.doit( formula );
  }

  // For static checking, make sure that if DTC is used
  // then incrementality is enabled
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
      && config.sat_lazy_dtc != 0 )
  {
    config.incremental = 1;
  }

  if ( config.dump_formula != 0 )
    egraph.dumpToFile( "presolve.smt2", formula );

  // Solve only if not simplified already
  if ( formula->isTrue( ) )
  {
    state = l_True;
  }
  else if ( formula->isFalse( ) )
  {
    state = l_False;
  }
  else
  {
    // Initialize theory solvers
    egraph.initializeTheorySolvers( &solver );

    // Compute polarities
    egraph.computePolarities( formula );

    // CNFize the input formula and feed clauses to the solver
    state = cnfizer.cnfizeAndGiveToSolver( formula );

    // Solve
    if ( state == l_Undef )
    {
      state = solver.smtSolve( config.sat_preprocess_booleans != 0
                            || config.sat_preprocess_theory   != 0 );
    }

    // If computation has been stopped, return undef
    if ( opensmt::stop ) state = l_Undef;
  }
}

#ifdef PRODUCE_PROOF
void OpenSMTContext::staticCheckSATIterp( ) 
{
  assert( config.produce_inter > 0 );

  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Statically Checking" << endl;

  if ( config.logic == UNDEF )
    opensmt_error( "unable to determine logic" );

  if ( egraph.hasItes( ) )
    opensmt_error( "Interpolation not supported for ite construct" );

  if ( config.logic == QF_UFIDL
    || config.logic == QF_UFLRA )
    opensmt_error( "Interpolation not supported (yet) for theory combination" );
  
  // Top-Level Propagator. It also canonize atoms
  TopLevelProp propagator( egraph, config );

  // Initialize theory solvers
  egraph.initializeTheorySolvers( &solver );

  for ( int in = 1 ; ; in ++ )
  {
    const uint64_t partition = SETBIT( in );
    // Get partition
    Enode * formula = egraph.getNextAssertion( );
    assert( in != 1 || formula != NULL );
    if ( formula == NULL ) break;
    // Canonize atoms
    formula = propagator.doit( formula );
    // CNFize the input formula and feed clauses to the solver
    state = cnfizer.cnfizeAndGiveToSolver( formula, partition );
  }

  // Solve
  if ( state == l_Undef )
  {
    if ( config.sat_preprocess_booleans != 0
      || config.sat_preprocess_theory != 0 )
      opensmt_warning( "not using SMT-preprocessing with interpolation" );
    state = solver.smtSolve( false );
  }

  // If computation has been stopped, return undef
  if ( opensmt::stop ) state = l_Undef;
}
#endif

//
// Here set the right parameter values for SMTCOMP
//
void OpenSMTContext::loadCustomSettings( )
{
  if ( config.logic == QF_IDL )
  {
    config.sat_polarity_mode = 5;
    config.sat_learn_up_to_size = 5;
    config.sat_minimize_conflicts = 1;
    config.sat_restart_first = 70;
    config.dl_theory_propagation = 1;
    config.sat_preprocess_booleans = 1;

  }
  else if ( config.logic == QF_UFIDL )
  {
    config.sat_polarity_mode = 1;
    config.sat_learn_up_to_size = 5;
    config.sat_minimize_conflicts = 1;
    config.sat_restart_first = 100;
    config.dl_theory_propagation = 1;
    config.sat_preprocess_booleans = 0;
  }
  else if ( config.logic == QF_RDL )
  {
    config.sat_polarity_mode = 0;
    config.sat_learn_up_to_size = 5;
    config.sat_minimize_conflicts = 1;
    config.sat_preprocess_booleans = 1;
    config.sat_restart_first = 70;
    config.dl_theory_propagation = 1;
    config.sat_restart_inc = 1.2;
  }
  else if ( config.logic == QF_UF )
  {
    config.sat_polarity_mode = 0;
    config.sat_learn_up_to_size = 8;
    config.sat_minimize_conflicts = 1;
    config.sat_preprocess_booleans = 1;
    config.sat_restart_first = 50;
    config.uf_theory_propagation = 1;
  }
  else if ( config.logic == QF_LRA )
  {
    config.sat_polarity_mode = 0;
    config.sat_learn_up_to_size = 12;
    config.sat_minimize_conflicts = 0;
    config.sat_restart_first = 70;
    config.lra_theory_propagation = 1;
    config.sat_preprocess_booleans = 0;
  }
}

// =======================================================================
// Functions that actually execute actions

void OpenSMTContext::DeclareSort( const char * name, int arity )
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Declaring sort " 
         << name 
	 << " of arity "
	 << arity
	 << endl;

  sstore.newSymbol( name );
}

void OpenSMTContext::DeclareFun( const char * name, Snode * s )
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Declaring function " 
         << name 
	 << " of sort "
	 << s
	 << endl;

  egraph.newSymbol( name, s );
}

void OpenSMTContext::Push( )
{ 
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Pushing backtrack point" << endl;

  solver.pushBacktrackPoint( ); 
}

void OpenSMTContext::Pop( )
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Popping backtrack point" << endl;

  solver.popBacktrackPoint( );
}

void OpenSMTContext::Reset( )
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Resetting" << endl;

  solver.reset( );
}

void OpenSMTContext::Assert( Enode * e )
{
  if ( config.verbosity > 1 )
  {
    if ( e->isBooleanOperator( ) )
      cerr << "# OpenSMTContext::Asserting formula with id " << e->getId( ) << endl;
    else
      cerr << "# OpenSMTContext::Asserting formula " << e << endl;
  }

  // Move an assertion into the Egraph
  // They are stored and might be preprocessed 
  // before entering the actual solver
  egraph.addAssertion( e );
}

void OpenSMTContext::GetProof( )
{
#ifdef PRODUCE_PROOF
  if ( state == l_False )
    solver.printProof( config.getRegularOut( ) );
  else
    opensmt_warning( "Skipping command (get-proof) as formula is not unsat" );
#else
  opensmt_warning( "Skipping command (get-proof): you need a version of opensmt compiled with --enable-proof" );
#endif
}

void OpenSMTContext::GetInterpolants( )
{
#ifdef PRODUCE_PROOF
  if ( config.produce_inter == 0 )
  {
    opensmt_warning( "Skipping command (get-interpolants) as (produce-interpolants) is not set" );
  }
  else if ( state == l_False )
  {
    solver.printInter( config.getRegularOut( ) );
  }
  else
  {
    opensmt_warning( "Skipping command (get-interpolants) as formula is not unsat" );
  }
#else
  opensmt_warning( "Skipping command (get-interpolants): you need a version of opensmt compiled with --enable-proof" );
#endif
}

lbool OpenSMTContext::CheckSAT( )
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Checking satisfiability" << endl;

  // Retrieve the conjunction of the
  // yet unchecked assertions
  Enode * formula = egraph.getUncheckedAssertions( );

  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Processing: " << formula << endl;

  state = cnfizer.cnfizeAndGiveToSolver( formula );
  if ( state == l_Undef )
    state = solver.solve( );

  if ( config.print_success )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}

lbool OpenSMTContext::CheckSAT( vec< Enode * > & assumptions )
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Checking satisfiability" << endl;

  // Retrieve the conjunction of the
  // yet unchecked assertions
  Enode * formula = egraph.getUncheckedAssertions( );

  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Processing: " << formula << endl;

  state = cnfizer.cnfizeAndGiveToSolver( formula );

  if ( state == l_Undef )
    state = solver.solve( assumptions, false );

  if ( config.print_success )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}

lbool OpenSMTContext::CheckSAT( vec< Enode * > & assumptions, unsigned limit )
{
  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Checking satisfiability" << endl;

  // Retrieve the conjunction of the
  // yet unchecked assertions
  Enode * formula = egraph.getUncheckedAssertions( );

  if ( config.verbosity > 1 )
    cerr << "# OpenSMTContext::Processing: " << formula << endl;

  state = cnfizer.cnfizeAndGiveToSolver( formula );

  if ( state == l_Undef )
    state = solver.solve( assumptions, limit, false );

  if ( config.print_success )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}

void OpenSMTContext::Exit( )
{ 
  PrintResult( state, config.status );
}

void OpenSMTContext::PrintResult( const lbool & result, const lbool & config_status )
{
  ostream & out = config.getRegularOut( );
#ifdef SMTCOMP
  (void)config_status;
#else
  fflush( stderr );
  (void)config_status;
  //
  // For testing purposes we return error if bug is found
  //
  if ( config_status != l_Undef
    && result != l_Undef
    && result != config_status )
    out << "error" << endl;
  else
#endif
  if ( result == l_True )
    out << "sat" << endl;
  else if ( result == l_False )
    out << "unsat" << endl;
  else if ( result == l_Undef )
    out << "unknown" << endl;
  else
    opensmt_error( "unexpected result" );

  fflush( stdout );

#ifndef SMTCOMP
  if ( config.verbosity )
  {
    //
    // Statistics
    //
    double   cpu_time = cpuTime();
    reportf( "#\n" );
    reportf( "# CPU Time used: %g s\n", cpu_time == 0 ? 0 : cpu_time );
    uint64_t mem_used = memUsed();
    reportf( "# Memory used: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
    reportf( "#\n" );
  }
#endif
}

// =======================================================================
// Functions that add commands to the list

void OpenSMTContext::addAssert( Enode * t )
{
  Command c;
  c.command = ASSERT;
  c.enode = t;
  command_list.push_back( c );
}

void OpenSMTContext::addCheckSAT( )
{
  Command c;
  c.command = CHECK_SAT;
  command_list.push_back( c );
  nof_checksat ++;
}

void OpenSMTContext::addPush( int n )
{
  assert( n > 0 );
  for ( int i = 0 ; i < n ; ++ i )
  {
    Command c;
    c.command = PUSH;
    command_list.push_back( c );
  }
}

void OpenSMTContext::addPop( int n )
{
  assert( n > 0 );
  for ( int i = 0 ; i < n ; ++ i )
  {
    Command c;
    c.command = POP;
    command_list.push_back( c );
  }
}

void OpenSMTContext::addExit( )
{
  Command c;
  c.command = EXIT;
  command_list.push_back( c );
}


void OpenSMTContext::addGetProof( )
{
  Command c;
  c.command = GET_PROOF;
  command_list.push_back( c );
}

void OpenSMTContext::addGetInterpolants( )
{
  Command c;
  c.command = GET_INTERPOLANTS;
  command_list.push_back( c );
}

