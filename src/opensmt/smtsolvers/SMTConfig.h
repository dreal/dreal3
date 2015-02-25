/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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

#ifndef SMTCONFIG_H
#define SMTCONFIG_H

#include <fstream>
#include <iostream>
#include <sys/stat.h>
#include "common/Global.h"
#include "minisat/core/SolverTypes.h"

using std::ofstream;
using std::ifstream;

//
// Holds informations about the configuration of the solver
//
struct SMTConfig
{
  //
  // For standard executable
  //
  SMTConfig ( int    argc
            , char * argv[ ] )
    : rocset   ( false )
    , docset   ( false )
  {
    initializeConfig( );
    if (argc > 1) {
        filename = argv[argc - 1];
        struct stat s;
        if(stat(filename,&s) != 0 || !(s.st_mode & S_IFREG)) {
            opensmt_error( "can't open file" );
        }
    } else {
        filename = "output";
    }
    // Parse command-line options
    parseCMDLine( argc, argv );
  }
  //
  // For API
  //
  SMTConfig ( )
  {
    initializeConfig( );
  }

  ~SMTConfig ( )
  {
    if ( produce_stats )  stats_out.close( );
    if ( rocset )         out.close( );
    if ( docset )         err.close( );
  }

  void initializeConfig ( );

  void parseConfig      ( char * );
  void parseCMDLine     ( int argc, char * argv[ ] );
  void printHelp        ( );
  void printConfig      ( ostream & out );

  inline bool      isInit      ( ) { return logic != UNDEF; }

  inline ostream & getStatsOut     ( ) { assert( produce_stats );  return stats_out; }
  inline ostream & getRegularOut   ( ) { return rocset ? out : cout; }
  inline ostream & getDiagnosticOut( ) { return docset ? err : cerr; }

  inline void setProduceModels( ) { if ( produce_models != 0 ) return; produce_models = 1; }
  inline void setProduceProofs( ) { if ( produce_proofs != 0 ) return; produce_proofs = 1; }
  inline void setProduceInter( )  { if ( produce_inter != 0 )  return; produce_inter = 1; }

  inline void setRegularOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stdout" ) != 0 && !rocset )
    {
      out.open( attr );
      if( !out )
        opensmt_error2( "can't open ", attr );
      rocset = true;
    }
  }

  inline void setDiagnosticOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stderr" ) != 0 && !rocset )
    {
      err.open( attr );
      if( !err )
        opensmt_error2( "can't open ", attr );
      rocset = true;
    }
  }

  const char * filename;                     // Holds the name of the input filename
  logic_t      logic;                        // SMT-Logic under consideration
  lbool        status;                       // Status of the benchmark
  int          incremental;                  // Incremental solving
  int          produce_stats;                // Should print statistics ?
  int          produce_models;               // Should produce models ?
  int          produce_proofs;               // Should produce proofs ?
  int          produce_inter;                // Should produce interpolants ?
  bool         rocset;                       // Regular Output Channel set ?
  bool         docset;                       // Diagnostic Output Channel set ?
  int          dump_formula;                 // Dump input formula
  int          verbosity;                    // Verbosity level
  bool         print_success;                // Print sat/unsat
  int          certification_level;          // Level of certification
  char         certifying_solver[256];       // Executable used for certification
  // SAT-Solver related parameters
  int          sat_theory_propagation;       // Enables theory propagation from the sat-solver
  int          sat_polarity_mode;            // Polarity mode
  double       sat_initial_skip_step;        // Initial skip step for tsolver calls
  double       sat_skip_step_factor;         // Increment for skip step
  int          sat_restart_first;            // First limit of restart
  double       sat_restart_inc;              // Increment of limit
  int          sat_use_luby_restart;         // Use luby restart mechanism
  int          sat_learn_up_to_size;         // Learn theory clause up to size
  int          sat_temporary_learn;          // Is learning temporary
  int          sat_preprocess_booleans;      // Activate satelite (on booleans)
  int          sat_preprocess_theory;        // Activate theory version of satelite
  int          sat_centrality;               // Specify centrality parameter
  int          sat_trade_off;                // Specify trade off
  int          sat_minimize_conflicts;       // Conflict minimization: 0 none, 1 bool only, 2 full
  int          sat_dump_cnf;                 // Dump cnf formula
  int          sat_dump_rnd_inter;           // Dump random interpolant
  int          sat_lazy_dtc;                 // Activate dtc
  int          sat_lazy_dtc_burst;           // % of eij to generate
  int          sat_reduce_proof;             // Enable proof reduction
  int          sat_reorder_pivots;           // Enable pivots reordering for interpolation
  double       sat_ratio_red_time_solv_time; // Reduction time / solving time
  double       sat_red_time;                 // Reduction time
  int          sat_num_glob_trans_loops;     // Number of loops recycle pivots + reduction
  int          sat_remove_mixed;             // Compression of AB-mixed subtrees
  // Proof manipulation parameters
  int          proof_reduce;                 // Enable proof reduction
  double       proof_ratio_red_solv;         // Ratio reduction time solving time
  double       proof_red_time;               // Reduction time
  int          proof_red_trans;              // Number of reduction transformations loops
  int          proof_reorder_pivots;         // Enable pivot reordering
  int          proof_remove_mixed;           // Enable removal of mixed predicates
  int          proof_use_sym_inter;          // Use Pudlak method
  int          proof_certify_inter;          // Check interpolants
  // UF-Solver related parameters
  int          uf_disable;                   // Disable the solver
  int          uf_theory_propagation;        // Enable theory propagation
  // BV-Solver related parameters
  int          bv_disable;                   // Disable the solver
  int          bv_theory_propagation;        // Enable theory propagation
  // DL-Solver related parameters
  int          dl_disable;                   // Disable the solver
  int          dl_theory_propagation;        // Enable theory propagation
  // LRA-Solver related parameters
  int          lra_disable;                  // Disable the solver
  int          lra_theory_propagation;       // Enable theory propagation
  int          lra_poly_deduct_size;         // Used to define the size of polynomial to be used for deduction; 0 - no deduction for polynomials
  int          lra_trade_off;                // Trade-off value for DL preprocessing
  int          lra_gaussian_elim;            // Used to switch on/off Gaussian elimination in LRA
  int          lra_integer_solver;           // Flag to require integer solution for LA problem
  int          lra_check_on_assert;          // Probability (0 to 100) to run check when assert is called

  // SMT related parameters used by dReal
  string       nra_bmc_heuristic;             // Use BMC variable selection heuristic in Minisat from file

  // NRA-Solver related parameters (added for dReal2)
  bool         nra_delta_test;                // precision=(nra_delta_test ? delta : epsilon)
  bool         nra_use_delta_heuristic;       // Split variable in constraint with max residual delta?
  bool         nra_short_sat;                 // Test theory if CNF is SAT, before have full model.
  double       nra_precision;                 // the value of delta
  double       nra_icp_improve;               // improve value for realpaver(ICP)
  bool         nra_verbose;                   // --verbose option
  bool         nra_debug;                     // --debug option
  bool         nra_stat;                      // --stat option
  bool         nra_proof;                     // --proof option
  bool         nra_model;                     // --model option
  ofstream     nra_model_out;                 // file stream for model
  string       nra_model_out_name;            // filename for model
  ofstream     nra_proof_out;                 // file stream for proof
  string       nra_proof_out_name;            // filename for proof
  bool         nra_json;                      // --proof option
  ofstream     nra_json_out;                  // file stream for json (visualization)
  string       nra_json_out_name;             // filename for json (visualization)
  unsigned     nra_ODE_taylor_order;          // --ode-order option
  unsigned     nra_ODE_grid_size;             // --ode-grid option
  unsigned     nra_ODE_timeout;               // --ode-timeout option
  double       nra_ODE_step;                  // step control
  bool         nra_ODE_contain;               // contain ODE or not
  bool         nra_ODE_cache;                 // use cache for ODE computation
  bool         nra_ODE_forward_only;          // only use ODE forward pruning (not use ODE backward)
  bool         nra_ODE_parallel;              // solve ODE in parallel or not
  unsigned     nra_aggressive;                // number of samples to use for aggressive sampling

private:

  ofstream     stats_out;                    // File for statistics
  ofstream     out;                          // Regular output channel
  ofstream     err;                          // Diagnostic output channel
};

#endif
