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

#include <assert.h>
#include <string.h>
#include <sys/stat.h>
#include <chrono>
#include <fstream>
#include <iostream>

#include "./dreal_config.h"
#include "common/Global.h"
#include "minisat/core/SolverTypes.h"
#include "util/stat.h"

//
// Holds informations about the configuration of the solver
//
struct SMTConfig
{
  //
  // For standard executable
  //
  SMTConfig ( int    argc
            , const char * argv[ ] )
    : rocset   ( false )
    , docset   ( false )
  {
    initializeConfig( );
    parseCMDLine( argc, argv );
  }
  //
  // For API
  //
  SMTConfig ( )
    : produce_stats ( false )
    , rocset ( false )
    , docset ( false )
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
  void parseCMDLine     ( int argc, const char * argv[ ] );
  void printConfig      ( std::ostream & out );

  inline bool      isInit      ( ) { return logic != UNDEF; }

  inline std::ostream & getStatsOut     ( ) { assert( produce_stats );  return stats_out; }
  inline std::ostream & getRegularOut   ( ) { return rocset ? out : std::cout; }
  inline std::ostream & getDiagnosticOut( ) { return docset ? err : std::cerr; }

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
  void initLogging();
  void setVerbosityDebugLevel();
  void setVerbosityInfoLevel();
  void setVerbosityWarningLevel();  // Default
  void setVerbosityErrorLevel();

  std::string  filename;                     // Holds the name of the input filename
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
  std::string  nra_bmc_heuristic;             // Use BMC variable selection heuristic in Minisat from file

  // NRA-Solver related parameters (added for dReal2)
  int          nra_theory_propagation;        // enables theory propagation
  bool         nra_delta_test;                // precision=(nra_delta_test ? delta : epsilon)
  bool         nra_use_delta_heuristic;       // Split variable in constraint with max residual delta?
  bool         nra_short_sat;                 // Test theory if CNF is SAT, before have full model.
  double       nra_precision;                 // the value of delta
#ifdef LOGGING
  bool         nra_verbose;                   // --verbose option
  bool         nra_debug;                     // --debug option
  bool         nra_suppress_warning;          // suppress warnings (default: false)
#endif
  bool         nra_use_stat;                  // --stat option
  dreal::stat  nra_stat;
  bool         nra_proof;                     // --proof option
  bool         nra_readable_proof;            // --readable_proof option
  bool         nra_model;                     // --model option
  std::ofstream nra_model_out;                // file stream for model
  std::string  nra_model_out_name;            // filename for model
  std::ofstream nra_proof_out;                 // file stream for proof
  std::string  nra_proof_out_name;            // filename for proof
  bool         nra_json;                      // --proof option
  std::ofstream nra_json_out;                 // file stream for json (visualization)
  std::string   nra_json_out_name;            // filename for json (visualization)
  bool         nra_parallel;                  // use parallel contractor instead of seq
  bool         nra_check_sat;                 // check constraints when delta-sat
  unsigned long nra_ODE_taylor_order;         // --ode-order option
  unsigned long nra_ODE_grid_size;            // --ode-grid option
  double       nra_ODE_fwd_timeout;           // --ode-fwd-timeout option (unit: msec) (default 0.0, no timeout)
  double       nra_ODE_bwd_timeout;           // --ode-bwd-timeout option (unit: msec) (default 0.0, no timeout)
  double       nra_ODE_step;                  // step control
  bool         nra_ODE_contain;               // contain ODE or not
  bool         nra_ODE_cache;                 // use cache for ODE computation
  bool         nra_ODE_forward_only;          // only use ODE forward pruning (not use ODE backward)
  bool         nra_ODE_parallel;              // solve ODE in parallel or not
  bool         nra_ODE_show_progress;         // show the progress of ODE solving
  bool         nra_ODE_sampling;              // use sampling method (via GSL)
  bool         nra_ODE_trace;                 // print out ode trace
  double       nra_ODE_absolute_tolerance;    // specify the absolute tolerance which will be used by ODE solvers to determine a time-step
  double       nra_ODE_relative_tolerance;    // specify the relative tolerance which will be used by ODE solvers to determine a time-step
  unsigned long nra_aggressive;               // number of samples to use for aggressive sampling
  unsigned long nra_sample;                   // number of samples to use for sound sampling
  unsigned long nra_multiple_soln;            // maximum number of solutions to find
  unsigned long nra_found_soln;               // number of solutions found so far
  bool         nra_polytope;                  // use polytope contractor in IBEX
  bool         nra_simp;                      // use simplification in preprocessing
  bool         nra_ncbt;                      // use nonchronological backtracking in icp
  bool         nra_mcts;                      // use monte carlo tree search in icp
  bool         nra_mcss;                      // use monte carlo stack search in icp
  bool         nra_local_opt;                 // use local optimization to refine counter example (for exist-forall problems)
  bool         nra_worklist_fp;               // use worklist fixpoint algorithm
  bool         nra_multiprune;                // try the top k dimensions to branch on, and see which contract the most before selecting a branch
  bool         nra_multiheuristic;            // run two heuristics simultaneously, return when only one of them completes
  bool         nra_sizegrad_brancher;         // gradient-based branching heuristics
  bool         nra_simulation_thread;         // use a separate thread for simulation in ICP
  bool         nra_precision_output;          // print precision info in case of delta-sat
  unsigned     nra_random_seed;               // seed to random generators (default = std::random_device())
  bool         nra_output_num_nodes;          // print num sat and icp nodes
  std::string  nra_plan_heuristic;
  std::string  nra_plan_domain;               // planning domain
  std::string  nra_plan_problem;              // planning instance
  int          nra_icp_decisions;             // number of icp branch nodes
  bool         nra_show_search_progress;      // print search progress to console
  bool         nra_heuristic_forward;         // use forward search in the heuristic solution
  bool         nra_hybrid_notlearn_clause;    // use clause learning in hybrid heuristic
  unsigned long nra_slack_level;              // determine slack level
  bool         nra_dump_dr;                   // dump dr file

  void inc_icp_decisions() { nra_icp_decisions++; }
  int  icp_decisions() { return nra_icp_decisions; }
  bool         nra_lp;                        // use a combination of ICP and LP
  bool         nra_lp_prune;                  // use the LP solver for pruning
  bool         nra_linear_only;               // use glpk on linear only problems
  bool         nra_scoring;                   // use ICP that use scoring to branch

  void setODEFwdTimeout(double const ode_fwd_timeout);
  void setODEBwdTimeout(double const ode_bwd_timeout);

private:

  std::ofstream     stats_out;                    // File for statistics
  std::ofstream     out;                          // Regular output channel
  std::ofstream     err;                          // Diagnostic output channel
};

#endif
