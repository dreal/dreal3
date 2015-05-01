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

#include <sstream>
#include <string>
#include <gflags/gflags.h>
#include "SMTConfig.h"
#include "config.h"
#include "util/logging.h"
#include "version.h"

using std::string;

DEFINE_double(precision,          0.0, "precision");
DEFINE_bool  (delta,            false, "use delta");
DEFINE_bool  (delta_heuristic,  false, "delta heuristic");
DEFINE_string(bmc_heuristic,       "", "bmc heuristic");
DEFINE_bool  (short_sat,        false, "short sat");
DEFINE_double(ode_step,           0.0, "ode step");
DEFINE_uint64(ode_order,           20, "ode order");
DEFINE_uint64(ode_grid,            16, "ode grid");
DEFINE_uint64(ode_timeout,          0, "ode timeout");
DEFINE_bool  (ode_cache,        false, "ode cache");
DEFINE_bool  (ode_forward_only, false, "ode forward only");
DEFINE_bool  (ode_parallel,     false, "ode parallel");
DEFINE_bool  (proof,            false, "proof");
DEFINE_bool  (readable_proof,   false, "readable proof");
DEFINE_bool  (theory_propagation, false, "use theory propagation / deduction");
DEFINE_bool  (model,            false, "model");
DEFINE_bool  (visualize,        false, "visualize");
DEFINE_bool  (verbose,          false, "verbose");
DEFINE_bool  (debug,            false, "debug mode");
DEFINE_bool  (stat,             false, "show stat");
DEFINE_uint64(aggressive,           0, "number of samples to use for aggressive sampling");
DEFINE_uint64(sample,               0, "number of samples to use for sound sampling");
DEFINE_uint64(multiple_soln,        1, "maximum number of solutions to find");
DEFINE_bool  (polytope,         false, "use polytope contractor in IBEX");

void
SMTConfig::initializeConfig( )
{
  // Set Global Default configuration
  logic                        = UNDEF;
  status                       = l_Undef;
  incremental                  = 0;
  produce_stats                = 1;
  produce_models               = 0;
  produce_proofs               = 0;
  produce_inter                = 0;
  dump_formula                 = 0;
  verbosity                    = 0;
  print_success                = false;
  certification_level          = 0;
  strcpy( certifying_solver, "tool_wrapper.sh" );
  // Set SAT-Solver Default configuration
  sat_theory_propagation       = 0;
  sat_polarity_mode            = 0;
  sat_initial_skip_step        = 1;
  sat_skip_step_factor         = 1;
  sat_restart_first            = 100;
  sat_restart_inc              = 1.1;
  sat_use_luby_restart         = 0;
  sat_learn_up_to_size         = 0;
  sat_temporary_learn          = 1;
  sat_preprocess_booleans      = 1;
  sat_preprocess_theory        = 0;
  sat_centrality               = 18;
  sat_trade_off                = 8192;
  sat_minimize_conflicts       = 1;
  sat_dump_cnf                 = 0;
  sat_dump_rnd_inter           = 0;
  sat_lazy_dtc                 = 0;
  sat_lazy_dtc_burst           = 1;
  // UF-Solver Default configuration
  uf_disable                   = 0;
  uf_theory_propagation        = 1;
  // BV-Solver Default configuration
  bv_disable                   = 0;
  bv_theory_propagation        = 1;
  // DL-Solver Default configuration
  dl_disable                   = 0;
  dl_theory_propagation        = 1;
  // LRA-Solver Default configuration
  lra_disable                  = 0;
  lra_theory_propagation       = 1;
  lra_poly_deduct_size         = 0;
  lra_gaussian_elim            = 1;
  lra_integer_solver           = 0;
  lra_check_on_assert          = 0;
  // Proof parameters
  proof_reduce                 = 0;
  proof_ratio_red_solv         = 0;
  proof_red_time               = 0;
  proof_red_trans              = 0;
  proof_reorder_pivots         = 0;
  proof_remove_mixed           = 0;
  proof_use_sym_inter          = 1;
  proof_certify_inter          = 0;
  // NRA-Solver Default configuration
  nra_precision                = 0.0;
  nra_icp_improve              = 10.0;
  nra_verbose                  = false;
  nra_debug                    = false;
  nra_stat                     = false;
  nra_proof                    = false;
  nra_readable_proof           = false;
  nra_model                    = false;
  nra_ODE_parallel             = false;
  nra_ODE_cache                = false;
  nra_ODE_forward_only         = false;
  nra_ODE_taylor_order         = 20;
  nra_ODE_grid_size            = 16;
  nra_ODE_step                 = 0.0;
  nra_ODE_contain              = false;
  nra_ODE_timeout              = 0.0;
  nra_json                     = false;
  nra_delta_test               = false;
  nra_use_delta_heuristic      = false;
  nra_short_sat                = false;
  nra_bmc_heuristic            = "";
  nra_aggressive               = 0;
  nra_sample                   = 0;
  nra_multiple_soln            = 1;
  nra_found_soln               = 0;
  nra_polytope                 = false;
}

void SMTConfig::parseConfig ( char * f )
{
  FILE * filein = NULL;
  // Open configuration file
  if ( ( filein = fopen( f, "rt" ) ) == NULL )
  {
    // No configuration file is found. Print out
    // the current configuration
    // cerr << "# " << endl;
    cerr << "# WARNING: No configuration file " << f << ". Dumping default setting to " << f << endl;
    ofstream fileout( f );
    printConfig( fileout );
    fileout.close( );
  }
  else
  {
    int line = 0;

    while ( !feof( filein ) )
    {
      line ++;
      char buf[ 128 ];
      char * res = fgets( buf, 128, filein );
      (void)res;
      // Stop if finished
      if ( feof( filein ) )
        break;
      // Skip comments
      if ( buf[ 0 ] == '#' )
        continue;

      char tmpbuf[ 32 ];

      // GENERIC CONFIGURATION
           if ( sscanf( buf, "incremental %d\n"              , &incremental )                   == 1 );
      else if ( sscanf( buf, "produce_stats %d\n"            , &produce_stats )                 == 1 );
      else if ( sscanf( buf, "produce_models %d\n"           , &produce_models )                == 1 );
      else if ( sscanf( buf, "produce_proofs %d\n"           , &produce_proofs )                == 1 );
      else if ( sscanf( buf, "produce_inter %d\n"            , &produce_inter )                 == 1 );
      else if ( sscanf( buf, "regular_output_channel %s\n"   , tmpbuf )                         == 1 )
        setRegularOutputChannel( tmpbuf );
      else if ( sscanf( buf, "diagnostic_output_channel %s\n", tmpbuf )                         == 1 )
        setDiagnosticOutputChannel( tmpbuf );
      else if ( sscanf( buf, "dump_formula %d\n"             , &dump_formula )                  == 1 );
      else if ( sscanf( buf, "verbosity %d\n"                , &verbosity )                     == 1 );
      else if ( sscanf( buf, "certification_level %d\n"      , &certification_level )                     == 1 );
      else if ( sscanf( buf, "certifying_solver %s\n"        , certifying_solver )                     == 1 );
      // SAT SOLVER CONFIGURATION
      else if ( sscanf( buf, "sat_theory_propagation %d\n"   , &(sat_theory_propagation))       == 1 );
      else if ( sscanf( buf, "sat_polarity_mode %d\n"        , &(sat_polarity_mode))            == 1 );
      else if ( sscanf( buf, "sat_initial_skip_step %lf\n"   , &(sat_initial_skip_step))        == 1 );
      else if ( sscanf( buf, "sat_skip_step_factor %lf\n"    , &(sat_skip_step_factor))         == 1 );
      else if ( sscanf( buf, "sat_restart_first %d\n"        , &(sat_restart_first))            == 1 );
      else if ( sscanf( buf, "sat_restart_increment %lf\n"   , &(sat_restart_inc))              == 1 );
      else if ( sscanf( buf, "sat_use_luby_restart %d\n"     , &(sat_use_luby_restart))         == 1 );
      else if ( sscanf( buf, "sat_learn_up_to_size %d\n"     , &(sat_learn_up_to_size))         == 1 );
      else if ( sscanf( buf, "sat_temporary_learn %d\n"      , &(sat_temporary_learn))          == 1 );
      else if ( sscanf( buf, "sat_preprocess_booleans %d\n"  , &(sat_preprocess_booleans))      == 1 );
      else if ( sscanf( buf, "sat_preprocess_theory %d\n"    , &(sat_preprocess_theory))        == 1 );
      else if ( sscanf( buf, "sat_centrality %d\n"           , &(sat_centrality))               == 1 );
      else if ( sscanf( buf, "sat_trade_off %d\n"            , &(sat_trade_off))                == 1 );
      else if ( sscanf( buf, "sat_minimize_conflicts %d\n"   , &(sat_minimize_conflicts))       == 1 );
      else if ( sscanf( buf, "sat_dump_cnf %d\n"             , &(sat_dump_cnf))                 == 1 );
      else if ( sscanf( buf, "sat_dump_rnd_inter %d\n"       , &(sat_dump_rnd_inter))           == 1 );
      else if ( sscanf( buf, "sat_lazy_dtc %d\n"             , &(sat_lazy_dtc))                 == 1 );
      else if ( sscanf( buf, "sat_lazy_dtc_burst %d\n"       , &(sat_lazy_dtc_burst))           == 1 );
      // PROOF PRODUCTION CONFIGURATION
      else if ( sscanf( buf, "proof_reduce %d\n"             , &(proof_reduce))                 == 1 );
      else if ( sscanf( buf, "proof_ratio_red_solv %lf\n"    , &(proof_ratio_red_solv))         == 1 );
      else if ( sscanf( buf, "proof_red_time %lf\n"          , &(proof_red_time))               == 1 );
      else if ( sscanf( buf, "proof_red_trans %d\n"          , &(proof_red_trans))              == 1 );
      else if ( sscanf( buf, "proof_reorder_pivots %d\n"     , &(proof_reorder_pivots))         == 1 );
      else if ( sscanf( buf, "proof_remove_mixed %d\n"       , &(proof_remove_mixed))           == 1 );
      else if ( sscanf( buf, "proof_use_sym_inter %d\n"      , &(proof_use_sym_inter))          == 1 );
      else if ( sscanf( buf, "proof_certify_inter %d\n"      , &(proof_certify_inter))          == 1 );
      // EUF SOLVER CONFIGURATION
      else if ( sscanf( buf, "uf_disable %d\n"               , &(uf_disable))                   == 1 );
      else if ( sscanf( buf, "uf_theory_propagation %d\n"    , &(uf_theory_propagation))        == 1 );
      // BV SOLVER CONFIGURATION
      else if ( sscanf( buf, "bv_disable %d\n"               , &(bv_disable))                   == 1 );
      else if ( sscanf( buf, "bv_theory_propagation %d\n"    , &(bv_theory_propagation))        == 1 );
      // DL SOLVER CONFIGURATION
      else if ( sscanf( buf, "dl_disable %d\n"               , &(dl_disable))                   == 1 );
      else if ( sscanf( buf, "dl_theory_propagation %d\n"    , &(dl_theory_propagation))        == 1 );
      // LRA SOLVER CONFIGURATION
      else if ( sscanf( buf, "lra_disable %d\n"              , &(lra_disable))                  == 1 );
      else if ( sscanf( buf, "lra_theory_propagation %d\n"   , &(lra_theory_propagation))       == 1 );
      else if ( sscanf( buf, "lra_poly_deduct_size %d\n"     , &(lra_poly_deduct_size))         == 1 );
      else if ( sscanf( buf, "lra_gaussian_elim %d\n"        , &(lra_gaussian_elim))            == 1 );
      else if ( sscanf( buf, "lra_integer_solver %d\n"       , &(lra_integer_solver))           == 1 );
      else if ( sscanf( buf, "lra_check_on_assert %d\n"      , &(lra_check_on_assert))          == 1 );
      else
      {
        opensmt_error2( "unrecognized option ", buf );
      }
    }

    // Close
    fclose( filein );
  }

  if ( produce_stats )  stats_out.open( "stats.out" );
}

void SMTConfig::printConfig ( ostream & out )
{
  out << "#" << endl;
  out << "# OpenSMT Configuration File" << endl;
  out << "# . Options may be written in any order" << endl;
  out << "# . Unrecongnized options will throw an error" << endl;
  out << "# . Use '#' for line comments" << endl;
  out << "# . Remove this file and execute opensmt to generate a new copy with default values" << endl;
  out << "#" << endl;
  out << "# GENERIC CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enables incrementality (SMT-LIB 2.0 script-compatible)" << endl;
  out << "incremental "                << incremental << endl;
  out << "# Regular output channel " << endl;
  out << "regular_output_channel stdout" << endl;
  out << "# Diagnostic output channel " << endl;
  out << "diagnostic_output_channel stderr" << endl;
  out << "# Prints statistics in stats.out" << endl;
  out << "produce_stats "              << produce_stats << endl;
  out << "# Prints models" << endl;
  out << "produce_models "             << produce_models << endl;
  out << "# Prints proofs"  << endl;
  out << "produce_proofs "             << produce_proofs << endl;
  out << "# Prints interpolants" << endl;
  out << "produce_inter "              << produce_inter << endl;
  out << "# Dumps input formula (debugging)" << endl;
  out << "dump_formula "               << dump_formula << endl;
  out << "# Choose verbosity level" << endl;
  out << "verbosity "                  << verbosity << endl;
  out << "# Choose certification level" << endl;
  out << "# 0 - don't certify" << endl;
  out << "# 1 - certify conflicts" << endl;
  out << "# 2 - certify conflicts, deductions " << endl;
  out << "# 3 - certify conflicts, deductions, theory calls " << endl;
  out << "certification_level " << certification_level << endl;
  out << "certifying_solver " << certifying_solver << endl;
  out << "#" << endl;
  out << "# SAT SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enables theory propagation" << endl;
  out << "sat_theory_propagation "     << sat_theory_propagation << endl;
  out << "# Polarity mode for TAtoms and BAtoms" << endl;
  out << "# 0 - all true" << endl;
  out << "# 1 - all false" << endl;
  out << "# 2 - all random" << endl;
  out << "# 3 - heuristic TAtoms, true BAtoms" << endl;
  out << "# 4 - heuristic TAtoms, false BAtoms" << endl;
  out << "# 5 - heuristic TAtoms, random BAtoms" << endl;
  out << "sat_polarity_mode "  << sat_polarity_mode << endl;
  out << "# Initial and step factor for theory solver calls" << endl;
  out << "sat_initial_skip_step "   << sat_initial_skip_step << endl;
  out << "sat_skip_step_factor "    << sat_skip_step_factor << endl;
  out << "# Initial and increment conflict limits for restart" << endl;
  out << "sat_restart_first "       << sat_restart_first << endl;
  out << "sat_restart_increment "   << sat_restart_inc << endl;
  out << "sat_use_luby_restart "    << sat_use_luby_restart << endl;
  out << "# Learn theory-clauses up to the specified size (0 learns nothing)" << endl;
  out << "sat_learn_up_to_size "    << sat_learn_up_to_size << endl;
  out << "sat_temporary_learn "     << sat_temporary_learn << endl;
  out << "# Preprocess variables and clauses when possible" << endl;
  out << "sat_preprocess_booleans " << sat_preprocess_booleans << endl;
  out << "sat_preprocess_theory "   << sat_preprocess_theory << endl;
  out << "sat_centrality "          << sat_centrality << endl;
  out << "sat_trade_off "           << sat_trade_off << endl;
  out << "sat_minimize_conflicts "  << sat_minimize_conflicts << endl;
  out << "sat_dump_cnf "            << sat_dump_cnf << endl;
  out << "sat_dump_rnd_inter "      << sat_dump_rnd_inter << endl;
  out << "sat_lazy_dtc "            << sat_lazy_dtc << endl;
  out << "sat_lazy_dtc_burst "      << sat_lazy_dtc_burst << endl;
  out << "#" << endl;
  out << "# PROOF TRANSFORMER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "proof_reduce "             << proof_reduce << endl;
  out << "# Reduction timeout w.r.t. solving time" << endl;
  out << "proof_ratio_red_solv "     << proof_ratio_red_solv << endl;
  out << "# Reduction timeout" << endl;
  out << "proof_red_time "           << proof_red_time << endl;
  out << "# Number of reduction iterations" << endl;
  out << "proof_red_trans "          << proof_red_trans << endl;
  out << "proof_reorder_pivots "     << proof_reorder_pivots << endl;
  out << "proof_remove_mixed "       << proof_remove_mixed << endl;
  out << "proof_use_sym_inter "      << proof_use_sym_inter << endl;
  out << "# Choose certification level for interpolants" << endl;
  out << "# 0 - don't certify" << endl;
  out << "# 1 - certify final interpolant" << endl;
  out << "# 2 - certify final and theory interpolants" << endl;
  out << "proof_certify_inter "      << proof_certify_inter << endl;
  out << "#" << endl;
  out << "# EUF SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "uf_disable "               << uf_disable << endl;
  out << "uf_theory_propagation "    << uf_theory_propagation << endl;
  out << "#" << endl;
  out << "# BITVECTOR SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "bv_disable "               << bv_disable << endl;
  out << "bv_theory_propagation "    << bv_theory_propagation << endl;
  out << "#" << endl;
  out << "# DIFFERENCE LOGIC SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "dl_disable "               << dl_disable << endl;
  out << "dl_theory_propagation "    << dl_theory_propagation << endl;
  out << "#" << endl;
  out << "# LINEAR RATIONAL ARITHMETIC SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "lra_disable "              << lra_disable << endl;
  out << "lra_theory_propagation "   << lra_theory_propagation << endl;
  out << "lra_poly_deduct_size "     << lra_poly_deduct_size << endl;
  out << "lra_gaussian_elim "        << lra_gaussian_elim << endl;
  out << "lra_check_on_assert "      << lra_check_on_assert << endl;
}

void
SMTConfig::parseCMDLine( int /* argc */
                       , char * /* argv */ [] )
{
  nra_precision           = FLAGS_precision;
  nra_delta_test          = FLAGS_delta;
  nra_use_delta_heuristic = FLAGS_delta_heuristic;
  nra_short_sat           = FLAGS_short_sat;
  nra_bmc_heuristic       = FLAGS_bmc_heuristic;
  nra_ODE_step            = FLAGS_ode_step;
  nra_ODE_taylor_order    = FLAGS_ode_order;
  nra_ODE_grid_size       = FLAGS_ode_grid;
  nra_ODE_timeout         = FLAGS_ode_timeout;
  nra_ODE_cache           = FLAGS_ode_cache;
  nra_ODE_forward_only    = FLAGS_ode_forward_only;
  nra_ODE_parallel        = FLAGS_ode_parallel;
  nra_readable_proof      = FLAGS_readable_proof;
  sat_theory_propagation  = FLAGS_theory_propagation;
  nra_proof               = nra_readable_proof || FLAGS_proof;
  nra_model               = FLAGS_model;
  nra_json                = FLAGS_visualize;
  nra_verbose             = FLAGS_verbose || FLAGS_debug;
  nra_debug               = FLAGS_debug;
  nra_stat                = FLAGS_stat;
  nra_aggressive          = FLAGS_aggressive;
  nra_sample              = FLAGS_sample;
  nra_multiple_soln       = FLAGS_multiple_soln;
  nra_polytope            = FLAGS_polytope;

  if (nra_proof) {
      /* Open file stream */
      nra_proof_out_name = string(filename) + ".proof";
      nra_proof_out.open (nra_proof_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
      if(nra_proof_out.fail()) {
          cout << "Cannot create a file: " << nra_proof_out_name << endl;
          exit( 1 );
      }
  }
  if (nra_model) {
      nra_model_out_name = string(filename) + ".model";
  }
  if (nra_json) {
      nra_json_out_name = string(filename) + ".json";
      /* Open file stream */
      nra_json_out.open (nra_json_out_name.c_str(), std::ofstream::out | std::ofstream::trunc );
      if(nra_json_out.fail()) {
          cout << "Cannot create a file: " << filename << endl;
          exit( 1 );
      }
  }
  if (nra_verbose || nra_debug) {
      verbosity = 10;
  }
  FLAGS_log_prefix = 0;
  FLAGS_logtostderr = 1;
  if (nra_debug) { FLAGS_v = 4; }
  else if (nra_verbose) { FLAGS_v = 3; }
  else { FLAGS_v = 0; }
}

void SMTConfig::printHelp( )
{
  const char help_string[]
      =
      "Usage: ./solver [OPTION] filename\n"
      "where OPTION can be\n"
      "  --help [-h]              print this help\n"
      "  --config=<filename>      use configuration file <filename>\n"
      "\n"
      "  --precision=<double>     set precision (default 0.001)\n"
      "                           this overrides the value specified in input files\n"
      "\n"
      "  --delta                  interpret precision as delta instead of epsilon (default)\n"
      "\n"
      "  --delta-heuristic        use residual delta to select variables to split\n"
      "\n"
      "  --short-sat              short cut SAT solver assignments if SAT\n"
      "\n"
      "  --proof                  the solver produces an addition file \"filename.proof\"\n"
      "                           upon termination, and provides the following information:\n"
      "                             1. If the answer is delta-sat, then filename.proof contains\n"
      "                                a witnessing solution, plugged into a δ-perturbation of\n"
      "                                the original formula, such that the correctness can be\n"
      "                                easily checked externally.\n"
      "                             2. If the answer is unsat, then filename.proof contains a\n"
      "                                trace of the solving steps, which can be verified as a\n"
      "                                proof tree that establishes the unsatisfiability of the\n"
      "                                formula. This file can be the input of a stand-alone proof\n"
      "                                checker.\n"
      "\n"
      "   --verbose               the solver will output the detailed decision traces along with\n"
      "                           the solving process. That is, it will print the branch-and-prune\n"
      "                           trace in the constraint propagation procedures for checking\n"
      "                           consistency of theory atoms, as well as DPLL-level\n"
      "                           assert/check/backtracking operations.\n"
#ifdef SUPPORT_ODE
      "\n"
      "   --ode-order             specify the maximum order that will be used in Taylor method ODE solving\n"
      "                           (Default: 20)\n"
      "\n"
      "   --ode-grid              specify the number of grids that we use in ODE solving\n"
      "                           (Default: 16)\n"
      "\n"
      "   --ode-timeout           specify the timeout (msec) to be used in single ODE solving step\n"
      "                           (Default: +oo)\n"
      "\n"
      "   --ode-cache             enable reusing ODE computation by caching them\n"
      "                           (Default: false)\n"
      "\n"
      "   --ode-forward-only      use forward ODE pruning and do not use backward pruning\n"
      "                           (Default: false, use both of them)\n"
      "\n"
      "   --ode-parallel          specify to solve ODEs in parallel\n"
      "                           (Default: false)\n"
      "\n"
      "   --ode-step              specify the step size (positive float) in ODE solving\n"
      "                           (Default: automatically decided by CAPD)\n"
      "\n"
      "   --visualize             print out data for the visualization of ODE solving\n"
      "                           which will be saved to \"filename.json\".\n"
#endif
      ;
  cerr << help_string;
}
