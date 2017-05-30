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

#include <ezOptionParser/ezOptionParser.hpp>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <fstream>
#include <limits>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

#include "./dreal_config.h"
#include "SMTConfig.h"
#include "util/git_sha1.h"
#include "util/logging.h"
#include "version.h"

#ifdef LOGGING
INITIALIZE_EASYLOGGINGPP
#endif

using std::cerr;
using std::cout;
using std::endl;
using std::numeric_limits;
using std::ofstream;
using std::ostream;
using std::ostringstream;
using std::string;
using std::vector;
using std::logic_error;
using std::random_device;

void
SMTConfig::initializeConfig( )
{
  // Set Global Default configuration
  logic                        = UNDEF;
  status                       = l_Undef;
  incremental                  = 1;
  produce_stats                = 1;
  produce_models               = 0;
  produce_proofs               = 0;
  produce_inter                = 0;
  dump_formula                 = 0;
  verbosity                    = 0;
  print_success                = true;
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
  sat_preprocess_booleans      = 0;
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
  nra_theory_propagation       = 0;
  nra_precision                = 0.0;
  nra_verbose                  = false;
  nra_debug                    = false;
  nra_use_stat                 = false;
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
  nra_ODE_fwd_timeout          = 0.0;
  nra_ODE_bwd_timeout          = 0.0;
  nra_ODE_show_progress        = false;
  nra_ODE_sampling             = false;
  nra_ODE_trace                = false;
  nra_ODE_absolute_tolerance   = 1e-20;
  nra_ODE_relative_tolerance   = 1e-20;
  nra_json                     = false;
  nra_parallel                 = false;
  nra_check_sat                = false;
  nra_delta_test               = false;
  nra_use_delta_heuristic      = false;
  nra_short_sat                = false;
  nra_bmc_heuristic            = "";
  nra_aggressive               = 0;
  nra_sample                   = 0;
  nra_multiple_soln            = 1;
  nra_found_soln               = 0;
  nra_polytope                 = false;
  nra_simp                     = true;
  nra_ncbt                     = false;
  nra_mcts                     = false;
  nra_mcss                     = false;
  nra_local_opt                = false;
  nra_worklist_fp              = false;
  nra_simulation_thread        = false;
  nra_multiprune               = false;
  nra_multiheuristic           = false;
  nra_sizegrad_brancher        = false;
  nra_precision_output         = true;
  nra_random_seed              = random_device{}();
  nra_output_num_nodes         = false;
  nra_icp_decisions            = 0;
  nra_show_search_progress     = false;
  nra_heuristic_forward        = false;
  nra_hybrid_notlearn_clause   = false;
  nra_slack_level              = 0;
  nra_lp                       = false;
  nra_lp_prune                 = false;
  nra_linear_only              = false;
  nra_scoring                  = false;
  nra_suppress_warning         = false;
  nra_dump_dr                  = false;
  initLogging();
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
      else if ( sscanf( buf, "certification_level %d\n"      , &certification_level )           == 1 );
      else if ( sscanf( buf, "certifying_solver %s\n"        , certifying_solver )              == 1 );
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

void printUsage(ez::ezOptionParser & opt) {
    string usage;
    opt.getUsage(usage, 160);
    cout << usage;
    exit(1);
}

void
SMTConfig::parseCMDLine( int argc
                         , const char * argv [] ) {
    // For more information, Read
    // https://github.com/dreal-deps/ezoptionparser/blob/master/examples/complete.cpp
    ez::ezOptionParser opt;
    opt.add("", false, 0, 0,
            "Display usage instructions.",
            "-h", "-help", "--help", "--usage");
    opt.add("", false, 0, 0,
            "print out version information.",
            "--version");
    opt.add("", false, 1, 0,
            "set precision (default 0.001)\n"
            "this overrides the value specified in input files",
            "--precision");
    opt.add("", false, 0, 0,
            "do not print precision in case of delta-sat",
            "--no-precision-output");
    opt.add("", false, 0, 0,
            "interpret precision as delta instead of epsilon",
            "--delta", "--range-delta");
    opt.add("", false, 0, 0,
            "use residual delta to select variables to split",
            "--delta-heuristic", "--delta_heuristic");
    opt.add("" , false, 1, 0,
            "BMC heuristic",
            "--bmc-heuristic", "--bmc_heuristic");
    opt.add("" , false, 1, 0,
            "PDDL+ heuristic",
            "--plan-heuristic", "--plan_heuristic");
    opt.add("", false, 0, 0,
            "short cut SAT solver assignments if SAT",
            "--short-sat", "--short_sat");
    opt.add("", false, 1, 0,
            "manually specify the step size (positive double) in ODE solving (default: automatic control)",
            "--ode-step", "--ode_step");
    opt.add("", false, 1, 0,
            "specify the absolute tolerance which is used by ODE solvers to determine a time-step (default: 1e-20)",
            "--ode-absolute-tolerance", "--ode-abs-tol");
    opt.add("", false, 1, 0,
            "specify the relative tolerance which is used by ODE solvers to determine a time-step (default: 1e-20)",
            "--ode-relative-tolerance", "--ode-rel-tol");
    opt.add("", false, 1, 0,
            "specify the maximum order that will be used in Taylor method ODE solving (Default: 20)",
            "--ode-order", "--ode_order");
    opt.add("", false, 1, 0,
            "specify the number of grids that we use in ODE solving (default: 16)",
            "--ode-grid", "--ode_grid");
    opt.add("", false, 1, 0,
            "specify the timeout (msec) for ODE pruning steps (both for forward and backward) (default: +oo)",
            "--ode-timeout");
    opt.add("", false, 1, 0,
            "specify the timeout (msec) for a forward ODE pruning step (default: +oo)",
            "--ode-forward-timeout", "--ode-fwd-timeout");
    opt.add("", false, 1, 0,
            "specify the timeout (msec) for a backward ODE pruning step (default: +oo)",
            "--ode-backward-timeout", "--ode-bwd-timeout");
    opt.add("", false, 0, 0,
            "enable reusing ODE computation by caching them",
            "--ode-cache", "--ode_cache");
    opt.add("", false, 0, 0,
            "use only forward ODE pruning and do not use backward pruning",
            "--ode-forward-only", "--ode_forward_only");
    opt.add("", false, 0, 0,
            "specify to solve ODEs in parallel",
            "--ode-parallel", "--ode_parallel");
    opt.add("", false, 0, 0,
            "show the progress of ODE computation",
            "--ode-show-progress", "--ode_show_progress");
    opt.add("", false, 0, 0,
            "use sampling method for ODE (using GNU GSL)",
            "--ode-sampling", "--ode_sampling");
    opt.add("", false, 0, 0,
            "output ODE traces",
            "--ode-trace", "--ode_trace");
    opt.add("", false, 0, 0,
            "produce an addition file \"filename.proof\" which contains a proof for UNSAT",
            "--proof");
    opt.add("", false, 0, 0,
            "generate human-readable proof",
            "--readable-proof", "--readable_proof");
    opt.add("", false, 0, 0,
            "use theory propagation",
            "--theory-propagation", "--theory_propagation");
    opt.add("", false, 0, 0,
            "output delta-sat model if found",
            "--model");
    opt.add("", false, 0, 0,
            "output visualization file (.json)",
            "--visualize", "--vis");
    opt.add("", false, 0, 0,
            "enable parallelization",
            "--parallel");
    opt.add("", false, 0, 0,
            "check constraints when delta-sat",
            "--check-sat");

    opt.add("", false, 1, 0,
            "perform slacking up to a level {0(default), 1, 2}",
            "--slack-level");

#ifdef LOGGING
    opt.add("", false, 0, 0,
            "output debugging messages",
            "--debug");
    opt.add("", false, 0, 0,
            "output info messages",
            "--verbose");
    opt.add("", false, 0, 0,
            "suppress warning messages",
            "--suppress-warning");
#endif
    opt.add("", false, 0, 0,
            "output solving stats",
            "--stat");
    opt.add("", false, 1, 0,
            "number of samples to use for aggressive sampling",
            "--aggressive");
    opt.add("", false, 1, 0,
            "number of samples to use for sound sampling",
            "--sample");
    opt.add("", false, 1, 0,
            "maximum number of solutions to find",
            "--multiple-soln", "--multiple_soln", "--multiple-solution");
    opt.add("", false, 0, 0,
            "use polytope contractor in IBEX"
#ifndef USE_CLP
            " (not available in this build, need CLP)"
#endif
            , "--polytope");
    opt.add("", false, 0, 0,
            "use simplification in preprocessing (default: on)",
            "--simp");
    opt.add("", false, 0, 0,
            "do not use simplification in preprocessing",
            "--no-simp");
    opt.add("", false, 0, 0,
            "use non-chronological backtracking in ICP loop",
            "--ncbt");
    opt.add("", false, 0, 0,
            "use Monte Carlo tree search in ICP loop",
            "--mcts");
    opt.add("", false, 0, 0,
            "use Monte Carlo Stack search in ICP loop",
            "--mcss");
    opt.add("", false, 0, 0,
            "use local optimization to refine counter example (for exist-forall problems)"
#ifndef USE_NLOPT
            " (not available in this build, need NLOPT)"
#endif
            , "--local-opt");
    opt.add("", false, 0, 0,
            "use worklist fixpoint algorithm",
            "--worklist-fp");
    opt.add("", false, 0, 0,
            "use a separate simulation thread in ICP",
            "--simulation");
    opt.add("", false, 0, 0,
            "more smartly select dimension to branch on based on contraction after split",
            "--multiprune");
    opt.add("", false, 0, 0,
            "run two heuristics simultaneously, finish when the first finishes",
            "--multiheuristic");
    opt.add("", false, 0, 0,
            "use gradient-based branching heuristics",
            "--gradbranch");
    opt.add("", false, 0, 0,
            "read formula from standard input",
            "--in");
    opt.add("", false, 1, 0,
            "specify the random seed (default: non-deterministic random number from std::random_device())",
            "--random-seed", "--random_seed");
    opt.add("", false, 0, 0,
            "Activate satelite on booleans (default: off)",
            "--sat-prep-bool", "--sat-preprocess-booleans", "--sat_preprocess_booleans");
    opt.add("", false, 0, 0,
            "use heuristic forward search",
            "--heuristic_forward");
    opt.add("", false, 0, 0,
            "use heuristic forward search",
            "--show-search");
    opt.add("", false, 0, 0,
            "use hybrid solver clause learning",
            "--no-hybrid-clause-learning");
    opt.add("", false, 0, 0,
            "only invoke linear solvers on a purely linear problem"
#ifndef USE_GLPK
            " (not available in this build, need GLPK)"
#endif
            , "--linear-only");
    opt.add("", false, 0, 0,
            "use a combination of ICP and LP"
#ifndef USE_GLPK
            " (not available in this build, need GLPK)"
#endif
            , "--lp-icp");
    opt.add("", false, 0, 0,
            "use a combination of ICP and LP and also use the LP for pruning"
#ifndef USE_GLPK
            " (not available in this build, need GLPK)"
#endif
            , "--lp-icp-prune");
    opt.add("", false, 0, 0,
            "use modified ICP that use scoring for branching",
            "--scoring-icp");
    opt.add("", false, 0, 0,
            "Dump dr file without solving",
             "--dump-dr");

    opt.parse(argc, argv);
    opt.overview  = "dReal ";
    opt.overview += "v" + string(PACKAGE_VERSION);
    opt.overview += " (commit " + string(dreal::getGitSHA1()).substr(0, 12) + ")";

    if (opt.isSet("--version")) {
        // Usage Information
        cout << opt.overview << endl;
        exit(0);
    }

    // Usage Information
    opt.overview += " : delta-complete SMT solver";
    opt.syntax    = "dReal [OPTIONS] <input file>";

    if (opt.isSet("-h")) {
        printUsage(opt);
    }

    // Extract Boolean Args
    nra_delta_test          = opt.isSet("--delta");
    nra_use_delta_heuristic = opt.isSet("--delta-heuristic");
    nra_short_sat           = opt.isSet("--short-sat");
    nra_ODE_cache           = opt.isSet("--ode-cache");
    nra_ODE_forward_only    = opt.isSet("--ode-forward-only");
    nra_ODE_parallel        = opt.isSet("--ode-parallel");
    nra_ODE_show_progress   = opt.isSet("--ode-show-progress");
    nra_ODE_sampling        = opt.isSet("--ode-sampling");
    nra_ODE_trace           = opt.isSet("--ode-trace");
    nra_readable_proof      = opt.isSet("--readable-proof");
    nra_theory_propagation  = opt.isSet("--theory-propagation");
    nra_proof               = nra_readable_proof || opt.isSet("--proof");
    nra_check_sat           = opt.isSet("--check-sat");
    nra_model               = nra_check_sat || opt.isSet("--model");
    if (nra_model) { produce_models = true; }
    nra_json                = opt.isSet("--visualize");
    nra_parallel            = opt.isSet("--parallel");
#ifdef LOGGING
    nra_verbose             = opt.isSet("--verbose") || opt.isSet("--debug");
    nra_debug               = opt.isSet("--debug");
    nra_suppress_warning    = opt.isSet("--suppress-warning");
#endif
    nra_use_stat            = opt.isSet("--stat");
    nra_polytope            = opt.isSet("--polytope");
#ifndef USE_CLP
    if (nra_polytope) {
      cerr << "--polytope option is used, but this option is not available in this build. " << endl
           << "To use it, please install CLP and re-build dReal." << endl;
      nra_polytope = false;
    }
#endif
    nra_simp                =!opt.isSet("--no-simp");
    nra_ncbt                = opt.isSet("--ncbt");
    nra_mcts                = opt.isSet("--mcts");
    nra_mcss                = opt.isSet("--mcss");
    nra_local_opt           = opt.isSet("--local-opt");
#ifndef USE_NLOPT
    if (nra_local_opt) {
      cerr << "--local-opt option is used, but this option is not available in this build. " << endl
           << "To use it, please configure dReal with -DUSE_NLOPT=ON cmake option." << endl;
      nra_local_opt = false;
    }
#endif
    nra_worklist_fp         = opt.isSet("--worklist-fp");
    nra_simulation_thread   = opt.isSet("--simulation");
    nra_multiprune          = opt.isSet("--multiprune");
    nra_multiheuristic      = opt.isSet("--multiheuristic");
    nra_sizegrad_brancher   = opt.isSet("--gradbranch");
    nra_precision_output    =!opt.isSet("--no-precision-output");
    sat_preprocess_booleans = opt.isSet("--sat-prep-bool");
    nra_show_search_progress= opt.isSet("--show-search");
    nra_heuristic_forward   = opt.isSet("--heuristic_forward");
    nra_hybrid_notlearn_clause = opt.isSet("--no-hybrid-clause-learning");

    nra_lp                  = opt.isSet("--lp-icp") || opt.isSet("--lp-icp-prune");
    nra_lp_prune            = opt.isSet("--lp-icp-prune");
    nra_linear_only         = opt.isSet("--linear-only");
#ifndef USE_GLPK
    if (nra_lp) {
      cerr << "--lp-icp option (or --lp-icp-prune) is used, but this option is not available in this build. " << endl
           << "To use it, please configure dReal with -DUSE_GLPK=ON cmake option." << endl;
      nra_lp = false;
    }
    if (nra_lp_prune) {
      cerr << "--lp-icp-prune option is used, but this option is not available in this build. " << endl
           << "To use it, please configure dReal with -DUSE_GLPK=ON cmake option." << endl;
      nra_lp = false;
    }
    if (nra_linear_only) {
      cerr << "--linear-only option is used, but this option is not available in this build. " << endl
           << "To use it, please configure dReal with -DUSE_GLPK=ON cmake option." << endl;
      nra_lp = false;
    }
#endif
    nra_scoring             = opt.isSet("--scoring-icp");
    nra_dump_dr             = opt.isSet("--dump-dr");

    // Extract Double Args
    if (opt.isSet("--precision")) { opt.get("--precision")->getDouble(nra_precision); }
    if (opt.isSet("--ode-step")) { opt.get("--ode-step")->getDouble(nra_ODE_step); }
    if (opt.isSet("--ode-absolute-tolerance")) { opt.get("--ode-absolute-tolerance")->getDouble(nra_ODE_absolute_tolerance); }
    if (opt.isSet("--ode-relative-tolerance")) { opt.get("--ode-relative-tolerance")->getDouble(nra_ODE_relative_tolerance); }
    if (opt.isSet("--ode-step")) { opt.get("--ode-step")->getDouble(nra_ODE_step); }
    if (opt.isSet("--ode-fwd-timeout")) {
        try {
            double ode_fwd_timeout = 0.0;
            opt.get("--ode-fwd-timeout")->getDouble(ode_fwd_timeout);
            setODEFwdTimeout(ode_fwd_timeout);
        } catch (logic_error & e) {
            cerr << e.what() << endl;
            printUsage(opt);
        }
    }
    if (opt.isSet("--ode-bwd-timeout")) {
        try {
            double ode_bwd_timeout = 0.0;
            opt.get("--ode-bwd-timeout")->getDouble(ode_bwd_timeout);
            setODEBwdTimeout(ode_bwd_timeout);
        } catch (logic_error & e) {
            cerr << e.what() << endl;
            printUsage(opt);
        }
    }
    if (opt.isSet("--ode-timeout") && opt.isSet("--ode-fwd-timeout")) {
        cerr << "ERROR: --ode-timeout option cannot be used with --ode-forward-timeout option." << endl;
        printUsage(opt);
    }
    if (opt.isSet("--ode-timeout") && opt.isSet("--ode-bwd-timeout")) {
        cerr << "ERROR: --ode-timeout option cannot be used with --ode-backward-timeout option." << endl;
        printUsage(opt);
    }
    if (opt.isSet("--ode-timeout")) {
        try {
            double ode_timeout = 0.0;
            opt.get("--ode-timeout")->getDouble(ode_timeout);
            setODEFwdTimeout(ode_timeout);
            setODEBwdTimeout(ode_timeout);
        } catch (logic_error & e) {
            cerr << e.what() << endl;
            printUsage(opt);
        }
    }

    // Extract String Args
    if (opt.isSet("--bmc-heuristic")) { opt.get("--bmc-heuristic")->getString(nra_bmc_heuristic); }
    if (opt.isSet("--plan-heuristic")) { opt.get("--plan-heuristic")->getString(nra_plan_heuristic); }

    // Extract ULong Args
    if (opt.isSet("--ode-order")) { opt.get("--ode-order")->getULong(nra_ODE_taylor_order); }
    if (opt.isSet("--ode-grid")) { opt.get("--ode-grid")->getULong(nra_ODE_grid_size); }
    if (opt.isSet("--aggressive")) { opt.get("--aggressive")->getULong(nra_aggressive); }
    if (opt.isSet("--sample")) { opt.get("--sample")->getULong(nra_sample); }
    if (opt.isSet("--multiple-soln")) { opt.get("--multiple-soln")->getULong(nra_multiple_soln); }
    if (opt.isSet("--slack-level")) {
      opt.get("--slack-level")->getULong(nra_slack_level);
      if (nra_slack_level > 2) {
        cerr << "ERROR: --slack-level <N> should take one of {0, 1, 2}.\n\n";
        printUsage(opt);
      }
    }
    if (opt.isSet("--random-seed")) {
        // Hack: ezOptionParser doesn't have an API to read 'unsigned
        // int' ( it only supports 'int' and 'unsigned long'). We
        // first read a 'int' random and cast it to unsigned
        // int. Since it's for random seed, it's not really important
        // to keep the exact number.
        int tmp = 0;
        opt.get("--random-seed")->getInt(tmp);
        nra_random_seed = static_cast<unsigned>(tmp);
    }

    vector<string> badOptions;
    if(!opt.gotRequired(badOptions)) {
        for (size_t i = 0; i < badOptions.size(); ++i)
            cerr << "ERROR: Missing required option " << badOptions[i] << ".\n\n";
        printUsage(opt);
    }

    if(!opt.gotExpected(badOptions)) {
        for (size_t i = 0; i < badOptions.size(); ++i)
            cerr << "ERROR: Got unexpected number of arguments for option " << badOptions[i] << ".\n\n";
        printUsage(opt);
    }

    // Set up filename
    filename = "";
    bool stdin_is_on = opt.isSet("--in");
    vector<string*> args;
    args.insert(args.end(), opt.firstArgs.begin() + 1, opt.firstArgs.end());
    args.insert(args.end(), opt.unknownArgs.begin(),   opt.unknownArgs.end());
    args.insert(args.end(), opt.lastArgs.begin(),      opt.lastArgs.end());

    if (stdin_is_on && args.size() > 0) {
        printUsage(opt);
    }

    if (!stdin_is_on && args.size() == 0) {
        printUsage(opt);
    }

    if (args.size() > 1) {
        printUsage(opt);
    }

    assert((args.size() == 1 && !stdin_is_on) ||
           (args.size() == 0 && stdin_is_on));

    if (args.size() == 1) {
        filename = *args[0];
        if (filename.length() > 0) {
            struct stat s;
            if(stat(filename.c_str(),&s) != 0 || !(s.st_mode & S_IFREG)) {
                opensmt_error2( "can't open file:", filename );
            }
        }
    } else {
        filename = "output";
    }

    // --proof
    if (nra_proof) {
        /* Open file stream */
        nra_proof_out_name = filename + ".proof";
        nra_proof_out.open (nra_proof_out_name.c_str(), ofstream::out | ofstream::trunc);
        if(nra_proof_out.fail()) {
            cout << "Cannot create a file: " << nra_proof_out_name << endl;
            exit( 1 );
        }
    }

    // --model
    if (nra_model) {
        nra_model_out_name = filename + ".model";
    }

    // --visualize
    if (nra_json) {
        nra_json_out_name = filename + ".json";
        /* Open file stream */
        nra_json_out.open (nra_json_out_name.c_str(), ofstream::out | ofstream::trunc );
        if(nra_json_out.fail()) {
            cout << "Cannot create a file: " << filename << endl;
            exit( 1 );
        }
    }

#ifdef LOGGING
    // --verbose, --debug
    if (nra_verbose || nra_debug) {
        verbosity = 10;
    }

    // logging
    initLogging();
    if (nra_debug) {
        setVerbosityDebugLevel();
    } else if (nra_verbose) {
        setVerbosityInfoLevel();
    } else if (nra_suppress_warning) {
      void setVerbosityErrorLevel();
    } else {
        setVerbosityWarningLevel();
    }
#endif
}

void SMTConfig::initLogging() {
    static bool already_init = false;
    if (!already_init) {
        el::Loggers::reconfigureAllLoggers(el::ConfigurationType::Format, "%msg");
        el::Loggers::reconfigureAllLoggers(el::ConfigurationType::ToFile, "false");
        already_init = true;
    }
}

void SMTConfig::setVerbosityDebugLevel() {
    el::Loggers::setVerboseLevel(DREAL_DEBUG_LEVEL);
}

void SMTConfig::setVerbosityInfoLevel() {
    el::Loggers::setVerboseLevel(DREAL_INFO_LEVEL);
}

void SMTConfig::setVerbosityWarningLevel() {
    el::Loggers::setVerboseLevel(DREAL_WARNING_LEVEL);
}

void SMTConfig::setVerbosityErrorLevel() {
    el::Loggers::setVerboseLevel(DREAL_ERROR_LEVEL);
}

void SMTConfig::setODEFwdTimeout(double const ode_fwd_timeout) {
    if (ode_fwd_timeout <= 0.0) {
        ostringstream os;
        os << "ERROR: argument for --ode-forward-timeout option should be positive number. "
           << "It gets " << ode_fwd_timeout << ".";
        throw logic_error(os.str());
    }
    nra_ODE_fwd_timeout = ode_fwd_timeout;
}

void SMTConfig::setODEBwdTimeout(double const ode_bwd_timeout) {
    if (ode_bwd_timeout <= 0.0) {
        ostringstream os;
        os << "ERROR: argument for --ode-backward-timeout option should be positive number. "
           << "It gets " << ode_bwd_timeout << ".";
        throw logic_error(os.str());
    }
    nra_ODE_bwd_timeout = ode_bwd_timeout;
}
