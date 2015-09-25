/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "egraph/Egraph.h"
#include "api/OpenSMTContext.h"
#include "smtsolvers/SimpSMTSolver.h"
#include "version.h"
#include <cstdlib>
#include <string>
#include <cstdio>
#include <csignal>
#include <iostream>
#include <ezOptionParser/ezOptionParser.hpp>
#include "util/git_sha1.h"
#include "util/logging.h"

#if defined(__linux__)
#include <fpu_control.h>
#endif

using std::ostringstream;
using std::string;
using std::cerr;
using std::endl;

namespace opensmt {

void        catcher            ( int );
extern bool stop;

} // namespace opensmt

// extern int  smtset_in          ( FILE * );
// extern int  smtparse           ( );
// extern int  cnfset_in          ( FILE * );
// extern int  cnfparse           ( );
extern int  smt2set_in         ( FILE * );
extern int  smt2parse          ( );
extern int  smt2lex_destroy    ( );

extern OpenSMTContext * parser_ctx;

/*****************************************************************************\
 *                                                                           *
 *                                  MAIN                                     *
 *                                                                           *
\*****************************************************************************/

int main( int argc, const char * argv[] )
{
#ifdef LOGGING
  START_EASYLOGGINGPP(argc, argv);
#endif
  // Set up version, usage message
  ostringstream ss;
  ss << PACKAGE_VERSION
     << " (commit " << string(dreal::getGitSHA1()).substr(0, 12) << ")";

  opensmt::stop = false;
  // Allocates Command Handler (since SMT-LIB 2.0)
  OpenSMTContext context( argc, argv );
  // Catch SigTerm, so that it answers even on ctrl-c
  signal( SIGTERM, opensmt::catcher );
  signal( SIGINT , opensmt::catcher );
  // Initialize pointer to context for parsing
  parser_ctx    = &context;
  const char * filename = context.getConfig().filename.c_str();
  assert( filename );
  // Accepts file from stdin if nothing specified
  FILE * fin = NULL;
  // Make sure file exists
  if ( context.getConfig().filename == "output" )
    fin = stdin;
  else if ( (fin = fopen( filename, "rt" )) == NULL ) {
    opensmt_error2( "can't open file", filename );
  }

  // Parse
  // Parse according to filetype
  if ( fin == stdin )
  {
    smt2set_in( fin );
    smt2parse( );
  }
  else
  {
    const char * extension = strrchr( filename, '.' );
    // if ( strcmp( extension, ".smt" ) == 0 )
    // {
    //   opensmt_error( "SMTLIB 1.2 format is not supported in this version, sorry" );
    //   smtset_in( fin );
    //   smtparse( );
    // }
    // else if ( strcmp( extension, ".cnf" ) == 0 )
    // {
    //   context.SetLogic( QF_BOOL );
    //   cnfset_in( fin );
    //   cnfparse( );
    // }
    //else
    if ( strcmp( extension, ".smt2" ) == 0 )
    {
      smt2set_in( fin );
      smt2parse( );
    }
    else
    {
      opensmt_error2( extension, " extension not recognized. Please use one in { smt2, cnf } or stdin (smtlib2 is assumed)" );
    }
  }
  smt2lex_destroy();
  fclose( fin );

#ifndef SMTCOMP
  if ( context.getConfig( ).verbosity > 0 )
  {
    const int len_pack = strlen( PACKAGE_STRING );
    const char * site = "https://dreal.github.io";
    const int len_site = strlen( site );

    cerr << "#" << endl
         << "# -------------------------------------------------------------------------" << endl
         << "# " << PACKAGE_STRING;

    for ( int i = 0 ; i < 73 - len_site - len_pack ; i ++ )
      cerr << " ";

    cerr << site << endl
         << "# Compiled with gcc " << __VERSION__ << " on " << __DATE__ << endl
         << "# -------------------------------------------------------------------------" << endl
         << "#" << endl;
  }
#endif

  //
  // This trick (copied from Main.C of MiniSAT) is to allow
  // the repeatability of experiments that might be compromised
  // by the floating point unit approximations on doubles
  //
#if defined(__linux__) && !defined( SMTCOMP )
  fpu_control_t oldcw, newcw;
  _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
#endif

#ifdef PEDANTIC_DEBUG
  opensmt_warning("pedantic assertion checking enabled (very slow)");
#endif

#ifndef OPTIMIZE
//  opensmt_warning( "this binary is compiled with optimizations disabled (slow)" );
#endif
  //
  // Execute accumulated commands
  // function defined in OpenSMTContext.C
  //
  return context.executeCommands( );
}

namespace opensmt {

void catcher( int sig )
{
  switch (sig)
  {
    case SIGINT:
    case SIGTERM:
      if ( opensmt::stop )
      {
        ::parser_ctx->PrintResult( l_Undef );
        exit( 1 );
      }
      opensmt::stop = true;
      break;
  }
}

} // namespace opensmt
