/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
        Soonho  Kong        <soonhok@cs.cmu.edu>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso
dReal   -- Copyright (C) 2013 - 2015, Soonho Kong

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

#include <string>
#include <limits>
#include <utility>
#include "api/opensmt_c.h"
#include "api/OpenSMTContext.h"
#include "egraph/Egraph.h"
#include "cnfizers/Tseitin.h"
#include "smtsolvers/SimpSMTSolver.h"
#include "version.h"
#include "util/logging.h"

using std::string;
using std::numeric_limits;
using std::pair;

#ifndef SMTCOMP

#define CAST( FROM, TO ) \
  assert( FROM ); \
  OpenSMTContext * FROM_ = static_cast< OpenSMTContext * >( FROM ); \
  OpenSMTContext & TO = *FROM_;

//
// Communication APIs
//
void opensmt_init() {
    static bool already_init = false;
    if (!already_init) {
        const char * argv[] = {};
        START_EASYLOGGINGPP(0, argv);
        already_init = true;
    }
}

void opensmt_set_verbosity( opensmt_context c, int v )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  if (v > 3) {
      context.setDebug(true);
  } else if (v > 2) {
      context.setVerbose(true);
  }
}
void opensmt_set_precision ( opensmt_context c, const double p) {
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  context.setPrecision(p);
}

double opensmt_get_precision ( opensmt_context c ) {
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  return context.getPrecision();
}

char * opensmt_version( )
{
    return const_cast< char * >( PACKAGE_STRING );
}

opensmt_context opensmt_mk_context( opensmt_logic l )
{
  OpenSMTContext * c = new OpenSMTContext( );
  OpenSMTContext & context = *c;
  // IMPORTANT:
  // Any parameter in the config should be set
  // here, BEFORE SetLogic is called. In SetLogic
  // solvers are initialized with values taken
  // from the config ...
  SMTConfig & config = context.getConfig( );
  // When API is active incremental solving must be on
  config.incremental = 1;
  //
  // Set the right logic
  switch( l )
  {
    case qf_nra:     context.SetLogic( QF_NRA ); break;
    case qf_nra_ode: context.SetLogic( QF_NRA_ODE ); break;
    opensmt_error2( "unsupported logic: ", l );
  }

  // Return context
  return static_cast< void * >( c );
}

void opensmt_del_context( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  delete c_;
}

void opensmt_reset( opensmt_context c )
{
  // assert( c );
  // OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  // OpenSMTContext & context = *c_;
  CAST( c, context );
  context.Reset( );
}

void opensmt_print_expr( opensmt_expr e )
{
  Enode * enode = static_cast< Enode * >( e );
  cerr << enode;
}

void opensmt_push( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  context.Push( );
}

void opensmt_pop( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  context.Pop( );
}

void opensmt_assert( opensmt_context c, opensmt_expr e )
{
  assert( c );
  assert( e );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * expr = static_cast< Enode * >( e );
  context.Assert( expr );
}

opensmt_result opensmt_check( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  lbool result = context.CheckSAT( );
  if ( result == l_Undef ) return l_undef;
  if ( result == l_False ) return l_false;
  return l_true;
}

opensmt_result opensmt_check_assump( opensmt_context c, opensmt_expr l )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * unit = static_cast< Enode * >( l );
  assert( unit );
  vec< Enode * > assumptions;
  assumptions.push( unit );
  lbool result = context.CheckSAT( assumptions );
  if ( result == l_Undef ) return l_undef;
  if ( result == l_False ) return l_false;
  assert( result == l_True );
  return l_true;
}

opensmt_result opensmt_check_lim_assump( opensmt_context c
                                       , opensmt_expr l
                                       , unsigned limit )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * unit = static_cast< Enode * >( l );
  assert( unit );
  vec< Enode * > assumptions;
  assumptions.push( unit );
  lbool result = context.CheckSAT( assumptions, limit );
  if ( result == l_Undef ) return l_undef;
  if ( result == l_False ) return l_false;
  return l_true;
}

//
// Model APIs
//
void opensmt_print_model( opensmt_context c, const char * filename )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  ofstream os( filename );
  context.PrintModel( os );
}

#if 0
//
// Proof/Interpolation APIs
//
void opensmt_print_proof( opensmt_context
#ifdef PRODUCE_PROOF
    c
#endif
    , const char *
#ifdef PRODUCE_PROOF
    filename
#endif
    )
{
#ifdef PRODUCE_PROOF
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  ofstream os( filename );
  context.printProof( os );
#else
  error( "you should compile with PRODUCE_PROOF flag enabled (--enable-proof flag in configure)", "" );
#endif
}

void opensmt_print_interpolant( opensmt_context
#ifdef PRODUCE_PROOF
    c
#endif
    , const char *
#ifdef PRODUCE_PROOF
    filename
#endif
    )
{
#ifdef PRODUCE_PROOF
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  ofstream os( filename );
  context.printInter( os );
#else
  error( "you should compile with PRODUCE_PROOF flag enabled (--enable-proof flag in configure)", "" );
#endif
}
#endif

//
// Formula construction APIs
//

void opensmt_define_ode( opensmt_context c, const char * flowname, opensmt_expr * vars, opensmt_expr * rhses, unsigned n)
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  vector<pair<string, Enode *> *> odes;
  for (unsigned i = 0; i < n; i++) {
      Enode * var = static_cast<Enode *>(vars[i]);
      Enode * rhs = static_cast<Enode *>(rhses[i]);
      odes.push_back(new pair<string, Enode*>(var->getCar()->getName(), rhs));
  }
  context.DefineODE(flowname, &odes);
}

opensmt_expr opensmt_mk_integral ( opensmt_context c, opensmt_expr * vars_t,
                                   opensmt_expr time_l, opensmt_expr time_u,
                                   opensmt_expr * vars_0, unsigned n,
                                   const char * flowname) {
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  list< Enode * > args_t, args_0;
  for ( unsigned i = 0 ; i < n ; i ++ ) {
    Enode * arg_t = static_cast< Enode * >( vars_t[ i ] );
    Enode * arg_0 = static_cast< Enode * >( vars_0[ i ] );
    args_t.push_back( arg_t );
    args_0.push_back( arg_0 );
  }
  Enode * args_list_t = context.mkCons( args_t );
  Enode * args_list_0 = context.mkCons( args_0 );
  Enode * res = context.mkIntegral(static_cast<Enode*>(time_l), static_cast<Enode*>(time_u),
                                   args_list_0, args_list_t, flowname);
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_true( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * res = context.mkTrue( );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_false( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * res = context.mkFalse( );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bool_var( opensmt_context c, char const * s )
{
  assert( c );
  assert( s );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Snode * sort = context.mkSortBool( );
  context.DeclareFun( s, sort );
  Enode * res = context.mkVar( s, true );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_int_var( opensmt_context c, char const * s , long lb, long ub)
{
  assert( c );
  assert( s );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Snode * sort = context.mkSortInt( );
  context.DeclareFun( s, sort );
  Enode * res = context.mkVar( s, true );
  res->setDomainLowerBound(lb);
  res->setDomainUpperBound(ub);
  res->setValueLowerBound(lb);
  res->setValueUpperBound(ub);
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_unbounded_int_var( opensmt_context c, char const * s)
{
  return opensmt_mk_int_var(c, s, numeric_limits<long>::lowest(), numeric_limits<long>::max());
}

opensmt_expr opensmt_mk_forall_int_var( opensmt_context c, char const * s , long lb, long ub)
{
  assert( c );
  assert( s );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Snode * sort = context.mkSortInt( );
  context.DeclareFun( s, sort );
  Enode * res = context.mkVar( s, true );
  res->setDomainLowerBound(lb);
  res->setDomainUpperBound(ub);
  res->setValueLowerBound(lb);
  res->setValueUpperBound(ub);
  res->setForallVar();
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_forall_unbounded_int_var( opensmt_context c, char const * s)
{
  return opensmt_mk_int_var(c, s, numeric_limits<long>::lowest(), numeric_limits<long>::max());
}


opensmt_expr opensmt_mk_real_var( opensmt_context c, char const * s , double lb, double ub)
{
  assert( c );
  assert( s );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Snode * sort = context.mkSortReal( );
  context.DeclareFun( s, sort );
  Enode * res = context.mkVar( s, true );
  res->setDomainLowerBound(lb);
  res->setDomainUpperBound(ub);
  res->setValueLowerBound(lb);
  res->setValueUpperBound(ub);
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_unbounded_real_var( opensmt_context c, char const * s)
{
    return opensmt_mk_real_var(c, s, -numeric_limits<double>::infinity(), numeric_limits<double>::infinity());
}

opensmt_expr opensmt_mk_forall_real_var( opensmt_context c, char const * s , double lb, double ub)
{
  assert( c );
  assert( s );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Snode * sort = context.mkSortReal( );
  context.DeclareFun( s, sort );
  Enode * res = context.mkVar( s, true );
  res->setDomainLowerBound(lb);
  res->setDomainUpperBound(ub);
  res->setValueLowerBound(lb);
  res->setValueUpperBound(ub);
  res->setForallVar();
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_forall_unbounded_real_var( opensmt_context c, char const * s)
{
  return opensmt_mk_real_var(c, s, numeric_limits<double>::lowest(), numeric_limits<double>::max());
}

opensmt_expr opensmt_mk_forall( opensmt_context c, opensmt_expr * varlist, unsigned n, opensmt_expr body ) {
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  vector<pair<string, Snode *>*>* sorted_var_list = new vector<pair<string, Snode *>*>();
  for (unsigned i = 0; i < n; ++i) {
      opensmt_expr var = varlist[i];
      Enode * e = static_cast<Enode*>(var);
      Snode * sort = e->getSort();
      string name = e->getCar()->getName();
      sorted_var_list->push_back(new pair<string, Snode *>(name, sort));
  }
  Enode * e_body = static_cast<Enode*>(body);
  Enode * res = context.mkForall(sorted_var_list, e_body);
  delete sorted_var_list;
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_or( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  assert( c );
  assert( expr_list );
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkOr( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_or_2( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2)
{
  opensmt_expr list[2] = {expr1, expr2};
  return opensmt_mk_or(c, list, 2);
}

opensmt_expr opensmt_mk_or_3( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2, opensmt_expr expr3)
{
  opensmt_expr list[3] = {expr1, expr2, expr3};
  return opensmt_mk_or(c, list, 3);
}

opensmt_expr opensmt_mk_and( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  assert( c );
  assert( expr_list );
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkAnd( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_and_2( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2)
{
  opensmt_expr list[2] = {expr1, expr2};
  return opensmt_mk_and(c, list, 2);
}

opensmt_expr opensmt_mk_and_3( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2, opensmt_expr expr3)
{
  opensmt_expr list[3] = {expr1, expr2, expr3};
  return opensmt_mk_and(c, list, 3);
}

opensmt_expr opensmt_mk_eq ( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkEq( args_list );
  return static_cast< void * >( res );
 }

opensmt_expr opensmt_mk_ite( opensmt_context c, opensmt_expr i, opensmt_expr t, opensmt_expr e )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * i_ = static_cast< Enode * >( i );
  Enode * t_ = static_cast< Enode * >( t );
  Enode * e_ = static_cast< Enode * >( e );
  Enode * args = context.mkCons( i_
               , context.mkCons( t_
               , context.mkCons( e_ ) ) );
  Enode * res = context.mkIte( args );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_not( opensmt_context c, opensmt_expr x)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ));
  Enode * res = context.mkNot( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_num_from_string( opensmt_context c, const char * s )
{
  assert( c );
  assert( s );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * res = context.mkNum( s );
  return res;
}

opensmt_expr opensmt_mk_num( opensmt_context c, double const v )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * res = context.mkNum( v );
  return res;
}

opensmt_expr opensmt_mk_plus( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkPlus( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_plus_2( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2)
{
  opensmt_expr list[2] = {expr1, expr2};
  return opensmt_mk_plus(c, list, 2);
}

opensmt_expr opensmt_mk_plus_3( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2, opensmt_expr expr3)
{
  opensmt_expr list[3] = {expr1, expr2, expr3};
  return opensmt_mk_plus(c, list, 3);
}

opensmt_expr opensmt_mk_minus( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkMinus( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_uminus( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkUminus( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_times( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkTimes( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_times_2( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2)
{
  opensmt_expr list[2] = {expr1, expr2};
  return opensmt_mk_times(c, list, 2);
}

opensmt_expr opensmt_mk_times_3( opensmt_context c, opensmt_expr expr1, opensmt_expr expr2, opensmt_expr expr3)
{
  opensmt_expr list[3] = {expr1, expr2, expr3};
  return opensmt_mk_times(c, list, 3);
}


opensmt_expr opensmt_mk_div( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkDiv( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_leq( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkLeq( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_lt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkLt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_gt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkGt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_geq( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkGeq( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_abs( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkAbs( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_exp( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkExp( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_log( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkLog( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_pow( opensmt_context c, opensmt_expr arg1, opensmt_expr arg2)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg1 )
                    , context.mkCons( static_cast< Enode * >( arg2 ) ) );
  Enode * res = context.mkPow( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_sin( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkSin( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_cos( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkCos( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_tan( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkTan( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_asin( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkAsin( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_acos( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkAcos( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_atan( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkAtan( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_sinh( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkSinh( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_cosh( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkCosh( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_tanh( opensmt_context c, opensmt_expr arg)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg ) );
  Enode * res = context.mkTanh( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_atan2( opensmt_context c, opensmt_expr arg1, opensmt_expr arg2)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg1 )
                    , context.mkCons( static_cast< Enode * >( arg2 ) ) );
  Enode * res = context.mkAtan2( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_min( opensmt_context c, opensmt_expr arg1, opensmt_expr arg2)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg1 )
                    , context.mkCons( static_cast< Enode * >( arg2 ) ) );
  Enode * res = context.mkMin( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_max( opensmt_context c, opensmt_expr arg1, opensmt_expr arg2)
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( arg1 )
                    , context.mkCons( static_cast< Enode * >( arg2 ) ) );
  Enode * res = context.mkMax( static_cast< Enode * >( args_list ) );
  return static_cast< void * >( res );
}

/*
opensmt_expr opensmt_mk_bv_constant( opensmt_context c, unsigned w, unsigned long n )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  char buf[ 1024 ];
  sprintf( buf, "bv%ld[%d]", n, w );
  Enode * res = context.mkBvnum( buf );
  return res;
}

opensmt_expr opensmt_mk_bv_constant_from_string( opensmt_context c, unsigned w, const char * s )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  char buf[ 1024 ];
  sprintf( buf, "bv%s[%d]", s, w );
  Enode * res = context.mkBvnum( buf );
  return res;
}

opensmt_expr opensmt_mk_bv_add( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvadd( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sub( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvsub( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_mul( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvmul( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_neg( opensmt_context c, opensmt_expr x )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ) );
  Enode * res = context.mkBvneg( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_concat( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkConcat( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_and( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvand( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_or( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvor( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_xor( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvxor( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_not( opensmt_context c, opensmt_expr x )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ) );
  Enode * res = context.mkBvnot( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_extract( opensmt_context c, unsigned msb, unsigned lsb, opensmt_expr x )
{
  assert( c );
  assert( x );
  assert( lsb <= msb );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkExtract( msb, lsb, arg );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sign_extend( opensmt_context c, opensmt_expr x, unsigned n )
{
  assert( c );
  assert( x );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkSignExtend( n, arg );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_zero_extend( opensmt_context c, opensmt_expr x, unsigned n )
{
  assert( c );
  assert( x );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkZeroExtend( n, arg );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_shift_left( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  assert( c );
  assert( x );
  assert( y );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvshl( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_shift_right( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  assert( c );
  assert( x );
  assert( y );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvlshr( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_lt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvult( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_le( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvule( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_gt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvugt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_ge( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvuge( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_slt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvslt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sle( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvsle( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sgt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvsgt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sge( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvsge( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_ct_incur( opensmt_context c
                                , opensmt_expr    var
                                , opensmt_expr    cost
                                , opensmt_expr    id )
{
  assert( c );
  assert( var );
  assert( cost );
  assert( id );

  OpenSMTContext * ctxt = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *ctxt;

  Enode * evar  = static_cast< Enode * >( var );
  Enode * ecost = static_cast< Enode * >( cost );
  Enode * eid   = static_cast< Enode * >( id );
  Enode * args = context.mkCons( evar
               , context.mkCons( ecost
               , context.mkCons( eid ) ) );
  Enode * result = context.mkCostIncur( args );
  return static_cast< void * >( result );
}

opensmt_expr opensmt_mk_ct_bound( opensmt_context c
                                , opensmt_expr    var
                                , opensmt_expr    cost )
{
  assert( c );
  assert( var );
  assert( cost );

  OpenSMTContext * ctxt = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *ctxt;

  Enode * evar  = static_cast< Enode * >( var );
  Enode * ecost = static_cast< Enode * >( cost );
  Enode * args = context.mkCons( evar,
                 context.mkCons( ecost ) );
  Enode * result = context.mkCostBound( args );
  return static_cast< void * >( result );
}
*/
unsigned opensmt_conflicts( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  return context.getLearnts( );
}

unsigned opensmt_decisions( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  return context.getDecisions( );
}

opensmt_expr opensmt_get_value( opensmt_context c, opensmt_expr v )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  const Real & value = var->getValue();
  Enode * res = context.mkNum( value );
  return static_cast< void * >( res );
}

double opensmt_get_lb( opensmt_context c, opensmt_expr v )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  return var->getValueLowerBound();
}

double opensmt_get_ub( opensmt_context c, opensmt_expr v )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  return var->getValueUpperBound();
}
double opensmt_get_bound_lb( opensmt_context c, opensmt_expr v )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  return var->getBoundLowerBound();
}

double opensmt_get_bound_ub( opensmt_context c, opensmt_expr v )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  return var->getBoundUpperBound();
}

void opensmt_set_bound_lb( opensmt_context c, opensmt_expr v, double n )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  var->setBoundLowerBound(n);
}

void opensmt_set_bound_ub( opensmt_context c, opensmt_expr v, double n )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  var->setBoundUpperBound(n);
}

double opensmt_get_domain_lb( opensmt_context c, opensmt_expr v )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  return var->getDomainLowerBound();
}

double opensmt_get_domain_ub( opensmt_context c, opensmt_expr v )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  return var->getDomainUpperBound();
}

void opensmt_set_domain_lb( opensmt_context c, opensmt_expr v, double n )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  var->setDomainLowerBound(n);
}

void opensmt_set_domain_ub( opensmt_context c, opensmt_expr v, double n )
{
  assert( c );
  assert( v );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  var->setDomainUpperBound(n);
}

/*
void opensmt_get_num( opensmt_expr n, mpz_t val )
{
  assert( n );
  Enode * num = static_cast< Enode * >( n );
  assert( num->isConstant() );
  Real r = num->getValue();
  mpz_set( val, r.get_num().get_mpz_t() );
}
*/
opensmt_result opensmt_get_bool( opensmt_context c, opensmt_expr p )
{
  assert( c );
  assert( p );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * atom = static_cast< Enode * >( p );
  lbool value = context.getModel( atom );
  if ( value == l_True )
  {
    return l_true;
  }
  else if ( value == l_False )
  {
    return l_false;
  }
  return l_undef;
}

void opensmt_polarity( opensmt_context, opensmt_expr, int )
{
  // assert( c );
  // assert( a );
  // bool positive = static_cast< bool >( pos );
  // OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  // OpenSMTContext & context = *c_;
  // SimpSMTSolver & solver = context.solver;
  // Enode * atom = static_cast< Enode * >( a );
}

#endif
