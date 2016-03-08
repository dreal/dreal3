#include <fenv.h>
#include <algorithm>
#include <csignal>
#include <unordered_map>

#include "api/drealsolver.h"
#include "opensmt/api/OpenSMTContext.h"
#include "egraph/Egraph.h"
#include "smtsolvers/SimpSMTSolver.h"
#include "cnfizers/Tseitin.h"
#include "simplifiers/ExpandITEs.h"
#include "simplifiers/ArraySimplify.h"
#include "simplifiers/BVBooleanize.h"
#include "simplifiers/TopLevelProp.h"
#include "simplifiers/DLRescale.h"
#include "simplifiers/Ackermanize.h"
#include "simplifiers/Purify.h"
#include "util/string.h"
#include "dsolvers/nra_solver.h"

using std::unordered_map;
using std::cerr;
using std::endl;
using std::vector;
using std::ostream;
using std::string;
using std::pair;
using std::numeric_limits;
using std::list;

namespace dreal {

drealsolver::drealsolver() {
    OpenSMTContext * context = new OpenSMTContext();
    SMTConfig & config = context -> getConfig();
    config.incremental = 1;
    context -> SetLogic( QF_NRA );
    m_context = static_cast<env>(context);
}

drealsolver::~drealsolver() {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    delete context;
}

expr drealsolver::mk_true() {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * res = context -> mkTrue( );
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_false() {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * res = context -> mkFalse( );
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_bool_var ( char const * s ) {
    assert( m_context );  
    assert( s );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Snode * sort = context -> mkSortBool( );
    context -> DeclareFun( s, sort );
    Enode * res = context -> mkVar( s, true );
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_int_var ( char const * s , long lb, long ub) {
    assert( m_context );
    assert( s );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Snode * sort = context -> mkSortInt();
    context -> DeclareFun( s, sort );
    Enode * res = context -> mkVar( s, true );
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_int_var( char const * s) {
    return mk_int_var( s, numeric_limits<long>::lowest(), numeric_limits<long>::max());
}

expr drealsolver::mk_real_var( char const * s , double lb, double ub) {
    assert( m_context );
    assert( s );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Snode * sort = context -> mkSortReal();
    context -> DeclareFun( s, sort );
    Enode * res = context -> mkVar( s, true );
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_real_var( char const * s) {
    return mk_real_var( s, -numeric_limits<double>::infinity(), numeric_limits<double>::infinity() );
}

expr drealsolver::mk_forall( expr * varlist, unsigned n, expr body ) {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    vector<pair<string, Snode *>> sorted_var_list;
    for (unsigned i = 0; i < n; ++i) {
	expr var = varlist[i];
	Enode * e = static_cast<Enode*>(var);
	Snode * sort = e->getSort();
	string name = e->getCar()->getNameFull();
	sorted_var_list.push_back(make_pair(name, sort));
    }
    Enode * e_body = static_cast<Enode*>(body);
    Enode * res = context -> mkForall(sorted_var_list, e_body);
    expr temp = static_cast<expr>(e_body);
    expr_table.push_back(temp);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_or( expr * expr_list, unsigned n ) {
    assert( m_context );
    assert( expr_list );
    list< Enode * > args;
    for ( unsigned i = 0 ; i < n ; i ++ ) {
	Enode * arg = static_cast< Enode * >( expr_list[ i ] );
	args.push_back( arg );
    }
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( args );
    Enode * res = context -> mkOr( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_or( expr e1, expr e2) {
    expr elist[2] = { e1, e2 };
    return mk_or( elist, 2 );
}

expr drealsolver::mk_or( expr e1, expr e2, expr e3)
{
    expr elist[3] = { e1, e2, e3 };
    return mk_or( elist, 3);
}

expr drealsolver::mk_and( expr * expr_list, unsigned n ) {
    assert( m_context );
    assert( expr_list );
    list< Enode * > args;
    for ( unsigned i = 0 ; i < n ; i ++ ) {
	Enode * arg = static_cast< Enode * >( expr_list[ i ] );
	args.push_back( arg );
    }
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( args );
    Enode * res = context -> mkAnd( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_and( expr e1, expr e2) {
    expr elist[2] = {e1, e2};
    return mk_and(elist, 2);
}

expr drealsolver::mk_and( expr e1, expr e2, expr e3 ) {
    expr elist[3] = {e1, e2, e3};
    return mk_and(elist, 3);
}

expr drealsolver::mk_eq ( expr x, expr y ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( x ), 
					    context -> mkCons(static_cast<Enode*>(y)));
    Enode * res = context -> mkEq(args_list);
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_ite( expr i, expr t, expr e ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * i_ = static_cast< Enode * >( i );
    Enode * t_ = static_cast< Enode * >( t );
    Enode * e_ = static_cast< Enode * >( e );
    Enode * args = context -> mkCons(i_,context -> mkCons(t_,context -> mkCons(e_)));
    Enode * res = context -> mkIte(args);
    expr temp = static_cast<expr>(args);
    expr_table.push_back(temp);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_not( expr x ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( x ));
    Enode * res = context -> mkNot( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_num( const char * s ) {
    assert( s );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * res = context -> mkNum( s );
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_num( double const v ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * res = context -> mkNum( v );
    expr result = static_cast<expr>( res );
    expr_table.push_back(result);
    return result;
}

expr drealsolver::mk_plus( expr * expr_list, unsigned n ) {
    list< Enode * > args;
    for ( unsigned i = 0 ; i < n ; i ++ ) {
	Enode * arg = static_cast< Enode * >( expr_list[ i ] );
	args.push_back( arg );
    }
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( args );
    Enode * res = context -> mkPlus( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_plus( expr expr1, expr expr2 ) {
    expr elist[2] = {expr1, expr2};
    return mk_plus(elist, 2);
}

expr drealsolver::mk_minus( expr x, expr y ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( x )
					, context->mkCons( static_cast< Enode * >( y ) ) );
    Enode * res = context -> mkMinus( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_uminus( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkUminus( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_times( expr * expr_list, unsigned n ) {
    list< Enode * > args;
    for ( unsigned i = 0 ; i < n ; i ++ ) {
	Enode * arg = static_cast< Enode * >( expr_list[ i ] );
	args.push_back( arg );
    }
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( args );
    Enode * res = context -> mkTimes( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_times( expr expr1, expr expr2) {
    expr elist[2] = {expr1, expr2};
    return mk_times(elist, 2);
}

expr drealsolver::mk_div( expr x, expr y ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( x )
					    , context->mkCons( static_cast< Enode * >( y ) ) );
    Enode * res = context -> mkDiv( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_leq( expr lhs, expr rhs ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( lhs )
					    , context->mkCons( static_cast< Enode * >( rhs ) ) );
    Enode * res = context->mkLeq( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_lt( expr lhs, expr rhs ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( lhs )
					    , context->mkCons( static_cast< Enode * >( rhs ) ) );
    Enode * res = context -> mkLt( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_gt( expr lhs, expr rhs ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( lhs )
					    , context -> mkCons( static_cast< Enode * >( rhs ) ) );
    Enode * res = context -> mkGt( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_geq( expr lhs, expr rhs ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( lhs )
					    , context -> mkCons( static_cast< Enode * >( rhs ) ) );
    Enode * res = context -> mkGeq( args_list );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_abs( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkAbs( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_exp( expr arg) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkExp( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_log( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkLog( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_sqrt( expr arg) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkSqrt( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_pow( expr arg1, expr arg2) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( arg1 )
					    , context->mkCons( static_cast< Enode * >( arg2 ) ) );
    Enode * res = context->mkPow( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_sin( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkSin( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_cos( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkCos( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_tan( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkTan( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_asin( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkAsin( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_acos( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkAcos( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_atan( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkAtan( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_sinh( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkSinh( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_cosh( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkCosh( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_tanh( expr arg ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons( static_cast< Enode * >( arg ) );
    Enode * res = context -> mkTanh( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_atan2( expr arg1, expr arg2 ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context -> mkCons(  static_cast< Enode * >( arg1 )
					    , context->mkCons( static_cast< Enode * >( arg2 ) ) );
    Enode * res = context->mkAtan2( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_min( expr arg1, expr arg2 ) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context->mkCons(static_cast< Enode * >( arg1 )
					,context->mkCons( static_cast< Enode * >( arg2 ) ) );
    Enode * res = context->mkMin( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

expr drealsolver::mk_max( expr arg1, expr arg2) {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * args_list = context->mkCons(static_cast< Enode * >( arg1 )
					,context->mkCons( static_cast< Enode * >( arg2 ) ) );
    Enode * res = context -> mkMax( static_cast< Enode * >( args_list ) );
    expr temp = static_cast<expr>(args_list);
    expr_table.push_back(temp);
    expr result = static_cast<expr>(res);
    expr_table.push_back(result);  
    return result;
}

result drealsolver::get_bool_value ( expr p ) {
    assert( p );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * atom = static_cast< Enode * >( p );
    assert( atom -> isAtom() ); 
    lbool value = context->getModel( atom );
    if ( value == l_True )    
	return dr_true;
    else if ( value == l_False ) 
	return dr_false;
    return dr_undef;
}

void drealsolver::reset() {
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    context -> Reset();
}

void drealsolver::print( expr e ) {
    Enode * enode = static_cast< Enode * >( e );
    cerr << enode;
}

void drealsolver::push() {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    context -> Push();
}

void drealsolver::pop() {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    context -> Pop();
}

void drealsolver::declare( expr e ) {
    assert( m_context );
    assert( e );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * enode = static_cast< Enode * >( e );
    context -> Assert( enode );
}

result drealsolver::check() {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    lbool result = context -> CheckSAT( );
    if ( result == l_Undef ) return dr_undef;
    if ( result == l_False ) return dr_false;
    return dr_true;
}

result drealsolver::check_assump( expr l ) {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * unit = static_cast< Enode * >( l );
    assert( unit );
    vec< Enode * > assumptions;
    assumptions.push( unit );
    lbool result = context->CheckSAT( assumptions );
    if ( result == l_Undef ) return dr_undef;
    if ( result == l_False ) return dr_false;
    assert( result == l_True );
    return dr_true;
}

result drealsolver::check_lim_assump( expr l, unsigned limit ) {
    assert( m_context );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    Enode * unit = static_cast< Enode * >( l );
    assert( unit );
    vec< Enode * > assumptions;
    assumptions.push( unit );
    lbool result = context -> CheckSAT( assumptions, limit );
    if ( result == l_Undef ) return dr_undef;
    if ( result == l_False ) return dr_false;
    return dr_true;
}


expr drealsolver::get_value( expr v ) {
    assert( v );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    assert( context -> getStatus( ) == l_True );
    Enode * var = static_cast< Enode * >( v );
    const Real & value = var->getValue();
    Enode * res = context -> mkNum( value );
    return static_cast< void * >( res );
}

double drealsolver::get_lb( expr v ) {
    assert( v );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    assert( context -> getStatus( ) == l_True );
    Enode * var = static_cast< Enode * >( v );
    return var->getValueLowerBound();
}

double drealsolver::get_ub( expr v ) {
    assert( v );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    assert( context -> getStatus( ) == l_True );
    Enode * var = static_cast< Enode * >( v );
    return var->getValueUpperBound();
}

double drealsolver::get_domain_lb( expr v ) {
    assert( v );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    assert( context -> getStatus( ) == l_True );
    Enode * var = static_cast< Enode * >( v );
    return var->getDomainLowerBound();
}

double drealsolver::get_domain_ub( expr v ) {
    assert( v );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    assert( context -> getStatus( ) == l_True );
    Enode * var = static_cast< Enode * >( v );
    return var->getDomainUpperBound();
}

void drealsolver::set_domain_lb( expr v, double n ) {
    assert( v );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    assert( context -> getStatus( ) == l_True );
    Enode * var = static_cast< Enode * >( v );
    var->setDomainLowerBound(n);
}

void drealsolver::set_domain_ub( expr v, double n ) {
    assert( v );
    OpenSMTContext * context = static_cast< OpenSMTContext * >( m_context );
    assert( context -> getStatus( ) == l_True );
    Enode * var = static_cast< Enode * >( v );
    var->setDomainUpperBound(n);
}







}

