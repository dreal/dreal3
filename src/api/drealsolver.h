#pragma once

#include <vector>
#include <utility>
#include <string>
#include <iostream>
#include <list>

#include "egraph/Egraph.h"
#include "smtsolvers/SimpSMTSolver.h"
#include "cnfizers/Tseitin.h"

#define dreal_error(S) { std::cerr << "# Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; exit( 1 ); }
#define dreal_error2(S,T) { std::cerr << "# Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; exit(1); }
#define dreal_warning(S)    { std::cerr << "# Warning: " << S << std::endl; }
#define dreal_warning2(S,T) { std::cerr << "# Warning: " << S << " " << T << std::endl; }

class drealsolver
{
public:
    drealsolver();
    ~drealsolver();

    int	    executeCommands      ( );
    void    SetLogic             ( logic_t );                    
    void    SetLogic             ( const char * );               
    void    SetOption            ( const char * );               
    void    SetOption            ( const char *, const char * ); 
    void    SetInfo              ( const char * );               
    void    SetInfo              ( const char *, const char * ); 

    void    DeclareSort          ( const char *, int );          // Declares a new sort
    void    DeclareFun           ( const char *, Snode * );      // Declares a new function symbol
    void    DeclareFun           ( const char *, Snode * , const char * p);  // Declares a new function symbol
    void    DefineODE            ( char const *, std::vector<std::pair<Enode *, Enode *>> const & odes );      // Define an ODE
    void    Push                 ( );
    void    Pop                  ( );
    void    Reset                ( );
    inline void	    PrintModel           (std::ostream & os) { solver.printModel( os ); egraph.printModel( os ); }
    void    GetProof             ( );
    void    GetInterpolants      ( );
    void    Assert               ( Enode * );               // Pushes assertion
    lbool   CheckSAT             ( );                       // Command for (check-sat)
    void    Exit                 ( );                       // Command for (exit)
    void    PrintResult          ( const lbool &, const lbool & = l_Undef );
    
    void    addAssert            ( Enode * );               // Command for (assert ...)
    void    addCheckSAT          ( );                       // Command for (check-sat)
    void    addPush              ( int );                   // Command for (push ...)
    void    addPop               ( int );                   // Command for (pop ...)
    void    addGetProof          ( );                       // Command for (get-proof)
    void    addGetInterpolants   ( );                       // Command for (get-interpolants)
    void    addExit              ( );                       // Command for (exit)
  
    lbool   CheckSAT( vec< Enode * > & );                      // Command for (check-sat)
    lbool   CheckSAT( vec< Enode * > &, unsigned );            // Command for (check-sat)

    inline Enode * mkTrue      ( )                 { return egraph.mkTrue( ); }
    inline Enode * mkFalse     ( )                 { return egraph.mkFalse( ); }
    inline Enode * mkAnd       ( Enode * e )       { assert( e ); return egraph.mkAnd     ( e ); }
    inline Enode * mkOr        ( Enode * e )       { assert( e ); return egraph.mkOr      ( e ); }
    inline Enode * mkNot       ( Enode * e )       { assert( e ); return egraph.mkNot     ( e ); }
    inline Enode * mkImplies   ( Enode * e )       { assert( e ); return egraph.mkImplies ( e ); }
    inline Enode * mkXor       ( Enode * e )       { assert( e ); return egraph.mkXor     ( e ); }
    inline Enode * mkEq        ( Enode * e )       { assert( e ); return egraph.mkEq      ( e ); }
    inline Enode * mkIte       ( Enode * e )       { assert( e ); return egraph.mkIte     ( e ); }

    inline Enode * mkLeq       ( Enode * e )       { assert( e ); return egraph.mkLeq   ( e ); }
    inline Enode * mkLt        ( Enode * e )       { assert( e ); return egraph.mkLt    ( e ); }
    inline Enode * mkGeq       ( Enode * e )       { assert( e ); return egraph.mkGeq   ( e ); }
    inline Enode * mkGt        ( Enode * e )       { assert( e ); return egraph.mkGt    ( e ); }

    inline Enode * mkPlus      ( Enode * e )       { assert( e ); return egraph.mkPlus  ( e ); }
    inline Enode * mkMinus     ( Enode * e )       { assert( e ); return egraph.mkMinus ( e ); }
    inline Enode * mkTimes     ( Enode * e )       { assert( e ); return egraph.mkTimes ( e ); }
    inline Enode * mkUminus    ( Enode * e )       { assert( e ); return egraph.mkUminus( e ); }
    inline Enode * mkDiv       ( Enode * e )       { assert( e ); return egraph.mkDiv   ( e ); }
    inline Enode * mkAbs       ( Enode * e )       { assert(e); return egraph.mkAbs(e);}
    inline Enode * mkExp       ( Enode * e )       { assert(e); return egraph.mkExp(e);}
    inline Enode * mkLog       ( Enode * e )       { assert(e); return egraph.mkLog(e);}
    inline Enode * mkPow       ( Enode * e )       { assert(e); return egraph.mkPow(e);}
    inline Enode * mkSin       ( Enode * e )       { assert(e); return egraph.mkSin(e);}
    inline Enode * mkCos       ( Enode * e )       { assert(e); return egraph.mkCos(e);}
    inline Enode * mkTan       ( Enode * e )       { assert(e); return egraph.mkTan(e);}
    inline Enode * mkAsin      ( Enode * e )       { assert(e); return egraph.mkAsin(e);}
    inline Enode * mkAcos      ( Enode * e )       { assert(e); return egraph.mkAcos(e);}
    inline Enode * mkAtan      ( Enode * e )       { assert(e); return egraph.mkAtan(e);}
    inline Enode * mkSinh      ( Enode * e )       { assert(e); return egraph.mkSinh(e);}
    inline Enode * mkCosh      ( Enode * e )       { assert(e); return egraph.mkCosh(e);}
    inline Enode * mkTanh      ( Enode * e )       { assert(e); return egraph.mkTanh(e);}
    inline Enode * mkAtan2     ( Enode * e )       { assert(e); return egraph.mkAtan2(e);}
    inline Enode * mkMin       ( Enode * e )       { assert(e); return egraph.mkMin(e);}
    inline Enode * mkMax       ( Enode * e )       { assert(e); return egraph.mkMax(e);}
    inline Enode * mkMatan     ( Enode * e )       { assert(e); return egraph.mkMatan(e);}
    inline Enode * mkSafeSqrt  ( Enode * e )       { assert(e); return egraph.mkSafeSqrt(e);}
    inline Enode * mkSqrt      ( Enode * e )       { assert(e); return egraph.mkSqrt(e);}

    inline Enode * mkDeriv     ( Enode * e1 , Enode * e2)       { assert(e1); assert(e2); return egraph.mkDeriv(e1,e2);}


    inline Enode * mkVar ( const char * n, bool m = false ) { assert(n); return egraph.mkVar(n, m); }
    inline Enode * mkFun ( const char * n, Enode * a ) { assert( n ); return egraph.mkFun(n,a); }
    inline Enode * mkNum ( const char * n ) { assert(n); return egraph.mkNum( n ); }
    inline Enode * mkNum ( const Real & r ) { return egraph.mkNum(r); }

    inline Snode * mkSortBool() { return sstore.mkBool(); }
    inline Snode * mkSortInt()	{ return sstore.mkInt(); }
    inline Snode * mkSortReal()	{ return sstore.mkReal(); }
    inline Snode * mkSort(Snode * a)	{ return sstore.mkDot(a); }
    inline Snode * mkSortVar(const char * n) { return sstore.mkVar(n); }

    inline Enode * mkCons (Enode * car,Enode * cdr = NULL) {
	assert(car);
	return cdr == NULL ? egraph.cons( car ) : egraph.cons( car, cdr );
    }
    inline Enode * mkCons ( std::list< Enode * > & l ) { 
	return egraph.cons( l ); 
    }
    inline Snode * mkCons ( std::list< Snode * > & l ) { 
	return sstore.cons( l ); 
    }

    inline Enode * mkForallT   ( Enode * mode, Enode * lb, Enode * ub, Enode * e ) { 
	assert(e); return egraph.mkForallT(mode, lb, ub, e);
    }
    inline Enode * mkIntegral(Enode * time_0, Enode * time_t, Enode * vec_0, Enode * vec_t, const char * flowname) {
	assert(time_0);
	assert(time_t);
	assert(vec_0);
	assert(vec_t);
	assert(flowname);
	return egraph.mkIntegral(time_0, time_t, vec_0, vec_t, flowname);
    }
    inline Enode * mkForall(std::vector<std::pair<std::string, Snode *>> const & sorted_var_list, Enode * e) {
	assert(e);
	return egraph.mkForall(sorted_var_list, e);
    }
    inline Enode * mkExists ( std::vector<std::pair<std::string, Snode *>> const & sorted_var_list, Enode * e) {
	assert(e);
	return egraph.mkExists(sorted_var_list, e);
    }

    inline double getPrecision() { return config.nra_precision; }
    inline void setPrecision (const double d ) { config.nra_precision = d; }
    inline void setLocalOpt (const bool b ) { config.nra_local_opt = b; }
    inline void setWorklistFP (const bool b ) { config.nra_worklist_fp = b; }
    inline void setMaxPrecision ( const double d ) { if(d > config.nra_precision) setPrecision(d); }
    inline SMTConfig & getConfig()  { return config; }
    inline unsigned getLearnts() { return solver.nLearnts( ); }
    inline unsigned getDecisions()	{ return solver.decisions; }
    inline lbool    getStatus()	{ return state; }
    inline lbool    getModel(Enode * a) { return solver.getModel(a); }
    inline Egraph * getEgraphP()    { return egraph_p; }

    inline void setPolarityMode ( unsigned m ) { assert( m <= 6 ); config.sat_polarity_mode = m; }
    inline void setVerbose(bool b) {
	if (b) {
	    config.setVerbosityInfoLevel();
	}
	config.nra_verbose = b;
    }
    inline void	setDebug(bool b) {
	if (b) {
	    config.setVerbosityDebugLevel();
	}
	config.nra_debug = b;
    }

    inline void setPolytope(bool b) { config.nra_polytope = b;}
    inline void	setShrinkForDop(bool b) { config.nra_shrink_for_dop = b; }
    inline void	setStat(bool b) { config.nra_use_stat = b;}

private:

    SMTConfig *	config_p;                                   
    SMTConfig & config;                                     
    SStore *	sstore_p;                               
    SStore &	sstore;                                     
    Egraph *    egraph_p;                                   
    Egraph &	egraph;                                     
    SimpSMTSolver * solver_p;                                   
    SimpSMTSolver & solver;                                    
    Tseitin *	cnfizer_p;                                  
    Tseitin &	cnfizer;                                    
  
    lbool   state;                                      
    std::vector<Command>    command_list;                           
    unsigned	nof_checksat;	// Counter for CheckSAT commands
    bool    init;                                      

    typedef enum {
	CMD_UNDEF,                                                  // undefined command
	SET_LOGIC,                                                  // (set-logic)
	SET_OPTION,                                                 // (set-option)
	SET_INFO,                                                   // (set-info)
	DECLARE_SORT,                                               // (declare-sort)
	DEFINE_SORT,                                                // (define-sort)
	DECLARE_FUN,                                                // (declare-fun)
	DEFINE_FUN,                                                 // (define-fun)
	DEFINE_ODE,                   // (define-ode)
	PUSH,                                                       // (push)
	POP,                                                        // (pop)
	ASSERT,                                                     // (assert)
	CHECK_SAT,                                                  // (check-sat)
	GET_ASSERTIONS,                                             // (get-assertions)
	GET_PROOF,                                                  // (get-proof)
	GET_INTERPOLANTS,                                           // (get-interpolants)
	GET_UNSAT_CORE,                                             // (get-unsat-core)
	GET_VALUE,                                                  // (get-value)
	GET_ASSIGNMENT,                                             // (get-assignment)
	GET_OPTION,                                                 // (get-option)
	GET_INFO,                                                   // (get-info)
	EXIT,                                                       // (exit)
    } command_name_t;

    struct Command {
	Command() :command( CMD_UNDEF ),enode( NULL ),snode( NULL ) {}
	
	command_name_t command;
	Enode *        enode;
	Snode *        snode;
	char           str[256];
	int            num;
    };

    int	    executeIncremental ();   // Execute with incremental ability
    int	    executeStatic      ();   // Execute without incremental ability (faster as more preproc is done)
    void    staticCheckSAT     ();   // For when only one check is required
    void    loadCustomSettings ();   
};


