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

/************************************************************************************[SimpSMTSolver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef SIMP_SMT_SOLVER_H
#define SIMP_SMT_SOLVER_H

#include <set>
#include <map>
#include <vector>
#include "minisat/mtl/Queue.h"
#include "smtsolvers/CoreSMTSolver.h"


class SimpSMTSolver : public CoreSMTSolver
{
 public:
    // Constructor/Destructor:
    //
    SimpSMTSolver ( Egraph &, SMTConfig & );
    ~SimpSMTSolver( );

    bool         addSMTClause         ( std::vector< Enode * > &, uint64_t in = 0 );
    inline lbool smtSolve             ( ) { return solve( false, false ); }
    inline lbool smtSolve             ( bool do_simp ) { return solve( do_simp, false ); }
    Enode *      mergeTAtoms          ( Enode *, bool, Enode *, bool, Enode * );
    void         eliminateTVar        ( Enode * );
    void         initialize           ( );

#if NEW_SIMPLIFICATIONS
    void         gatherTVars          ( Enode *, bool, Clause * );
    void         gaussianElimination  ( );
    void         substituteInClauses  ( );
    bool         dpfm                 ( );
#else
    void         getDLVars            ( Enode *, bool, Enode **, Enode ** );
#endif

    void         gatherInterfaceTerms ( Enode * );

    std::set< Clause * >                      to_remove;
    std::vector< Clause * >                   unary_to_remove;
#if NEW_SIMPLIFICATIONS
    std::set< Enode * >                       t_var; // Theory variables
#else
    // TODO: change to std::vector< list< Clauses * > >
    std::map< Enode *, std::set< enodeid_t > >     t_var; // Variables to which is connected to
#endif
    std::map< enodeid_t, std::vector< Clause * > > t_pos; // Clauses where theory variable appears positively
    std::map< enodeid_t, std::vector< Clause * > > t_neg; // Clauses where theory variable appears negatively

#if NEW_SIMPLIFICATIONS
    std::vector< LAExpression * >             var_to_lae;
#endif

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true);
    bool    addClause (vec<Lit>& ps, uint64_t in = 0);

    // Variable mode:
    //
    void    setFrozen (Var v, bool b); // If a variable is frozen it will not be eliminated.

    // Solving:
    //
    lbool   solve     ( const vec< Enode * > &, bool = true   , bool = false );
    lbool   solve     ( const vec< Enode * > &, const unsigned, bool = true, bool = false );
    lbool   solve     ( const vec< Lit > &    , bool = true   , bool = false );
    lbool   solve     ( const vec< Lit > &    , const unsigned, bool = true, bool = false );
    lbool   solve     ( bool = true, bool = false );
    bool    eliminate ( bool = false);             // Perform variable elimination based simplification.

    // Generate a (possibly simplified) DIMACS file:
    //
    void    toDimacs  (const char* file);
    virtual void filterUnassigned();
    // Mode of operation:
    //
    int     grow;             // Allow a variable elimination step to grow by a number of clauses (default to zero).
    bool    asymm_mode;       // Shrink clauses by asymmetric branching.
    bool    redundancy_check; // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)

    // Statistics:
    //
    int     merges;
    int     asymm_lits;
    int     remembered_clauses;

// protected:
  public:

    // Helper structures:
    //
    struct ElimData {
        int          order;      // 0 means not eliminated, >0 gives an index in the elimination order
        vec<Clause*> eliminated;
        ElimData() : order(0) {} };

    struct ElimOrderLt {
        const vec<ElimData>& elimtable;
        ElimOrderLt(const vec<ElimData>& et) : elimtable(et) {}
        bool operator()(Var x, Var y) { return elimtable[x].order > elimtable[y].order; } };

    struct ElimLt {
        const vec<int>& n_occ;
        ElimLt(const vec<int>& no) : n_occ(no) {}
        int  cost      (Var x)        const { return n_occ[toInt(Lit(x))] * n_occ[toInt(~Lit(x))]; }
        bool operator()(Var x, Var y) const { return cost(x) < cost(y); } };


    // Solver state:
    //
    int                 elimorder;
    bool                use_simplification;
    vec<ElimData>       elimtable;
    vec<char>           touched;
    vec<vec<Clause*> >  occurs;
    vec<int>            n_occ;
    Heap<ElimLt>        elim_heap;
    Queue<Clause*>      subsumption_queue;
    vec<char>           frozen;
    int                 bwdsub_assigns;

    // Temporaries:
    //
    Clause*             bwdsub_tmpunit;

    // Main internal methods:
    //
    bool          asymm                    (Var v, Clause& c);
    bool          asymmVar                 (Var v);
    void          updateElimHeap           (Var v);
    void          cleanOcc                 (Var v);
    vec<Clause*>& getOccurs                (Var x);
    void          gatherTouchedClauses     ();
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v);
    bool          backwardSubsumptionCheck (bool verbose = false);
    bool          eliminateVar             (Var v, bool fail = false);
    void          remember                 (Var v);
    void          extendModel              ();
    void          verifyModel              ();

    void          removeClause             (Clause& c);
    bool          strengthenClause         (Clause& c, Lit l);
    void          cleanUpClauses           ();
    bool          implied                  (const vec<Lit>& c);
    void          toDimacs                 (FILE* f, Clause& c);
    bool          isEliminated             (Var v) const;
};


//=================================================================================================
// Implementation of inline methods:

inline void SimpSMTSolver::updateElimHeap(Var v) {
    if (elimtable[v].order == 0)
        elim_heap.update(v); }

inline void SimpSMTSolver::cleanOcc(Var v)
{
    assert(use_simplification);
    Clause **begin = (Clause**)occurs[v];
    Clause **end = begin + occurs[v].size();
    Clause **i, **j;
    for (i = begin, j = end; i < j; i++) {
        bool found_in_clauses = false;
        for (int k = 0; k < clauses.size(); k++) {
            if (*i == clauses[k]) {
                found_in_clauses = true;
                break;
            }
        }
        if (!found_in_clauses || (*i)->mark() == 1){
            *i = *(--j);
            i--;
        }
    }
    //occurs[v].shrink_(end - j);  // This seems slower. Why?!
    occurs[v].shrink(end - j);
}

inline vec<Clause*>& SimpSMTSolver::getOccurs(Var x) {
    cleanOcc(x); return occurs[x]; }

inline bool  SimpSMTSolver::isEliminated (Var v) const { return v < elimtable.size() && elimtable[v].order != 0; }
inline void  SimpSMTSolver::setFrozen    (Var v, bool b) { if ( !use_simplification ) return; frozen[v] = (char)b; if (b) { updateElimHeap(v); } }
inline lbool SimpSMTSolver::solve        (bool do_simp, bool turn_off_simp) { vec<Lit> tmp; return solve(tmp, do_simp, turn_off_simp); }

//=================================================================================================

#endif
