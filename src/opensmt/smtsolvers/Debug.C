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

#include <assert.h>
#include <stdio.h>

#include <iomanip>
#include <iostream>
#include <map>
#include <utility>
#include <vector>

#include "common/Global.h"
#include "egraph/Egraph.h"
#include "egraph/Enode.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Vec.h"
#include "smtsolvers/CoreSMTSolver.h"
#include "smtsolvers/SMTConfig.h"
#include "tsolvers/THandler.h"
#include "json/json.hpp"

using std::map;
using std::endl;
using std::cerr;
using std::ostream;
using std::string;
using std::cout;
using std::unordered_set;
using nlohmann::json;


#ifndef SMTCOMP
void CoreSMTSolver::dumpCNF( )
{
  const char * name = "cnf.smt2";
  std::ofstream dump_out( name );
  egraph.dumpHeaderToFile( dump_out );
  dump_out << "(assert" << endl;
  dump_out << "(and" << endl;

  for ( int i = 0 ; i < clauses.size( ) ; i ++ )
  {
    Clause & c = *clauses[ i ];

    if ( c.mark( ) == 1 )
      continue;

    printSMTClause( dump_out, c );
    dump_out << endl;
  }

  //
  // Also dump the trail which contains clauses of size 1
  //
  for ( int i = 0 ; i < trail.size( ) ; i ++ )
  {
    Var v = var(trail[i]);
    if ( v <= 1 ) continue;
    Enode * e = theory_handler->varToEnode( v );
    dump_out << (sign(trail[i])?"(not ":" ") << e << (sign(trail[i])?") ":" ") << endl;
  }

  dump_out << "))" << endl;
  dump_out << "(check-sat)" << endl;
  dump_out << "(exit)" << endl;
  dump_out.close( );
  cerr << "[Dumped " << name << "]" << endl;
}

void CoreSMTSolver::verifyModel()
{
#ifdef DREAL_DEBUG
  bool failed = false;
#endif
  for (int i = 0; i < clauses.size(); i++)
  {
    assert(clauses[i]->mark() == 0);
    Clause& c = *clauses[i];
    for (int j = 0; j < c.size(); j++)
      if (modelValue(c[j]) == l_True)
        goto next;

    reportf("unsatisfied clause: ");
    printClause(*clauses[i]);
    printSMTClause( cerr, *clauses[i] );
    reportf("\n");
#ifdef DREAL_DEBUG
    failed = true;
#endif
next:;
  }
#ifdef DREAL_DEBUG
  assert(!failed);
#endif
  // Removed line
  // reportf("Verified %d original clauses.\n", clauses.size());
}

void CoreSMTSolver::checkLiteralCount()
{
  // Check that sizes are calculated correctly:
  int cnt = 0;
  for (int i = 0; i < clauses.size(); i++)
    if (clauses[i]->mark() == 0)
      cnt += clauses[i]->size();

  if ((int)clauses_literals != cnt){
    fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
    assert((int)clauses_literals == cnt);
  }
}

void CoreSMTSolver::printTrail( )
{
  for (int i = 0; i < trail.size(); i++)
  {
    printLit( trail[i] );
    // cerr << " | ";
    // printSMTLit( cerr, trail[i] );
    cerr << endl;
  }
}

map<Enode *, bool> CoreSMTSolver::getBoolModel() {
    map<Enode *, bool> ret;
    for (int i = 0; i < trail.size(); i++) {
        Lit const & l = trail[i];
        Var const v = var(l);
        if (v >= 2) {
            Enode * e = theory_handler->varToEnode(v);
            bool p = value(l) == l_True;
            if (e->isNot()) {
                e = e->get1st();
                p = !p;
            }
            if (e->isVar()) {
                if (sign(l)) {
                    p = !p;
                }
                ret.emplace(e, p);
            }
        }
    }
    return ret;
}

void CoreSMTSolver::printModel( )
{
  // Print Boolean model
  printModel( config.getRegularOut( ) );
  // Print Theory model
  egraph.printModel( config.getRegularOut( ) );
}

void CoreSMTSolver::printModel( ostream & out )
{
  for (Var v = 2; v < model.size(); v++)
  {
    Enode * e = theory_handler->varToEnode( v );
    if ( e->isTAtom( ) )
      continue;
    int tmp1, tmp2;
    if( sscanf( (e->getCar( )->getName( )).c_str( ), CNF_STR, &tmp1, &tmp2 ) != 1 )
      if ( model[ v ] != l_Undef )
        out << ( model[ v ] == l_True ? "" : "(not " ) << e << ( model[ v ] == l_True ? "" : ")" ) << endl;
  }
}

void CoreSMTSolver::printExtModel( ostream & out )
{
  for (Var v = 2; v < model.size(); v++)
  {
    Enode * e = theory_handler->varToEnode( v );
    int tmp1, tmp2;
    if( sscanf( (e->getCar( )->getName( )).c_str( ), CNF_STR, &tmp1, &tmp2 ) != 1 )
      if ( model[ v ] != l_Undef )
        out << ( model[ v ] == l_True ? "" : "(not " ) << e << ( model[ v ] == l_True ? "" : ")" ) << endl;
  }
}

void CoreSMTSolver::printCurrentAssignment( bool withLiterals )
{
  printCurrentAssignment( config.getRegularOut( ), withLiterals );
}

void CoreSMTSolver::printCurrentAssignment( ostream & out, bool  )
{
    for (Var v = 2; v < nVars(); v++)
      {
  Enode * e = theory_handler->varToEnode( v );
  if(e && !e->isTLit() && //model != NULL && model.size() >= v &&
     !e->isSymb()
     ){

    out << std::setw(40) << e << " : " << (assigns[v] == toInt(l_True) ? "T" : (assigns[v] == toInt(l_False) ? "F" : "U"))  << endl;
  }
      }

    const std::vector< Pair (Enode *) > substitutions = egraph.getSubstitutions();
  for(auto p : substitutions){
    if (p.second->isTrue()) {
      out  << std::setw(40) << p.first << " : T";
    } else if (p.second->isFalse()) {
      out  << std::setw(40) << p.first << " : F";
    }
    out << endl;
  }

}

json getModeFromEnode(Enode* e) {
  json mode_record = {};
  std::unordered_set<Enode *> vars = e->get_vars();
  if(vars.size() == 1){
    Enode* v = *vars.begin();
    std::stringstream ss;
    ss << v;
    string var = ss.str();
    // cout << "Got var: " << var << endl;
    if(var.find("mode_") == 0) {
          int aut_id_start = var.find("_")+1;
          int aut_id_end = var.find("_", aut_id_start+1);

          int aut_id = atoi(var.substr(aut_id_start,
                                       (aut_id_end - aut_id_start)).c_str());

          int start_step = var.find("_", aut_id_start)+1;
          int end_step = var.find("_", start_step+1);

          int step = atoi(var.substr(start_step,
                                     (end_step-start_step)).c_str());


          int start_mode_id = var.find("_", end_step)+1;
          int end_mode_id = var.find("_", start_mode_id+1);
          int mode_id = atoi(var.substr(start_mode_id,
                                        (end_mode_id - start_mode_id)).c_str());


          int start_mode = var.find_last_of("_")+1;
          int end_mode = var.size();
          string mode = var.substr(start_mode, end_mode-start_mode);




          int aut_start = var.find("_", end_mode_id)+1;
          int aut_end = var.find_last_of("_", start_mode-1);
          string automaton = var.substr(aut_start, aut_end-aut_start);



          // // int aut_end = 0;
          // std::regex r ("_[0-9]*_");
          // std::smatch m;
          // if(std::regex_search(var, m, r)){
          //   aut_end =
          // }

          // cout << "looking for mode, got: " << e << endl
          //      << "aut_id = " << aut_id << endl
          //      << "step = " << step << endl
          //      << "mode_id = " << mode_id << endl
          //      << mode << " " << start_mode << " " << end_mode << endl
          //      << automaton << " " << aut_start << " " << aut_end
          //      << endl;

          // modes.push_back(var);
          //modes[automaton][step] = mode;
          mode_record["automaton_id"] = aut_id;
          mode_record["step"] = step;
          mode_record["mode_id"] = mode_id;
          mode_record["mode"] = mode;
          mode_record["automaton"] = automaton;
    }
  }
  return mode_record;
}

json CoreSMTSolver::visualizeModes() const
{
  json modes = {};
  for (Var v = 2; v < nVars(); v++)
    {
      Enode * e = theory_handler->varToEnode( v );
      if(e && !e->isTLit() && //model != NULL && model.size() >= v &&
         !e->isSymb()){
        // cout << std::setw(40) << e << " : "
        //     << (assigns[v] == toInt(l_True) ? "T" :
        //      (assigns[v] == toInt(l_False) ? "F" : "U"))  << endl;
        if(assigns[v] == toInt(l_True)){
          json mode = getModeFromEnode(e);
          if(!mode.is_null()){
            modes.push_back(mode);
          }
        }
      }
    }

  const std::vector< Pair (Enode *) > substitutions = egraph.getSubstitutions();
  for(auto p : substitutions){
    if (p.second->isTrue()) {
      //cout  << std::setw(40) << p.first << " : T";
      json mode = getModeFromEnode(p.first);
      if(!mode.is_null()){
        modes.push_back(mode);
      }
    }
    //cout << endl;
  }
  return modes;
}

#endif
