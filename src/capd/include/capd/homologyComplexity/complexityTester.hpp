/// @addtogroup 2
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file complexityTester.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/homologyComplexity/complexityTester.h"
#include "capd/auxil/stringOstream.h"

// -- DELETE extern int lastAcyclicSubsetSize;
const int memLimit=200000000;

const double timeLimit=3600.0;

template<typename ObjectGenerator, typename ResultType>
std::string ComplexityTester<ObjectGenerator,ResultType>::findComplexity(
  int A_firstScale,
  int A_lastScale,
  int A_step,
  std::ostream& out
){
  vector<double> objectSize;
  vector<double> compTime;
  std::string result;
  double lastTime=0;

  int i=1;
  for(int s=A_firstScale;(A_lastScale-s)*A_step>=0;s+=A_step,++i){
    int card=0;
    try{
      fcout << "===========================================================" << std::endl;
      fcout << "Size " << s  << std::endl;
      long int mem=memSize();
      fcout << "Starting with memory available " << mem << std::endl;
      if(mem < memLimit) throw std::string("MemoryLimit");
      if(lastTime > timeLimit) throw std::string("TimeLimit");
      CRef<ObjectType> objectCR=m_objectGenerator.getObjectCR(s);
      card=objectCR().cardinality();
      fcout << "Cardinality is " << card << " elements" << std::endl;
      fcout << "Enclosing box is ";
      for(int j=0;j<objectCR().embDim();++j){
        fcout << objectCR().getUnpaddedWidth(j) << " ";
      }
      fcout  << std::endl;

      objectSize.push_back((double)card);
      Stopwatch sw;
// -- DELETE:       lastAcyclicSubsetSize=0;
      CRef<ResultType> resultCR=m_algorithm(objectCR);
      double t=lastTime=sw.processTime();
      compTime.push_back(t);
      fcout << "Total computation time is " << t << std::endl;
      fcout << "The algorithm outcome is:\n" << std::endl;
      fcout << resultCR() << std::endl;
//      result << i << "\t" << card << "\t" << sw << "\t" << lastAcyclicSubsetSize  << "\n";
      result << i << "\t" << card << "\t" << sw << "\n";
    }catch(std::bad_alloc& e){
      fcout << "Caught exception: " << e.what() << std::endl;
      fcout << "Memory available is " << memSize() << std::endl;
      compTime.push_back(0);
      result << i << "\t" << card << "\t" << " Out of memory "  << "\n";
    }catch(std::exception& e){
      fcout << "Caught exception: " << e.what() << std::endl;
      compTime.push_back(0);
      result << i << "\t" << card << "\t" << " Exception caught "  << "\n";
    }catch(std::string& s){
      if(s == "MemoryLimit"){
        compTime.push_back(-1);
        result << i << "\t" << card << "\t" << " -1 "  << "\n";
      }else if(s == "TimeLimit"){
        compTime.push_back(-2);
        result << i << "\t" << card << "\t" << " -2 "  << "\n";
      }else{
        fcout << "Caught exception: " << s << std::endl;
        compTime.push_back(0);
        result << i << "\t" << card << "\t" << " -3 "  << "\n";
      }
    }catch(const char* c){
      fcout << "Caught exception: " << c << endl;
      compTime.push_back(0);
      result << i << "\t" << card << "\t" << " Exception caught "  << "\n";
    }catch(...){
      fcout << "Caught an unknown exception: " << endl;
      compTime.push_back(0);
      result << i << "\t" << card << "\t" << " Exception caught "  << "\n";
    }

    fcout << "Finishing with memory available " << memSize() << std::endl;
  }
  fcout << "=============================================================" << std::endl;
  result << "=============================================================\n";

  if(A_lastScale>A_firstScale){
    std::pair<double,double> p=powerRegression(objectSize,compTime);
    result << "Time=(" << p.second << ")*card^(" << p.first << ")\n";
  }
  return result;
}
/// @}

