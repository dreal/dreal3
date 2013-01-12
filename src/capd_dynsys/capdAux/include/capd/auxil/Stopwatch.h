/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Stopwatch.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_AUXIL_STOPWATCH_H_ 
#define _CAPD_AUXIL_STOPWATCH_H_ 

#include "capd/auxil/clock.h"

class Stopwatch{
  private:
    long double startWorldSecs,startProcessSecs;
  public:
    Stopwatch():
      startWorldSecs(getWorldSeconds()),
      startProcessSecs(getProcessSeconds()){
    }
    double worldTime() const{
      return (double)(getWorldSeconds()-startWorldSecs);
    }
    double processTime() const{
      return (double)(getProcessSeconds()-startProcessSecs);
    }
    friend std::ostream& operator<<(std::ostream& out, const Stopwatch& sw){
      double wt=sw.worldTime();
      double pt= sw.processTime();
      out   << pt << " proc secs (" << wt << " world secs)";
      return out;
    }
    void reset() {
      startWorldSecs = getWorldSeconds();
      startProcessSecs = getProcessSeconds();
    }
};


#endif // _CAPD_AUXIL_STOPWATCH_H_ 
/// @}

