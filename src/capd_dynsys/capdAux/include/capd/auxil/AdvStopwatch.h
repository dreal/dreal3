/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file AdvStopwatch.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_AUXIL_ADVSTOPWATCH_H_
#define _CAPD_AUXIL_ADVSTOPWATCH_H_

#include "capd/auxil/clock.h"

class AdvStopwatch{
  private:
    mutable long double startWorldSecs,startProcessSecs;
    mutable long double runningWorldSecs,runningProcessSecs;
    mutable bool running;
  public:
    AdvStopwatch():
      startWorldSecs(getWorldSeconds()),
      startProcessSecs(getProcessSeconds()),
      runningWorldSecs(0),
      runningProcessSecs(0),
      running(true)
    {}

    void start() const{
      if(!running){
        startWorldSecs=getWorldSeconds();
        startProcessSecs=getProcessSeconds();
        running=true;
      }
    }

    void stop() const{
      if(running){
        runningWorldSecs+=getWorldSeconds()-startWorldSecs;
        runningProcessSecs+=getProcessSeconds()-startProcessSecs;
        running=false;
      }
    }

    void record() const{
      stop();
      start();
    }

    double worldTime() const{
      return (double)(runningWorldSecs);
    }

    double processTime() const{
      return (double)(runningProcessSecs);
    }

    friend std::ostream& operator<<(std::ostream& out, const AdvStopwatch& sw){
      sw.record();
      double wt=sw.worldTime();
      double pt= sw.processTime();
      out   << pt << " proc secs (" << wt << " world secs)";
      return out;
    }
};


#endif // _CAPD_AUXIL_ADVSTOPWATCH_H_
/// @}

