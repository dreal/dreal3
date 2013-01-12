
////////////////////////////////////////////////////////////////////////////
///
/// @file logger.h
///
/// This file contains definition of some output
/// streams that can be used instead the standard ones (sout, serr)
/// which support logging to a file or suppressing messages to the screen.
///
/// @author Pawel Pilarczyk, Marian Mrozek, Tomasz Kapela
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk, Marian Mrozek.
//
// This file constitutes a part of the CAPD Library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// Started in July 1997. Last revision: September 5, 2009.

#ifndef _CAPD_AUXIL_SOUTPUTS_H_
#define _CAPD_AUXIL_SOUTPUTS_H_

#include "capd/auxil/OutputStream.h"

#ifndef CAPD_OUTPUTSTREAM
/// This symbol is defined if the "OutputStream" class is available,
/// and the basic streams like "sout" are defined.
#define CAPD_OUTPUTSTREAM
#endif

namespace capd {
/// A replacement for standard output stream, with optional logging
/// and other features provided by the class 'OutputStream'.
extern ::capd::auxil::OutputStream sout;

/// The console output stream to which one should put all the junk that
/// spoils the log file, like progress indicators.
extern ::capd::auxil::OutputStream scon;

/// A wrapper for the standard error stream.
extern ::capd::auxil::OutputStream serr;

/// The output stream to which one can send messages for logging only.
/// Those messages are not shown to the standard output and are ignored
/// if the log file is not in use.
extern ::capd::auxil::OutputStream slog;

/// Another logging stream.
extern ::capd::auxil::OutputStream slog2;

/// Another logging stream.
extern ::capd::auxil::OutputStream slog3;

/// An output stream for writing additional debug messages.
/// This stream is turned off by default.
extern ::capd::auxil::OutputStream sbug;

/// An auxiliary stream which captures sequences of processed data.
extern ::capd::auxil::OutputStream sseq;

/// Defines how much output will be displayed to the screen (or default
/// output stream) and also saved to log files.
enum LogLevel { Silent, ProgresIdicators, LogLevel1, LogLevel2, LogLevel3, Debug, LogAll};

inline void setLogLevel(LogLevel level ){
  switch(level){
    case LogAll:
    case Debug:
      sbug.show = true;
    case LogLevel3:
      slog3.show = true;
    case LogLevel2:
      slog2.show = true;
    case LogLevel1:
      slog.show = true;
    case ProgresIdicators:
      scon.show = true;
    case Silent:
      break;
  }
  switch(level){
    case Silent:
      scon.show = false;
    case ProgresIdicators:
      slog.show = false;
    case LogLevel1:
      slog2.show = false;
    case LogLevel2:
      slog3.show = false;
    case LogLevel3:
      sbug.show = false;
    case Debug:
    case LogAll:
      break;
  }
} // setLogLevel

} // namespace capd

#endif // _CAPD_AUXIL_SOUTPUTS_H_

