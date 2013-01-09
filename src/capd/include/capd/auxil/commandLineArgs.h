/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file commandLineArgs.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_CAPD_COMMANDLINEARGS_H_)
#define _CAPD_COMMANDLINEARGS_H_
#include <map>
#include "capd/auxil/stringOstream.h"

typedef std::map<std::string,std::string> OptionMapType;
typedef std::string::size_type IndexType;

// Read the arguments in argv, decompose pairs key=value and store
// the (key,value) pairs in the map m provided
// When no = is present treat it as a value with key=1,2,3...
inline void _CAPD_COMMANDLINEARGS_decomposeArgv(int argc,char** argv,OptionMapType& A_m){
  int fileNameCnt=0;
  for(int i=1;i<argc;++i){
    std::string arg(argv[i]);
    IndexType idx;
    idx=arg.find("=");
    if(idx == std::string::npos){
      std:: string s;
      s << (++fileNameCnt);
      A_m.insert(make_pair(s,arg));
    }else{
      std::string argName(arg,0,idx);
      std::string argVal(arg,idx+1,arg.length()-idx-1);
      A_m.insert(make_pair(argName,argVal));
    }
  }
}

// Count the number of times A_val appers as value in the map A_m
// Return the pair (count,arg), where count is the number computed and arg is the key of the first
// value found
inline std::pair<int,std::string> _CAPD_COMMANDLINEARGS_valCount(const std::string& A_val,OptionMapType& A_m){
  OptionMapType::iterator it;
  int count=0;
  std::string arg;
  for(it=A_m.begin();it!=A_m.end();++it){
    if(it->second == A_val){
      ++count;
      arg=it->first;
    }
  }
  return std::make_pair(count,arg);
}

// This function returns the number of files on command line
inline int _CAPD_COMMANDLINEARGS_fileCount(OptionMapType& A_m){
  int i=0;
  while(true){
    std:: string s;
    s << (++i);
    if(!A_m.count(s)) return i-1;
  }
}

// This function returns the ith file on command line
inline std::string _CAPD_COMMANDLINEARGS_getFile(int i,OptionMapType& A_m){
  std:: string s;
  s << i;
  return (A_m.count(s) ? A_m[s]  :  "" );
}

// A macro declaring an std::map _command_line_args_ for command
// line args and calling _CAPD_COMMANDLINEARGS_decomposeArgv to setup its values
#define setupCommandLineArgs                                   \
  OptionMapType _command_line_args_;                           \
  _CAPD_COMMANDLINEARGS_decomposeArgv(argc,argv,_command_line_args_);

// A macro to declare a variable for a named command line argument,
// assign it a default value and replace it by the command line argument
// value if provided
#define declareCommandLineArg(type,name,value)                 \
  type name(value);                                            \
  if(_command_line_args_.count(#name)){                        \
    std::istringstream iss(_command_line_args_[#name]);        \
    iss >> name;/* std::cout << #name << "=" << name;*/}                                              \

// A macro to assign a value to a global variable from
// the command line argument value if provided.
// The declaration must be provided seperately
#define assignCommandLineArgValue(name)                        \
  if(_command_line_args_.count(#name)){                        \
    std::istringstream iss(_command_line_args_[#name]);        \
    iss >> name;}

// Command line arguments not in the form arg=value
// are referred to as files and numbered by consecutive
// numbers starting from 1. The following macro returns
// the ith file
#define getCommandLineFile(i)                                  \
  _CAPD_COMMANDLINEARGS_getFile(i,_command_line_args_)

// This is a shortcut for _CAPD_COMMANDLINEARGS_fileCount above
#define getCommandLineFileCount()                              \
  _CAPD_COMMANDLINEARGS_fileCount(_command_line_args_)

// This is a shortcut for _CAPD_COMMANDLINEARGS_valCount above
// to work on _command_line_args_
#define getValueCountAndArg(value)                             \
  _CAPD_COMMANDLINEARGS_valCount(value,_command_line_args_)

// A macro printing all command line args to std::cout
#define showCommandLineArgs                                    \
  for(OptionMapType::const_iterator                            \
      it=_command_line_args_.begin();                          \
      it!=_command_line_args_.end();                           \
      ++it)                                                    \
      std::cout << "arg[" << it->first <<                      \
      "]=" << it->second << std::endl;

#endif //_CAPD_COMMANDLINEARGS_H_

/// @}
