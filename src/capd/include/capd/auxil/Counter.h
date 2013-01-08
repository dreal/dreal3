//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file Counter.h
///
/// @author Tomasz Kapela   @date 2010-03-11
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_AUXIL_COUNTER_H_
#define _CAPD_AUXIL_COUNTER_H_
#include "capd/auxil/logger.h"
#include <set>

namespace capd{
namespace auxil{

/**
 * Counter add to each object of given class unique id and also counts number of objects created and existing.
 *
 * This class is for debugging purpose mainly. It reports each creation and destruction to capd::slog stream.
 * You can turn on/off its output by
 * \code  capd::slog.show = true/false; \endcode
 * For example output:
 * < + A [34][12] >
 * means that there was created object (+) of class A
 * with id=34 (we start with id=1) and that at this moment there exit 12 objects.
 * Destruction is denoted by '-' and substitution by '='.
 *
 * To add counter to your class A simply inherit from Counter<A> i.e.:
 * \code
 *    class A: public capd::auxil::Counter<A>{
 *      ...
 *    };
 * \endcode
 *
 * @remark If class A defines its own copy constructor and/or operator= and
 *         you do not manually call corresponding functions from Counter
 *         than default constructor will be reported for copy constructor
 *         and nothing for =.
 *
 */
template <typename T>
class Counter{
public:
  typedef std::set<int> IndicesSetType;
  typedef T CountedType;

  int id;                            ///< unique id of the object
  static int maxIndex;               ///< number of created objects
  static int numberOfObjects;        ///< number of existing objects
  static IndicesSetType indicesSet;  ///< set of indices of existing objects
  static bool storeIndices;          ///< decides if indices of existing objects should be stored
  static std::string name;           ///< string that help distinguish counters for different classes

  Counter() : id(++maxIndex){
    ++numberOfObjects;
    capd::slog << "\n< + " << name << " [" << id << "][" << numberOfObjects << "] >";
    if(storeIndices) indicesSet.insert(id);
  }
  Counter(const Counter & c): id(++maxIndex){
      ++numberOfObjects;
      capd::slog << "\n< + " << name << " [" << id << "][" << numberOfObjects << "]  copy from [" << c.id << " ] >" ;
      if(storeIndices) indicesSet.insert(id);
  }
  void operator=(const Counter & c){
      capd::slog << "\n< = " << name << " [" << id << "] = [" << c.id <<"] >";
  }
  ~Counter(){
      -- numberOfObjects;
      capd::slog << "\n< - " << name << " [" << id << "][" << numberOfObjects << "] >";
      if(storeIndices) indicesSet.erase(id);
  }
};

template <typename T>
int Counter<T>::maxIndex = 0;

template <typename T>
int Counter<T>::numberOfObjects = 0;

template <typename T>
bool Counter<T>::storeIndices = true;

template <typename T>
std::set<int> Counter<T>::indicesSet;

template <typename T>
std::string Counter<T>::name = "";
}} // end of namespace capd::auxil

#endif // _CAPD_AUXIL_COUNTER_H_
