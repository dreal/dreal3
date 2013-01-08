/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CRef.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_AUXIL_CREF_H_ 
#define _CAPD_AUXIL_CREF_H_ 

#include <stdexcept>

template<typename T>
class CRef;

template<typename T>
class CRef{
  private:
    T* ptr;
    int* cnt;
    void remove() {
      if (cnt && (--*cnt == 0)){
        delete cnt;
        if(ptr) delete ptr;
      }
    }
  public:
    explicit CRef():ptr(0),cnt(0){}
    explicit CRef(T* p):ptr(p),cnt(new int(1)){}
    CRef(const CRef<T>& p)throw():ptr(p.ptr),cnt(p.cnt){
      if(cnt) ++*cnt;
    }
    ~CRef()throw(){
      remove();
    }
    CRef<T>& operator=(const CRef<T>& p)throw(){
      if(this != &p){
        remove();
        ptr=p.ptr;
        cnt = p.cnt;
        if(cnt) ++*cnt;
      }
      return *this;
    }
    T& operator()() const throw(std::domain_error){
      if(ptr) return *ptr;
      throw std::domain_error("CRef::operator() : null reference");
    }
    T& operator*() const throw(std::domain_error){
      if(ptr) return *ptr;
      throw std::domain_error("CRef::operator* : null reference");
    }
    int count() const throw(std::domain_error){
      if(cnt) return *cnt;
      throw std::domain_error("CRef::count : null reference");
    }
    bool isNull(){
      return !ptr;
    }
    friend std::ostream& operator<<(std::ostream& out,const CRef<T>& A_CRef){
      out << "CRef pointing at address " << std::hex << A_CRef.ptr;
      out << " with count=" << std::dec << *A_CRef.cnt << " ";
      return out;
    }
};
#endif // _CAPD_AUXIL_CREF_H_ 

/// @}

