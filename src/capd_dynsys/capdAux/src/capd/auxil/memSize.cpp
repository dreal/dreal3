#include <vector>
#include <limits>

unsigned long int memSize(){
  unsigned long int ileMin=0,ileMax=std::numeric_limits<unsigned long int>::max();
  unsigned long int ile=ileMax;
  while(ile>ileMin){
    try{
      char* t=new char[ile];
      if(t){
        ileMin=ile;
        delete[] t;
      }else{
        ileMax=ile;
      }
    }catch(std::bad_alloc){
      ileMax=ile;
    }
    ile=(ileMax+ileMin)/2;
  }
  return ile;
}


