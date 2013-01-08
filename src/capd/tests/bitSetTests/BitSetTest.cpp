#include <iostream>
#include <exception>
#include <sstream>
#include <string>

#include "capd/bitSet/BitmapT.h"
#include "capd/bitSet/BitSetT.h"

typedef unsigned long int word;
using namespace std;

int main(){
  try{
    string as("0101010101 1010101010 0101010101 1010101010 0101010101 1010101010 0101010101 1010101010 0101010101 1010101010");
    string bs("0101010101 0101010101 0101010101 0101010101 0101010101 0101010101 0101010101 0101010101 0101010101 0101010101");
    string cs("0101010101111111111101010101011111111111010101010111111111110101010101111111111101010101011111111111");
    string ds("0101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101");
    BitSetT<BitmapT<word> > a(as),b(bs),c(cs),d(ds);

    bool success=true;
    cout << "\n === BitSet Test ===\n\n";
    cout << "a=" << a << std::endl;
    cout << "b=" << b << std::endl;
    a+=b;
    cout << "c=" << a  << std::endl;
    if(!(a==c)){
      cout << " Test for += failed\n";
      success =false;
    }
    a*=b;
    cout << "d=" << a  << std::endl;
    if(!(a==d)){
      cout << " Test for *= failed\n";
      success =false;
    }
    if(success) cout << "\n === Test successfully completed ===\n";
  }catch(std::exception& e){
    cout << "Caught exception: " << e.what() << endl;
  }catch(std::string& as){
    cout << "Caught exception: " << as.c_str() << endl;
  }catch(const char* c){
    cout << "Caught exception: " << c << endl;
  }catch(...){
    cout << "Caught an unknown exception: " << endl;
  }
}
