/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BmpHeader.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#if !defined(_BMPHEADER_HPP_)
#define _BMPHEADER_HPP_

#include "capd/bitSet/BmpHeader.h"
using namespace std;

inline unsigned int get2ByteUInt(std::ifstream& f){
   unsigned short int i=0;
   f.read(reinterpret_cast<char*>(&i),2);
   return i;
}

inline unsigned int get4ByteUInt(std::ifstream& f){
   unsigned int i=0;
   f.read(reinterpret_cast<char*>(&i),4);
   return i;
}

inline void put2ByteUInt(std::ofstream& f, int j){
   unsigned short int i=static_cast<unsigned short int>(j);
   f.write(reinterpret_cast<char*>(&i),2);
}

inline void put4ByteUInt(std::ofstream& f, int j){
   f.write(reinterpret_cast<char*>(&j),4);
}

inline void showInt(const char* text, int n){
  std::cout << "Field " << text << " is " << std::dec << n << " (" << std::hex << n << ")\n" << std::dec ;
}

//template<>
inline void BmpHeader<unsigned long int,2>::showHeader(){
  showInt("type",type);
  showInt("size",size);
  showInt("reserved1",reserved1);
  showInt("reserved2",reserved2);
  showInt("offset",offset);
  showInt("ihsize",ihsize);
  showInt("width",width);
  showInt("height",height);
  showInt("planes",planes);
  showInt("bits",bits);
  showInt("compression",compression);
  showInt("imagesize",imagesize);
  showInt("xresolution",xresolution);
  showInt("yresolution",yresolution);
  showInt("ncolours",ncolours);
  showInt("importantcolours",importantcolours);
  showInt("color0",color0);
  showInt("color1",color1);
}

template<typename word, int dim>
inline void BmpHeader<word,dim>::showHeader(){
  showInt("type",type);
}


inline void BmpHeader<unsigned long int,2>::read(std::ifstream& file){
  type=get2ByteUInt(file);               // Magic identifier
  if( type == standardType ){                                // File size in bytes
    size=get4ByteUInt(file);
    reserved1=get2ByteUInt(file);
    reserved2=get2ByteUInt(file);
    offset=get4ByteUInt(file);             // Offset to image data in bytes

    ihsize=get4ByteUInt(file);             // Info header size in bytes
    width=get4ByteUInt(file);                       // Width of image
    height=get4ByteUInt(file);                      // Height of image
    planes=get2ByteUInt(file);             // Number of colour planes
    bits=get2ByteUInt(file);               // Bits per pixel
    compression=get4ByteUInt(file);        // Compression type
    imagesize=get4ByteUInt(file);          // Image size in bytes
    xresolution=get4ByteUInt(file);                 // Pixels per meter in x dir
    yresolution=get4ByteUInt(file);                 // Pixels per meter in y dir
    ncolours=get4ByteUInt(file);           // Number of colours
    importantcolours=get4ByteUInt(file);   // Important colours


    if( bits != 1 ){                                // bits per pixel
      std::ostringstream s;
      s << "This is not a black and white image. Field bits must be one and is: " << bits << " colors" << std::endl;
      throw std::runtime_error(s.str());
    }


    color0=get4ByteUInt(file);
    color1=get4ByteUInt(file);
//showHeader();
  }else{
    std::ostringstream s;
    s << "Got file type " << type << ". Should be " << standardType << "(classical 2 dim bitmap)" << std::endl;
//    throw std::runtime_error(s.str());
    throw EmbDimException(s.str());
  }

}

template<typename word, int dim>
void BmpHeader<word,dim>::read(std::ifstream& file){
  type=get2ByteUInt(file);               // Magic identifier
  if( type == multidimType || type == repsetType){ // File size in bytes
    dimension=get4ByteUInt(file);
    if(dimension != dim){
      std::ostringstream s;
      s << "When reading BmpHeader found dimension " << dimension << ". Should be " << dim << std::endl;
//      throw std::runtime_error(s.str());
      throw EmbDimException(s.str());
    }
    length=get4ByteUInt(file);
    actualDimZeroBitWidth=get4ByteUInt(file);
    for(int i=0;i<dimension;++i){
      paddedBitWidth[i]=get4ByteUInt(file);
    }
  }else{
    std::ostringstream s;
    s << "Got file type " << type << ". Should be " << multidimType << " (multidim bitmap) or " << repsetType << " (repset multidim bitmap) " << std::endl;
    throw std::runtime_error(s.str());
  }
}

inline void BmpHeader<unsigned long int,2>::write(std::ofstream& file){
  put2ByteUInt(file,standardType);               // Magic identifier

  put4ByteUInt(file,size);
  put2ByteUInt(file,0);
  put2ByteUInt(file,0);
  put4ByteUInt(file,offset);             // Offset to image data in bytes

  put4ByteUInt(file,ihsize);             // Info header size in bytes
  put4ByteUInt(file,width);                       // Width of image
  put4ByteUInt(file,height);                      // Height of image
  put2ByteUInt(file,planes);             // Number of colour planes
  put2ByteUInt(file,bits);               // Bits per pixel
  put4ByteUInt(file,compression);        // Compression type
  put4ByteUInt(file,imagesize);          // Image size in bytes
  put4ByteUInt(file,xresolution);                 // Pixels per meter in x dir
  put4ByteUInt(file,yresolution);                 // Pixels per meter in y dir
  put4ByteUInt(file,ncolours);           // Number of colours
  put4ByteUInt(file,importantcolours);   // Important colours
  put4ByteUInt(file,color0);
  put4ByteUInt(file,color1);
}

template <typename word, int dim>
void BmpHeader<word,dim>::write(std::ofstream& file){
//  put2ByteUInt(file,multidimType);               // Magic identifier
  put2ByteUInt(file,type);    // New type may be 'BD' for cubical sets or 'BR' for representable sets ('BM' is for classical 2d bitmaps)
  if(dimension != dim){
    std::ostringstream s;
    s << "When writing BmpHeader found dimension " << dimension << ". Should be " << dim << std::endl;
    throw std::runtime_error(s.str());
  }
  put4ByteUInt(file,dim);
  put4ByteUInt(file,length);
  put4ByteUInt(file,actualDimZeroBitWidth);
  for(int i=0;i<dim;++i){
    put4ByteUInt(file,paddedBitWidth[i]);
  }
}
#endif //_BMPHEADER_HPP_

/// @}

