/// @addtogroup matrixAlgorithms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSetT.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_EUCL_BIT_SET_HPP_)
#define _EUCL_BIT_SET_HPP_

#include "capd/bitSet/EuclBitSetT.h"
#include "capd/auxil/skipCommentsIstream.h"
#include "capd/bitSet/EmbDimException.h"
#include "capd/auxil/stringOstream.h"

/************************************************************************************/
// Auxiliary method.
// It is assumed that originally paddedBitWidth contains actual requested widths in all directions
// The method updates paddedBitWidth[0] to contain correct paddedBitWitdh
// and sets up actualDimZeroBitWidth, WordWidth and length
template <typename P_BitSet,int dim>
void EuclBitSetT<P_BitSet,dim>::setupWidths(){
  actualDimZeroBitWidth=paddedBitWidth[0];
  paddedBitWidth[0]=(paddedBitWidth[0]/bitsPerWord+(paddedBitWidth[0] % bitsPerWord != 0))*bitsPerWord;
  wordWidth[0]=paddedBitWidth[0]/bitsPerWord;

  for(int i=1;i<embDim();++i){
    wordWidth[i]=paddedBitWidth[i];
  }
  this->length=wordWidth[0];
  // -- MM  cout << "Memory requested for [";  // *** DEBUG *** //

  for(int i=1;i<embDim();++i){
  // -- MM  cout << paddedBitWidth[i] << " ";  // *** DEBUG *** //

    unsigned int loglength=baseTwoLog(this->length)+baseTwoLog(paddedBitWidth[i]);
    if( loglength > 8*sizeof(unsigned long int)){
      std::string s;
      s << "Size of unsigned long int is to small to contain the length of the bitmap:\n  " << "paddedBitWidth[" << i << "]=" << paddedBitWidth[i] << " length=" << this->length << "\n";
      throw std::runtime_error(s);
    }
    this->length*=paddedBitWidth[i];
  }
  // -- MM  cout << "]" << this->length/8 << " bytes" << std::endl; // *** DEBUG *** //
}
/************************************************************************************/

template <typename P_BitSet,int dim>
void EuclBitSetT<P_BitSet,dim>::setupStrides(){
  int bitStride[dim];
  int sumBitStride[dim];

  wordStride[0]=1;
  bitStride[0]=1;
  sumBitStride[0]=bitStride[0];
  neighbStride[0]=1;

  for(int i=1;i<dim;++i){
    wordStride[i]=wordStride[i-1]*wordWidth[i-1];
    bitStride[i]=bitStride[i-1]*paddedBitWidth[i-1];
    sumBitStride[i]=sumBitStride[i-1]+bitStride[i];
    neighbStride[i]=-2*sumBitStride[i-1]+bitStride[i];
  }
  sumBitStrides=sumBitStride[dim-1];
}
/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(int size,bool clear){
  for(int i=0;i<dim;++i){
    paddedBitWidth[i]=size;
  }
  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(this->length);
  if(clear) internalBitSet.clear();
  swap(internalBitSet,*(P_BitSet*)(this));
}

/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(const int* w,bool clear){
  for(int i=0;i<dim;++i){
    paddedBitWidth[i]=w[i];
  }
  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(this->length);
  if(clear) internalBitSet.clear();
  swap(internalBitSet,*(P_BitSet*)(this));
}

/************************************************************************************/

// BitmapT from a provided bitmap data
template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(const int* w, const char* bytes){
  for(int i=0;i<dim;++i){
    paddedBitWidth[i]=w[i];
  }
  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(this->length,const_cast<char*>(bytes));
  swap(internalBitSet,*(P_BitSet*)(this));
}

/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(const EuclBitSetT& org,bool clear){
  for(int i=0;i<dim;++i){
    paddedBitWidth[i]=org.paddedBitWidth[i];
  }
  // before setupWidths is called paddedBitWidth[0] should contain unpadded bit width
  paddedBitWidth[0]=org.actualDimZeroBitWidth;
  // after calling setupWidths() paddedBitWidth[0] will contain the padded  bit width
  setupWidths();
  setupStrides();


  P_BitSet internalBitSet(org.getBitSet(),clear);
  swap(internalBitSet,*(P_BitSet*)(this));
}

/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(const EuclBitSetT& org,const std::vector<int>& lc,const std::vector<int>& uc){
  for(int i=0;i<dim;++i){
    if(lc[i]<0 || uc[i]>=org.paddedBitWidth[i]) throw "EuclBitSetT: incorrect part\n";
    paddedBitWidth[i]=uc[i]-lc[i]+1;
  }
  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(this->length);
  internalBitSet.clear();
  swap(internalBitSet,*(P_BitSet*)(this));

  // This part could be written more efficiently
  BitCoordIterator it(*this);
  for(it=this->begin();it<this->end();++it){
    int c[dim];
    for(int i=0;i<dim;++i) c[i]=lc[i]+it[i];
    if( it[0]< this->actualDimZeroBitWidth && org.contains(Pixel(c))) it.setBit();
  }
}

/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(const EuclBitSetT& org,const Pixel& lc,const Pixel& uc){
  for(int i=0;i<dim;++i){
    if(lc.coord[i]<0 || uc.coord[i]>=org.paddedBitWidth[i]) throw "EuclBitSetT: incorrect part\n";
    paddedBitWidth[i]=uc.coord[i]-lc.coord[i]+1;
  }
  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(this->length);
  internalBitSet.clear();
  swap(internalBitSet,*(P_BitSet*)(this));

  // This part could be written more efficiently
  BitCoordIterator it(*this);
  for(it=this->begin();it<this->end();++it){
    int c[dim];
    for(int i=0;i<dim;++i) c[i]=lc.coord[i]+it[i];
    if( it[0]< this->actualDimZeroBitWidth && org.contains(Pixel(c))) it.setBit();
  }
}

/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(const RepSet<ElementaryCube>& A_RepSetOfElementaryCube){
  if(A_RepSetOfElementaryCube.embeddingDimension()!=dim) throw EmbDimException("EuclBitSetT<P_BitSet,dim>::importRepSetOfElementaryCube: incorrect embedding dimension");
  int minCoord[dim];
  int maxCoord[dim];
  A_RepSetOfElementaryCube.lowerEnclosingBox(minCoord,maxCoord);
  for(int i=0;i<dim;++i){
    paddedBitWidth[i]=maxCoord[i]-minCoord[i]+1;
  }
  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(this->length,true); // clear
  swap(internalBitSet,*(P_BitSet*)(this));

  typename std::set<ElementaryCube>::const_iterator pos;
  for(pos=A_RepSetOfElementaryCube.begin(); pos != A_RepSetOfElementaryCube.end(); ++pos){
    const ElementaryCube& current=*pos;
//    if(current.dimension()!=dim) throw std::runtime_error("EuclBitSetT<P_BitSet,dim>::importRepSetOfElementaryCube: not a full elementary cube");
    if(current.dimension()!=dim) throw DimException("EuclBitSetT<P_BitSet,dim>::importRepSetOfElementaryCube: not a full elementary cube");
    int coord[dim];
    for(int i=0;i<dim;++i){
      coord[i]=current.leftCoordinate(i)-minCoord[i];
    }
    addPixel(typename EuclBitSetT<P_BitSet,dim>::Pixel(coord));
//fcout << "  Cardinality is " << this->cardinality() << std::endl;
  }
}

/************************************************************************************/

/*
template <typename P_BitSet,int dim>
template <typename P_Chain>
EuclBitSetT<P_BitSet,dim>::EuclBitSetT(const P_Chain& chain, const EuclBitSetT& space){
  EuclBitSetT internalBitSet(space,true);
  typename P_Chain::const_iterator it;
  for(it=chain.begin();it!=chain.end();++it){
//    if(it->second % 2 == ScalarType(1)){
    if(it->second != ScalarType(0)){
      int coords[dim];
      it->first.getVals(coords);
      BitCoordIterator it(internalBitSet,coords);
      it.setBit();
    }
  }
  swap(internalBitSet,*(EuclBitSetT*)(this));

}
*/

/************************************************************************************/

template <typename P_BitSet,int dim>
void EuclBitSetT<P_BitSet,dim>::addBox(const Pixel& lc,const Pixel& uc){
  BitCoordIterator it(*this);
  for(it=this->begin();it<this->end();++it){
    for(int k=0;k<dim;++k) if(it[k]<lc.coord[k] || it[k]>uc.coord[k]) goto next;
    it.setBit();
    next:;
  }
}

/************************************************************************************/

template <typename P_BitSet,int dim>
void EuclBitSetT<P_BitSet,dim>::addBoxBoundary(const Pixel& lc,const Pixel& uc){
  BitIterator it(*this);
    for(it=this->begin();it<this->end();++it){
    Pixel p(it);
    for(int k=0;k<dim;++k) if(p.coord[k]<lc.coord[k] || p.coord[k]>uc.coord[k]) goto next;
    for(int k=0;k<dim;++k) if(p.coord[k]==lc.coord[k] || p.coord[k]==uc.coord[k]){
      it.setBit();
      goto next;
    }
    next:;
  }
}

/************************************************************************************/

template <typename P_BitSet,int dim>
template<typename Selector>
EuclBitSetT<P_BitSet,dim>& EuclBitSetT<P_BitSet,dim>::add(const Selector& select,bool clear){
  BitCoordIterator it(*this);
  for(it=this->begin();it<this->end();++it){
    if( select(it.coords()) ){
      it.setBit();
    }else if(clear) it.clearBit();
  }
  return *this;
}

/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>& EuclBitSetT<P_BitSet,dim>::wrap(){
  // in org we keep the copy of the original bitmap
  const EuclBitSetT<P_BitSet,dim> org(*this);

  typename EuclBitSetT<P_BitSet,dim>::PointIterator itOrg(org.begin());
  typename EuclBitSetT<P_BitSet,dim>::PointIterator itEnd(org.end());
  for(;itOrg<itEnd;++itOrg){
    BitIterator it(*this,itOrg);
    NeighbIterator nbIt=this->neighbBegin(it);
    BitIterator nbhdEndIt=this->neighbEnd(it);
    for(;nbIt<nbhdEndIt;++nbIt){
      nbIt.setBit();
    }
  }

  return *this;
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline EuclBitSetT<P_BitSet,dim>& EuclBitSetT<P_BitSet,dim>::peel(){
  this->invert();
  this->wrap();
  this->invert();
  return *this;
}


/************************************************************************************/

template<>
void EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,2>::readBmp(const char* fileName){
//std::cout << "Reading ... \n";
  std::ifstream file(fileName,std::ios::in|std::ios::binary);
  BmpHeader<unsigned long int,2> header;
  header.read(file);

  paddedBitWidth[0]=header.width;
  paddedBitWidth[1]=header.height;
  setupWidths();
  setupStrides();

  BitSetT<BitmapT<unsigned long int> > internalBitSet(this->length,true);
  swap(internalBitSet,*(BitSetT<BitmapT<unsigned long int> >*)(this));

  int bytesToRead=paddedBitWidth[0]*header.height/8;

  unsigned char* byteBitmapPtr=reinterpret_cast<unsigned char *>(bitmap);
  file.read(reinterpret_cast<char *>(byteBitmapPtr),bytesToRead);

  // In bmp files each byte stores bits in a reversed order, so we need to change
  unsigned char* byteBitmapEndPtr=byteBitmapPtr+bytesToRead;
  for(unsigned char* cPtr=byteBitmapPtr; cPtr<byteBitmapEndPtr;++cPtr){
    char w=0;
    for(int i=0;i<8;++i){
      w = w | (((*cPtr >> i) & 1) << (7-i));
    }
    *cPtr=w;
  }


  if(header.color1>header.color0){ // black indicated by 0 index, so we must invert
    // We need to invert (flip), because black pixels are stored as zeros
    // We cannot use the class invert method, because in the bitmap file
    // the excess bits resulting from padding to 32 bits are marked as black
    for(int i=0;i<header.height;++i){
//std::cout << "Line " << i  << std::endl;
      unsigned long int* wordPtr=bitmap+i*paddedBitWidth[0]/bitsPerWord;
      for(int j=0;j<header.width;j+=bitsPerWord){
//std::cout << "  Word " << j  << std::endl;
        *wordPtr=~(*wordPtr);
        // In the last byte,
        // if width is not a multiciplity of bitsPerWord,
        // we need to cut the excessive inverted bytes
        int validExtraBits;
        if( (validExtraBits=header.width-j)<bitsPerWord){
//std::cout << "  Word before invertion " << std::hex << *wordPtr  << std::dec << std::endl;
          *wordPtr &= ((1 << validExtraBits)-1);
//std::cout << "  Word after invertion " << std::hex << *wordPtr  << std::dec << std::endl;
        };
        ++wordPtr;
      }
    }
  }
}

/************************************************************************************/

template <typename P_BitSet,int dim>
void EuclBitSetT<P_BitSet,dim>::readBmp(const char* fileName){
  std::ifstream file(fileName,std::ios::in|std::ios::binary);
  BmpHeader<typename P_BitSet::Word,dim> header;
  header.read(file);


  for(int i=0;i<dim;++i){
    paddedBitWidth[i]=header.paddedBitWidth[i];
  }
  // To make it compatible with setupWidths, we assign first header.actualDimZeroBitWidth
  // to paddedBitWidth[0], it will be then corrected by setupWidths
  paddedBitWidth[0]=header.actualDimZeroBitWidth;

  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(this->length,true); // true means clear
  swap(internalBitSet,*(P_BitSet*)(this));

  int bytesToRead=this->length*sizeof(Word);

  char* byteBitmapPtr=reinterpret_cast<char *>(this->bitmap);
  file.read(byteBitmapPtr,bytesToRead);
}

/************************************************************************************/

template<>
void EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,2>::writeBmp(const char* fileName,unsigned int){
  std::ofstream file(fileName,std::ios::out|std::ios::binary);
  BmpHeader<unsigned long int,2> header;
  // Under construction!!!
  // Header must be properly setup before it is written!!!
  int bytesToWrite=length*sizeof(unsigned long int);
  header.offset=62;
  header.size=bytesToWrite+header.offset;
  header.ihsize=40;
  header.width=actualDimZeroBitWidth;
  header.height=paddedBitWidth[1];
  header.planes=1;
  header.bits=1;
  header.compression=0;
  header.imagesize=0;
  header.xresolution=0;
  header.yresolution=0;
  header.ncolours=2;
  header.importantcolours=0;
  header.color0=0xffffff;  // define that index 0 means white
  header.color1=0;         // define that index 1 means black
  header.write(file);

  // In bmp files each byte stores bits in a reversed order, so we need to change
  char* byteBitmapPtr=reinterpret_cast<char *>(bitmap);
  char* byteBitmapEndPtr=byteBitmapPtr+bytesToWrite;
  for(char* cPtr=byteBitmapPtr; cPtr<byteBitmapEndPtr;++cPtr){
    char w=0;
    for(int i=0;i<8;++i){
      w = w | (((*cPtr >> i) & 1) << (7-i));
    }
    *cPtr=w;
  }
  file.write(byteBitmapPtr,bytesToWrite);
}

/************************************************************************************/

template <typename P_BitSet,int dim>
void EuclBitSetT<P_BitSet,dim>::writeBmp(const char* fileName,unsigned int A_type){
  std::ofstream file(fileName,std::ios::out|std::ios::binary);
  BmpHeader<typename P_BitSet::Word,dim> header;
  header.type=A_type;  // multidimType is 'BM', repsetType is 'BR'
  header.dimension=dim;
  header.length=this->length;
  header.actualDimZeroBitWidth=actualDimZeroBitWidth;
  for(int i=0;i<dim;++i){
    header.paddedBitWidth[i]=paddedBitWidth[i];
  }
  header.write(file);
  int bytesToWrite=this->length*sizeof(Word);
  char* byteBitmapPtr=reinterpret_cast<char *>(this->bitmap);
  file.write(byteBitmapPtr,bytesToWrite);
}

/************************************************************************************/

template <typename P_BitSet,int dim>
EuclBitSetT<P_BitSet,dim>& EuclBitSetT<P_BitSet,dim>::operator=(const EuclBitSetT<P_BitSet,dim>& set2){
  if(&set2==this) return *this;
  paddedBitWidth[0]=set2.actualDimZeroBitWidth; // setupWidths requests unpadded width in paddedBitWidth[0]!!
  for(int i=1;i<dim;++i){
    paddedBitWidth[i]=set2.paddedBitWidth[i];
  }
  setupWidths();
  setupStrides();

  P_BitSet internalBitSet(set2.getBitSet());
  swap(internalBitSet,*(P_BitSet*)(this));

  return *this;
}

/************************************************************************************/

template <typename P_BitSet,int dim>
bool EuclBitSetT<P_BitSet,dim>::findSomePoint(Pixel& p) const{
  PointIterator it(*this);
  if(it.findPoint()){
    p=Pixel(it);
    return true;
  }else{
    return false;
  }
}

/************************************************************************************/

template <typename P_BitSet,int dim>
bool EuclBitSetT<P_BitSet,dim>::midPoint(Pixel& p) const{
  if(this->empty()) return false;
  PointCoordIterator it(*this);
  for(int i=0;i<dim;++i) p.coord[i]=0;
  for(it=this->begin();it<this->end();++it) for(int i=0;i<dim;++i) p.coord[i]+=it[i];
  int card=this->cardinality();
  for(int i=0;i<dim;++i) p.coord[i]=int(p.coord[i]/(double)card+0.5);
  return true;
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline bool EuclBitSetT<P_BitSet,dim>::contains(const Pixel& p) const{
  if(p.coord[0]<0 || p.coord[0]>=actualDimZeroBitWidth) return false;
  for(int i=1;i<dim;++i) if(p.coord[i]<0 || p.coord[i]>=paddedBitWidth[i]) return false;
  return BitIterator(*this,p).getBit();
}

/************************************************************************************/

template <typename P_BitSet,int dim>
std::istream& operator>>(std::istream& A_in,EuclBitSetT<P_BitSet,dim>& A_BmpCubSet){
  SkipCommentsIstream in(A_in);
  if(in.eof()) throw std::runtime_error("cubfile seems to be empty!");
  std::ios::pos_type startOfIn=in.tellg();
  A_BmpCubSet.clear();
  char ch=' ';
  in >> ch;
  in.unget();
  unsigned int actualDim=0;
  if(ch == '{'){  // Set of cubes format
    RepSet<ElementaryCube> eCubeRepSet;
    in >> eCubeRepSet;
    if(dim!=eCubeRepSet.embeddingDimension()) throw EmbDimException("operator>>(istream&,EuclBitSetT<P_BitSet,dim>::importRepSetOfElementaryCube): incorrect embedding dimension");
    EuclBitSetT<P_BitSet,dim> cubSet(eCubeRepSet);
    swap(cubSet,A_BmpCubSet);
  }else if(ch>='0' and ch<='9'){ // numbers only format
    RepSet<ElementaryCube> eCubeRepSet;
    while(true){
      char ch;
      in >> ch;
      if(ch<'0' or ch>'9' or in.eof()) break;
      in.unget();
      char buf[256];
      in.get(buf,256);
      std::string s(buf);
      std::istringstream ins(s);
      std::vector<int> coords;
      while(true){
        char ch;
        ins >> ch;
        if(ch<'0' or ch>'9' or ins.eof()) break;
        ins.unget();
        int c;
        ins >> c;
        coords.push_back(c);
      }
      if(!actualDim) actualDim=coords.size();
      if(actualDim != dim){
          std::ostringstream s;
          s << "Found box of dimension " << actualDim << " different from expected " << dim << " when reading a cubfile!";
          throw EmbDimException(s.str());
      }
      if(actualDim != coords.size()){
          std::ostringstream s;
          s << "Found box of dimension " << coords.size() << " different from expected " << actualDim << " when reading a cubfile!";
          throw EmbDimException(s.str());
      }
      eCubeRepSet.insert(ElementaryCube(&coords[0],actualDim));
    }
    EuclBitSetT<P_BitSet,dim> cubSet(eCubeRepSet);
    swap(cubSet,A_BmpCubSet);
  }else{          // List of cubes format
    int lineCnt=0;
    int declaredDim=0;
    bool determineDimAndBoundingBox=true;
    // We first check if the dimension and bounding box are given in the prefix of the file of the form
    // d\D* \d+           dimension 3
    // b\D* (\d+)+        boundingBox 256 512 100

    std::vector<int> boundingBox,lowerCorner;
    if(ch == 'd'){   // List may be preceded by dimension
      while(ch < '0' or ch > '9') in >> ch;
      in.unget();
      in >> declaredDim;
      if(declaredDim!=dim){
        std::ostringstream s;
        s << "Declared dimension is " << declaredDim << " but must be " << dim << "! \n";
        throw EmbDimException(s.str());
      }else{
        actualDim=declaredDim;
      }
      ++lineCnt;
      in >> ch;
      if(ch == 'b'){   // bounding box is given
        while(ch < '0' or ch > '9') in >> ch;
        in.unget();
        for(unsigned int i=0;i<actualDim;++i){
          int c;
          in >> c;
          boundingBox.push_back(c);
          lowerCorner.push_back(0);
        }
        ++lineCnt;
        determineDimAndBoundingBox=false; // Dimension and bounding box were read successfully
      }else{
        in.unget();
      }
    }
    if(determineDimAndBoundingBox){
      // We read from the beginning and determine the dimension first
      std::vector<int> minCoords,maxCoords;
      ch=' ';
      while(ch!='(' && !in.eof()) in >> ch; // Searching for '('
      in.unget();
      if(in.eof()) throw std::runtime_error("operator>>: No opening ( found when trying to determine the dimension in a list of cubes!");
      in >> ch; // Reading '('
      ++lineCnt;
      while(true){
        int c;
        in >> c;
        in >> ch;
        if(in.eof()) throw std::runtime_error("operator>>: No closing ) found when trying to determine the dimension in a list of cubes!");
        if(ch == ',' || ch == ')'){
          minCoords.push_back(c);
          maxCoords.push_back(c);
        }
        if(ch == ')'){
          break;
        }
      }
      actualDim=minCoords.size();
      if(actualDim != dim){
        std::ostringstream s;
        s << "Found box of dimension " << actualDim << " but " << dim << " expected!";
        throw EmbDimException(s.str());
      }
      // We continue with determining the bounding box
      while(true){
        in >> ch;
        if(in.eof()){
          break;
        }
        if(ch!='('){
          std::ostringstream s;
          s << "Got '" << ch << "' on line " << lineCnt << " and '(' expected when reading a cubfile!";
          throw std::runtime_error(s.str());
        }
        unsigned int i=0;
        ++lineCnt;
        while(true){
          int c;
          in >> c;
          if(c<minCoords[i]) minCoords[i]=c;
          if(c>maxCoords[i]) maxCoords[i]=c;
          in >> ch;
          ++i;
          if(ch==')' && i == actualDim){
            break;
          }else if(ch==')' || i >= actualDim){
            std::ostringstream s;
            s << "Found box of dimension different from " << actualDim << " on line " << lineCnt << " when determining the bounding box of a cubfile!";
            throw EmbDimException(s.str());
          };
          if(ch==',') continue;
          // otherwise the file is corrupt
          std::ostringstream s;
          s << "Got '" << ch << "' on line " << lineCnt << " and ',' or ')' expected when determining the bounding box of a cubfile!";
          throw std::runtime_error(s.str());
        }
      }
      for(unsigned int i=0;i<actualDim;++i){
        boundingBox.push_back(maxCoords[i]-minCoords[i]+1);
        lowerCorner.push_back(minCoords[i]);
      }
      in.clear();
      in.seekg(startOfIn);
      lineCnt=0;
    }
    // replace the provided bitmap with the bitmap with proper size
    {
      EuclBitSetT<P_BitSet,dim> cubSet(&boundingBox[0],true); // true means clear
      swap(A_BmpCubSet,cubSet);
    }

    // Now read the actual data
    int cnt=0;
    int cntMod=100000; // Every cntMod line we will show how many bytes were read
    ch=' ';
    while(ch!='(' && !in.eof()) in >> ch; // Searching for '('
    in.unget();
    while(true){
      ++lineCnt;
      std::vector<int> coords(actualDim);
      in >> ch;
//std::cout << "XGot " << ch << std::endl;
      if(in.eof()){
//std::cout << "XEof found" << std::endl;
        break;
      }
      if(ch!='('){
        std::ostringstream s;
        s << "Got '" << ch << "' on line " << lineCnt << " and '(' expected when reading a cubfile!";
        throw std::runtime_error(s.str());
      }
      unsigned int i=0;
      while(true){
        int c;
        in >> c;
        c-=lowerCorner[i];
        if(c<0 || c>=boundingBox[i]){
          std::ostringstream s;
          s << "operator>>: Coordinate " << c << " on line " << lineCnt << " is out of the provided bounding box!";
          throw std::runtime_error(s.str());
        }
        coords[i]=c;
        in >> ch;
        ++i;
        if(ch==')' && i == actualDim){
          break;
        }else if(ch==')' || i >= actualDim){
          std::ostringstream s;
          s << "Found box of dimension different from " << actualDim << " on line " << lineCnt << " when reading a cubfile!";
//          throw std::runtime_error(s.str());
          throw EmbDimException(s.str());
        };
        if(ch==',') continue;
        // otherwise the file is corrupt
        std::ostringstream s;
        s << "Got '" << ch << "' on line " << lineCnt << " and ',' or ')' expected when reading a cubfile!";
        throw std::runtime_error(s.str());
      }
//      typename  EuclBitSetT<P_BitSet,dim>::BitIterator it(A_BmpCubSet,&coords[0]);
      // changed but not fully tested!! - one bug already removed and now seems to be OK at least for small files
      typename  EuclBitSetT<P_BitSet,dim>::BitCoordIterator it(A_BmpCubSet,&coords[0]);
      it.setBit();
      if(++cnt % cntMod == 0) std::cout << "Read " << cnt/cntMod << " * " << cntMod << " bytes \n";
    }
  }
  return A_in;
}

/************************************************************************************/
#endif


/// @}

