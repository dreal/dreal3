/****                              ****/
/**** (c) Marian Mrozek 2010       ****/
// This version intended for reading into SComplex

#if !defined(_READCUBICALSET_HPP_)
#define _READCUBICALSET_HPP_

#include <fstream>
#include <sstream>
#include <string>
#include <exception>
#include <stdexcept>
#include <vector>
#include <climits>

#include "capd/auxil/stringOstream.h"
#include "capd/auxil/skipCommentsIstream.h"
#include "capd/bitSet/EmbDimException.h"
#include "capd/homologicalAlgebra/CubSetBuilder.h"
#include "capd/bitSet/BmpHeader.hpp"

typedef std::vector<int> intVect;
typedef unsigned int uint;

/* ------------------------  ------------------------ */
// auxiliary
inline char readUpto(SkipCommentsIstream& in,const char* chars){
  char ch,chs;
  const char* chPt;
  while(true){
    in >> ch;
    if(in.eof()) return 0;
    chPt=chars;
    while( (chs=*chPt++) != 0){
      if(ch==chs) return chs;
    }
  }
}


static bool openCells=false;

/* ------------------------  ------------------------ */
// used in set of cubes format
inline int unbracketCubeCoord(SkipCommentsIstream& inp){
  char ch;
  int coord,coord2;
  inp >> ch;
  if(ch!='[' && ch!='(') throw std::ios_base::failure("unbracketCubeCoord: Failed to read \'[\'");
//std::cout << "Op =" << ch << "=\n";
  if(ch=='(')  openCells=true;
  inp >> coord;
  inp >> ch;
  if(ch!=',' && ch!=']' && ch!=')') throw std::ios_base::failure("unbracketCubeCoord: Failed to read \',\' or \']\'");
  if(ch==','){
    inp >> coord2;
    if(!(coord2==coord || coord2==coord+1)) throw std::ios_base::failure("unbracketCubeCoord: Non elementary interval found");
    inp >> ch;
  }else{
    coord2=coord;
  }
  if(ch!=']' && ch!=')') throw std::ios_base::failure("unbracketCubeCoord: Failed to read \']\'");
  if(inp.eof()) throw std::ios_base::failure("unbracketCubeCoord: EOF encountered when reading cube coord");
  return coord+coord2;  // ==2*coord+(coord2-coord);
}

/* ------------------------  ------------------------ */
// used in set of cubes format
inline void unbracketCube(SkipCommentsIstream& inp,intVect& v){
  do{
    int c;
    c=unbracketCubeCoord(inp);
    v.push_back(c);
    char ch(' ');
    inp >> ch;
    if(inp.eof()) break;
    if(ch!='x'){
      inp.unget();
      break;
    }
  }while(true);
}

/* ------------------------  ------------------------ */
// used in numbers only format
inline void getCubeCoords(SkipCommentsIstream& inp,intVect& v){
  std::string s;
  getline(inp,s);
  std::istringstream ins(s);
  while(true){
    char ch;
    ins >> ch;
    if(ch<'0' or ch>'9' or ins.eof()) break;
    ins.unget();
    int c;
    ins >> c;
    v.push_back(c);
  }
}

/* ------------------------  ------------------------ */
// used in list of full cubes format
inline bool unparenCube(SkipCommentsIstream& in,int* v,unsigned int embDim,int lineCnt){
  unsigned int i=0;
  if(!readUpto(in,"(")) return false;
  while(true){
    int c;
    char ch;
    in >> c;
/*
    if(!determineDimAndBoundingBox && (c<0 || c>=boundingBox[i])){
      std::ostringstream s;
      s << "unparenCube:  Coordinate " << c << " on line " << lineCnt << " is out of the provided bounding box!";
      throw std::runtime_error(s.str());
    }
*/
    v[i]=c;
    in >> ch;
    ++i;
    if(ch==')' && i == embDim){
      break;
    }else if(ch==')' || i >= embDim){
      std::ostringstream s;
      s << "unparenCube: Found box of dimension different from " << embDim << " on line " << lineCnt << " when reading a cubfile!";
      throw EmbDimException(s.str());
    };
    if(ch==',') continue;
    // otherwise the file is corrupt
    std::ostringstream s;
    s << "unparenCube: Got '" << ch << "' on line " << lineCnt << " and ',' or ')' expected when reading a cubfile!";
    throw std::runtime_error(s.str());
  }
  return true;
}

/* ------------------------  ------------------------ */
// used in list of full cubes format
inline int determineDim(SkipCommentsIstream& in){
  char ch=' ';
  readUpto(in,"(");
  int cnt=0;
  while(true){
    int c;
    in >> c;
    in >> ch;
    ++cnt;
    if(in.eof()) throw std::runtime_error("determineDim: EOF reached when searching for ')'!");
    if(ch == ')'){
      break;
    }
  }
  return cnt;
}


/* ------------------------  ------------------------ */
inline void registerCell(int* coords,int* cmin,int* cmax,uint n){
  for(unsigned int i=0;i<n;++i){
    if(coords[i] > cmax[i]) cmax[i]=coords[i];
    if(coords[i] < cmin[i]) cmin[i]=coords[i];
  }
}

/* ------------------------  ------------------------ */
template <class P_CubSetBuilder>
inline void processCell(bool buildingPass,P_CubSetBuilder& csb,intVect& coords,intVect& cmin,intVect& cmax){
  if(buildingPass){
    csb.addCell(&coords[0]);
  }else{
    registerCell(&coords[0],&cmin[0],&cmax[0],coords.size());
  }
}

/* ------------------------  ------------------------ */
template <class P_CubSetBuilder>
inline void setupDimAndType(P_CubSetBuilder& csb,int dim,FileType fileType){
  csb.setDim(dim);
  csb.setFileType(fileType);
}

/* ------------------------  ------------------------ */
template <class P_CubSetBuilder>
inline void setupBounds(P_CubSetBuilder& csb,int dim,intVect& cmin,intVect& cmax){
  if(cmin.size()==0){
    cmin.reserve(dim);
    cmax.reserve(dim);
    for(int i=0;i<dim;++i){
      cmin.push_back(INT_MAX);
      cmax.push_back(INT_MIN);
    }
  }
}

/* ------------------------  ------------------------ */
template <class P_CubSetBuilder>
inline void setupDimAndBounds(P_CubSetBuilder& csb,int dim,intVect& cmin,intVect& cmax,FileType fileType=unrecognized){
  setupDimAndType(csb,dim,fileType);
  setupBounds(csb,dim,cmin,cmax);
}

//enum FileType{unrecognized,plain,setOfFullCubes,setOfCubes,binFul,binCel};

/* ------------------------  ------------------------ */
template <class P_CubSetBuilder>
void readCubicalSet(std::ifstream& A_in,P_CubSetBuilder& A_csb,bool dimOnly=false){
//void readCubicalSet(std::istream& A_in,P_CubSetBuilder& A_csb,bool dimOnly=false){
  bool buildingPass=false;
  intVect cmin,cmax;

  if(!A_in.good()){
    std::string s;
    s << "Unable to open file  for reading \n";
    throw std::runtime_error(s.c_str());
  }


  SkipCommentsIstream in(A_in);
  if(in.eof()) throw std::runtime_error("readCubicalSet: cubfile is empty!");
  std::ios::pos_type startOfIn=in.tellg();


  FileType fileType=unrecognized;

  // First probing for file type
  char ch;
  char c1=A_in.get();
  char c2=A_in.get();
  in.clear();
  in.seekg(startOfIn);

  if(c1=='B' && (c2=='M' || c2=='D' || c2=='R')){
    fileType=bin;
    if(c2=='R'){
      A_csb.setFullCubes(false);
      std::cout << "Assuming cubical set in binary format" << std::endl;
    }else{
      A_csb.setFullCubes(true);
      std::cout << "Assuming full cubical set in binary format" << std::endl;
    }
  }else{
    in >> ch;
    in.unget();
    if(ch>='0' and ch<='9'){
      fileType=plain;
      A_csb.setFullCubes(true);
      if(!dimOnly) std::cout << "Assuming plain numbers format / 1 2 3 ... /" << std::endl;
    }else{
      ch=readUpto(in,"[{(");
      c2=readUpto(in,"x\0x0D\0x0A");
      if(ch == 0){
        throw "readCubicalSet: Failed to recognize input data format!";
      }else if (ch == '(' && c2!='x'){
        fileType=setOfFullCubes;
        A_csb.setFullCubes(true);
        if(!dimOnly) std::cout << "Assuming set of full cubes format /(1,2,3 ... )/" << std::endl;
      }else{
        fileType=setOfCubes;
        A_csb.setFullCubes(false);
        if(!dimOnly) std::cout << "Assuming set of elementary cubes format /[1,2]x[3]x.../" << std::endl;
      }
    }
  }



  openCells=false; // we preassume that no open cells will be provided
  // Two passes if bounding box is needed, otherwise one pass:
  // pass 0 - determining bounding box
  // pass 1 - building pass
  for(int pass=0;pass<2;++pass){
    if(!A_csb.isBoundingBoxNeeded()) pass=1; // This is a building pass if no bounding box is needed
//std::cout << "pass=" << pass  << std::endl;
    buildingPass=(pass==1); //
    in.clear();
    in.seekg(startOfIn);

    unsigned int embDim=0;
    char ch=' ';
    in >> ch;
    in.unget();

    switch(fileType){
    // Binary formats
      case bin:{
        if(c2=='M'){
          embDim=2;
        }else{
          get2ByteUInt(A_in);
          embDim=get4ByteUInt(A_in);
        }
        if(dimOnly){
          setupDimAndType(A_csb,embDim,fileType);
          goto finish;
        }else{
          throw "readCubicalSet: only reading headers supported so far on binary files";
        }
      }

      break;
    // Set of cubes format
      case setOfCubes:{
        intVect coords;
        ch=readUpto(in,"[(");
        in.unget();
        unbracketCube(in,coords);
        embDim=coords.size();
//std::cout << "embDim=" << embDim << std::endl;

//        A_csb.setFullCubes(false);
        setupDimAndBounds(A_csb,embDim,cmin,cmax,fileType);
        if(dimOnly) goto finish;
        processCell(buildingPass,A_csb,coords,cmin,cmax);
        do{
          ch=readUpto(in,"[(");
          in.unget();
          if(ch==0) break;
          coords.clear();
          coords.reserve(embDim);
          unbracketCube(in,coords);
          if(embDim != coords.size()){
            throw EmbDimException("readCubicalSet: inconsistent embedding dimension found on input!");
          }
          processCell(buildingPass,A_csb,coords,cmin,cmax);
        }while(true);
      }
      break;

      // Numbers only format
      case plain:{
//        A_csb.setFullCubes(true);
        intVect coords;
        getCubeCoords(in,coords);
        embDim=coords.size();
        setupDimAndBounds(A_csb,embDim,cmin,cmax,fileType);
        if(dimOnly) goto finish;
        processCell(buildingPass,A_csb,coords,cmin,cmax);
        while(true){
          char ch=' ';
          in >> ch;
          if(in.eof() or ch<'0' or ch>'9') break;
          in.unget();
          coords.clear();
          coords.reserve(embDim);
          getCubeCoords(in,coords);
          if(embDim != coords.size()){
            throw EmbDimException("readCubicalSet: inconsistent embedding dimension found on input!");
          }
          processCell(buildingPass,A_csb,coords,cmin,cmax);
        }
      }
      break;

      // List of cubes format
      case setOfFullCubes:{
//        A_csb.setFullCubes(true);
        int lineCnt=0;
        int declaredDim=0;
        bool determineDimAndBoundingBox=true;
        // We first check if the dimension and bounding box are given in the prefix of the file of the form
        // d\D* \d+           dimension 3
        // b\D* (\d+)+        boundingBox 256 512 100

        intVect boundingBox,lowerCorner;
        if(ch == 'd'){   // List may be preceded by dimension
          while(ch < '0' or ch > '9') in >> ch;
          in.unget();
          in >> declaredDim;
          embDim=declaredDim;
          setupDimAndBounds(A_csb,embDim,cmin,cmax,fileType);
          if(dimOnly) goto finish;
          ++lineCnt;
          in >> ch;
          if(ch == 'b'){   // bounding box is given
            while(ch < '0' or ch > '9') in >> ch;
            in.unget();
            for(unsigned int i=0;i<embDim;++i){
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
        if(!embDim){  // if embDim was not determined yet
          embDim=determineDim(in);

          setupDimAndBounds(A_csb,embDim,cmin,cmax,fileType);
          if(dimOnly) goto finish;
          in.clear();
          in.seekg(startOfIn);
          lineCnt=0;
        }

        // Now read the actual data
        int cnt=0;
        int cntMod=1000000; // Every cntMod line we will show how many bytes were read
        ch=' ';
        while(ch!='(' && !in.eof()) in >> ch; // Searching for '('
        in.unget();
        while(true){
          ++lineCnt;
          intVect coords(embDim);
          if(!unparenCube(in,&coords[0],embDim,lineCnt)) break;
          processCell(buildingPass,A_csb,coords,cmin,cmax);
          if(++cnt % cntMod == 0) std::cout << "Read " << cnt/cntMod << " * " << cntMod << " cubes \n";
        }
      }
      break;
      default: throw "readCubicalSet: Failed to recognize input data format!!!";
    }
    if(A_csb.isBoundingBoxNeeded() && pass==0){
      A_csb.setBoundingBox(&cmin[0],&cmax[0]);
    }
  }//for(int pass
  A_csb.setOpenCells(openCells);
  A_csb.finalize();
finish:
  in.clear();
  in.seekg(startOfIn);
}


/* ------------------------  ------------------------ */
template <class P_CubSetBuilder>
void readCubicalMap(std::istream& A_in,P_CubSetBuilder& A_csb){
  bool buildingPass=false;
  intVect cmin,cmax;

  if(!A_in.good()){
    std::string s;
    s << "Unable to open file  for reading \n";
    throw std::runtime_error(s.c_str());
  }

  SkipCommentsIstream in(A_in);
  if(in.eof()) throw std::runtime_error("readCubicalMap: cubfile is empty!");
  std::ios::pos_type startOfIn=in.tellg();

  // Two passes if bounding box is needed, otherwise one pass:
  // pass 0 - determining bounding box
  // pass 1 - building pass
  for(int pass=0;pass<2;++pass){
    if(!A_csb.isBoundingBoxNeeded()) pass=1; // This is a building pass if no bounding box is needed
    buildingPass=(pass==1); //
    in.clear();
    in.seekg(startOfIn);

    FileType fileType=unrecognized;

    unsigned int embXDim=0,embYDim,embXYDim;
    char ch=' ';
    in >> ch;
    in.unget();

    // Set of cubes format
    if(ch == '{'){
      throw  std::runtime_error("readCubicalMap: set of cubes format not supported for maps!");
    // List of cubes format
    }else if(ch>='0' and ch<='9'){
      throw  std::runtime_error("readCubicalMap: numbers only format not supported for maps!");
    }else{
      fileType=mapOfCubes;
      A_csb.setFullCubes(true);
      int lineCnt=0;

      intVect boundingBox,lowerCorner;
      // We read from the beginning, determine the dimensions and set up the tables
      embXDim=determineDim(in);
      if(!readUpto(in,"-")) throw std::runtime_error("readCubicalMap: EOF reached when searching for '-'!");
      if(!readUpto(in,">")) throw std::runtime_error("readCubicalMap: EOF reached when searching for '>'!");
      embYDim=determineDim(in);
      embXYDim=embXDim+embYDim;

      setupDimAndBounds(A_csb,embXYDim,cmin,cmax,fileType);
      A_csb.setDomDim(embXDim);
      A_csb.setRngDim(embYDim);

      in.clear();
      in.seekg(startOfIn);
      lineCnt=0;

/*    // For XY order in graph - keep it just in case  - needs changes in 2 other places
      int domIndex0=0;
      int rngIndex0=embXDim;
*/
      // For YX order in graph - more efficient (clearing hypeplanes goes through words, not bits)
      int domIndex0=embYDim;
      int rngIndex0=0;

      // Now read the actual data
      int cnt=0;
      int cntMod=1000000; // Every cntMod line we will show how many bytes were read
      ch=' ';
      while(ch!='(' && !in.eof()) in >> ch; // Searching for '('
      in.unget();
      while(true){
        ++lineCnt;
        intVect coords(embXYDim);
        if(!unparenCube(in,&coords[domIndex0],embXDim,lineCnt)) break;
        if(buildingPass){
          A_csb.addDomCell(&coords[domIndex0]);
        }else{
          registerCell(&coords[domIndex0],&cmin[domIndex0],&cmax[domIndex0],embXDim);
        }
        if(!readUpto(in,"-")) throw std::runtime_error("readCubicalMap: EOF reached when searching for '-'!");
        if(!readUpto(in,">")) throw std::runtime_error("readCubicalMap: EOF reached when searching for '>'!");
        if(!readUpto(in,"{")) throw std::runtime_error("readCubicalMap: EOF reached when searching for '{'!");

        while(true){
          ch=readUpto(in,"(}");
          if(!ch) throw std::runtime_error("readCubicalMap: ')' or '}' expected, premature end of file reached");
          if(ch=='}') break;
          in.unget();
          unparenCube(in,&coords[rngIndex0],embYDim,lineCnt);
          if(buildingPass){
            A_csb.addRngCell(&coords[rngIndex0]);
            A_csb.addCell(&coords[0]);
          }else{
            registerCell(&coords[rngIndex0],&cmin[rngIndex0],&cmax[rngIndex0],embYDim);
          }
        }


        if(++cnt % cntMod == 0) std::cout << "Read " << cnt/cntMod << " * " << cntMod << " cubes \n";
      }
    }
    if(A_csb.isBoundingBoxNeeded() && pass==0){
      A_csb.setBoundingBox(&cmin[0],&cmax[0]);
    }
  }//for(int pass
  A_csb.finalize();
  in.clear();
  in.seekg(startOfIn);
}


#endif // _READCUBICALSET_HPP_
