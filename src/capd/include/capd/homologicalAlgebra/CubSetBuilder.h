/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubSetBuilder.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#if !defined(_CUBSETBUILDER_H_)
#define _CUBSETBUILDER_H_

//enum FileType{unrecognized,plain,setOfFullCubes,setOfCubes,mapOfCubes,binFul,binCel};
enum FileType{unrecognized,plain,setOfFullCubes,setOfCubes,mapOfCubes,bin};

/* ------------------------  ------------------------ */

class CubSetBuilder{
  public:
    CubSetBuilder():
      fullCubes(true),
      openCells(false),
      embDim(0)
    {}

    bool isBoundingBoxNeeded(){
      return true;
    }

    void setFullCubes(bool b){
      // If b==true, the set read contains only full cubes
      fullCubes=b;
    }
    void setOpenCells(bool b){
      // If b==true, the set read contains only full cubes
      openCells=b;
    }
    bool onlyFullCubes(){
      return fullCubes;
    }
    void setDim(int A_embDim){
      // provides embedding dimension
      embDim=A_embDim;
    }
    void setFileType(FileType A_fileType){
      // provides embedding dimension
      fileType=A_fileType;
    }
    int getDim(){
      return embDim;
    }
    FileType getFileType(){
      return fileType;
    }
    void setBoundingBox(int A_cmin[],int A_cmax[]){
      // provides boundingBox
    }
    void addCell(int coords[]){
      // Provides  n coordinates of a cube read.

    }
    void finalize(){
    }



  protected:
    bool fullCubes,openCells;
    int embDim;
    FileType fileType;
};

#endif //_CUBSETBUILDER_H_
