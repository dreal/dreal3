// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// cell.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_CELL_HPP_ 
#define _CAPD_CHOM_CELL_HPP_ 

#include "capd/chom/chom.hpp"

//-----------------------------------------------------------------------------
// Cell declarations
//-----------------------------------------------------------------------------

/*! \class cell
    \brief Base class for vertex, edge, and ncell.

    All cells have a dimension and an interior flag.
    If the cell is interior to the cube boundaries of the current level,
    then interior\f$=1\f$, and interior\f$=0\f$ otherwise.
    Initially, all cells have interior\f$=0\f$.
    Last modified by BK on 6/25/00.
*/

class cell{
 protected:
   char interior;
   char dim;
   char sflag;
   char misc_flag;
 public:
   cell(char d)
     :interior(0), dim(d), sflag(0), misc_flag(0) {}
   ~cell() {}
   void Save()
     {sflag=1;}                      //!< Flag this cell to be saved for generator info.
   bool NoSave() const
     {return(!(sflag));}             //!< Return true if cell can be deleted after simplification.
   char Interior() const
     {return interior;}              //!< Return interior flag.
   char Dim() const
     {return dim;}                   //!< Return dimension.
   void MarkInterior()
     {interior=1;}                   //!< Each cell eventually becomes interior but not vice-versa.
};

#endif // _CAPD_CHOM_CELL_HPP_ 

