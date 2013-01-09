// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// bitcodes.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_BITCODES_HPP_ 
#define _CAPD_CHOM_BITCODES_HPP_ 

#include "capd/chom/chom.hpp"

//-----------------------------------------------------------------------------
// Bitcode  declarations
//-----------------------------------------------------------------------------

/*! \class bitcode
    \brief Base class for blocks and cubes.

    Last modified by BK on 5/8/01.
*/
class bitcode{
 private:
   char* code;
   char  bits;
   void operator=(const bitcode&); // disable assignment operator
   bitcode(const bitcode&);        // disable copy constructor
 public:
   static int counter;
   static int max;
   bitcode(char no_bits) : bits(no_bits)
     {++counter; ++max; if (!bits) code=NULL; else {code=new char[Bytes()]; memset(code,0,Bytes());}}
   ~bitcode()
     {--counter; if (bits) delete code;}
   int Bytes() const
     {if (bits%8) return(bits/8+1); else return(bits/8);}
   int Bits() const
     {return(bits);}
   int Bits(int b)
     {bits=b;return 0;}
   void operator++();           //!< Prefix ++ increments code by 1.
   void operator--();           //!< Prefix -- decrements code by 1.
   void operator++(int);        //!< Postfix ++ shifts code to the right, moving up one tree level.
   void operator--(int);        //!< Postfix -- shifts code to the left, moving down one tree level.
                                // MUST be followed by an prefix increment if low bit is 1.
   int operator[](int n) const
     {return((code[n/8] & (1<<(n%8)))>>(n%8));}         //!< Returns n-th bit, n=0,...,bits-1.
   void operator()(int n, char value=0)
     {if ((*this)[n] != value) code[n/8] ^= 1<<(n%8);}  //!< Set n-th bit to given value.
   void Increment(int k);       //!< Increment kth coordinate where 0<=k<DIM
   void Decrement(int k);       //!< Decrement kth coordinate where 0<=k<DIM
   void SetAs(bitcode* bc)      //!< Resets bits to those in bc.
     {memset(code,0,Bytes()); for(int i=0; i<bc->Bits(); ++i) (*this)(i,(*bc)[i]);} // assumes bits>=bc.Bits()
   void SetAs(const bitcode& bc)//!< Resets bits to those in bc.
     {memset(code,0,Bytes()); for(int i=0; i<bc.Bits(); ++i) (*this)(i,bc[i]);}
   void Coordinates(int* c);    //!< Sets in c the integer coordinates of vertex with this bitcode.
   void Print() const;
   friend bool operator==(const bitcode& ,const bitcode&);
   friend bool operator<(const bitcode&, const bitcode&);
   friend int Ancestor(bitcode*, bitcode*);
};

/*! \fn bool operator==(const bitcode&, const bitcode&)
    \brief Determines equality of bitcodes.

    Last modified by BK on 7/13/00.
*/
bool operator==(const bitcode&, const bitcode&);

/*! \fn bool operator<(const bitcode&, const bitcode&)
    \brief Compares bitcodes using lexicographic order.

    Last modified by BK on 7/13/00.
*/
bool operator<(const bitcode&, const bitcode&);

/*! \fn Flat(const bitcode&, const bitcode&, int dimension);
    \brief Compares bitcodes for equality in the given dimension.

    Last modified by BK on 5/10/01.
*/
bool Flat(const bitcode&, const bitcode&, int dimension);

/*! \fn int Ancestor(bitcode*, bitcode*)
    \brief Compares bitcodes to find number of bits up to ancestor +1.

    Last modified by BK on 7/13/00.
*/
int Ancestor(bitcode*, bitcode*);

// Find vertex with lowest coordinates which is periodically equivalent
// This routine CREATES A NEW BITCODE
int LowestVertex(bitcode&, bitcode**);

#endif // _CAPD_CHOM_BITCODES_HPP_ 

