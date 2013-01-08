// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
// Modified by Marcio Gameiro - 04/28/2005
//-----------------------------------------------------------------------------
// chom_lu.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_CHOM_LU_HPP_ 
#define _CAPD_CHOM_CHOM_LU_HPP_ 

#include "capd/chom/chom.hpp"
#include "capd/chom/block.hpp"

// BIT-ARRAY MACRO HACK
#define CHARSIZE 8
#define MASK(y) (1<<(y)%CHARSIZE)
#define BITSLOT(y) ((y)/CHARSIZE)
#define SET(x,y) ((x)[BITSLOT(y)] |= MASK(y))
#define CLEAR(x,y) ((x)[BITSLOT(y)] &= ~MASK(y))
#define TEST(x,y) ((x)[BITSLOT(y)] & MASK(y))
#define NUMSLOTS(n) (((n)+CHARSIZE-1)/CHARSIZE)

// indexed bit-access attempt:
# define _MX_ xmax
# define _MY_ ymax
# define _MZ_ zmax
# define INDEX(x,y,z) ((x)+((y)*_MX_)+((z)*(_MX_*_MY_)))

//-----------------------------------------------------------------------------
// NAMING CONVENTIONS:
//   #define macros: all caps and underscore _ between words
//   Types and variables: no caps and underscore _ between words
//   Functions: Capitalize first letter of each word and no underscores
//-----------------------------------------------------------------------------

using namespace std;

extern int periodic; // 0=off, 1=first DIM-1 variables, 2=all DIM variables
extern int cube_bits;
extern int gen_flag[MAX_CHOM_DIM+1];
extern int Power2(int);
extern int GEN_TOL;
extern int SUBDIVISIONS;

typedef unsigned long ulong;

extern ulong bstrtoul (string bs); // convert binary string to ulong
extern void reduce(char* cubits, ulong xmax, ulong ymax, ulong zmax);
extern int Power2(int exponent);
extern void PrepRead(ifstream* in);
extern block* Read(complex* c, bitcode& bc);
extern void out_of_store();
extern void compute_homology(char* cubits, ulong* max_size, int Betti[]);
extern void compute_homology(char* cubits, ulong xmax, ulong ymax, ulong zmax, int Betti[]);

#endif // _CAPD_CHOM_CHOM_LU_HPP_ 
