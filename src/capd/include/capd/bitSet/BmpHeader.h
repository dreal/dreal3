/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BmpHeader.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#ifndef _CAPD_BITSET_BMPHEADER_H_
#define _CAPD_BITSET_BMPHEADER_H_

#include <sstream>
#include <stdexcept>
#include "capd/bitSet/EmbDimException.h"

template <typename word, int dim>
struct BmpHeader;

template<>
struct BmpHeader<unsigned long int,2>{
  static const unsigned int standardType='M'*256+'B'; // 19778
  static const unsigned int multidimType='D'*256+'B'; //
  unsigned int type;               // Magic identifier
  unsigned int size;
  unsigned int reserved1;
  unsigned int reserved2;
  unsigned int offset;             // Offset to image data in bytes
  unsigned int ihsize;             // Info header size in bytes
  int width;                       // Width of image
  int height;                      // Height of image
  unsigned int planes;             // Number of colour planes
  unsigned int bits;               // Bits per pixel
  unsigned int compression;        // Compression type
  unsigned int imagesize;          // Image size in bytes
  int xresolution;                 // Pixels per meter in x dir
  int yresolution;                 // Pixels per meter in y dir
  unsigned int ncolours;           // Number of colours
  unsigned int importantcolours;   // Important colours
  unsigned int color0;             // palette code for index 0
  unsigned int color1;             // palette code for index 1

  void read(std::ifstream& file);
  void write(std::ofstream& file);
  void showHeader();
};

template <typename word, int dim>
struct BmpHeader{
  static const unsigned int standardType='M'*256+'B'; // 19778
  static const unsigned int multidimType='D'*256+'B'; //
  static const unsigned int repsetType='R'*256+'B'; //
  unsigned int type;               // Magic identifier
  int dimension;
  int length;
  int actualDimZeroBitWidth;
  int paddedBitWidth[dim];
  void read(std::ifstream& file);
  void write(std::ofstream& file);
  void showHeader();
};


#endif // _CAPD_BITSET_BMPHEADER_H_

/// @}

