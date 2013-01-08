/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file acyclicConfigs.hpp
///
/// @author Marian Mrozek, Pawel Pilarczyk
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_ACYCLICCONFIGS_HPP)
#define _ACYCLICCONFIGS_HPP

#include <iostream>
#include <fstream>
#include <stdexcept>
#include <cstring>
#include <cstdlib>
#include "capd/homologicalAlgebra/acyclicConfigs.h"
#include "capd/bzip2/bzlib.h"
#include "capd/chom/acyclcfg.h"

// This table stores the acyclicity information concerning all the neighborhood configurations in dim 3
// Bit set to 1 means the configuraiton is acyclic
// The contents of this very large table must be either read from an external file in the current directory for every
// call of teh executable or the executable must be preprocessed with setAcyclicConfigsD3
// to import the table directly into the executable
//unsigned char acyclicConfigsD3[acyclicConfigsSize]=ACYCLIC_CONFIGS_D3MARKER;

/// The acyclic configurations table compressed with bzip2.
extern unsigned char bzip2acyclicConfigsD3 [];
extern unsigned int bzip2acyclicConfigsD3size;

/// Uncompressed table (8 MB) of 3D acyclic neighborhood configurations.
unsigned char *acyclicConfigsD3 = 0;

/// Creates the table of 3D acyclic configurations if necessary.
/// The support for bzipped configurations added by Pawel Pilarczyk.
void readAcyclicConfigs(){
  if(acyclicConfigsD3){
    return;
  }else{
    acyclicConfigsD3 = new unsigned char [acyclicConfigsSize];
/*
    // read the configurations from an external file
    std::ifstream in;
    in. open ("acyclicConfigsD3", std::ios::in | std::ios::binary);
    in. read (reinterpret_cast<char *> (acyclicConfigsD3), acyclicConfigsSize);
    in. close ();
*/
/*
    // compress the configurations to a memory buffer
    char bzipped [256 * 1024];
    unsigned int packlen = 256 * 1024;
    std::cout << "Compressing... " << std::flush;
    capd::bzip2::BZ2_bzBuffToBuffCompress (bzipped, &packlen,
      (char *)acyclicConfigsD3, acyclicConfigsSize, 9, 0, 0);
    std::cout << "Buffer len: " << packlen << "\n";
*/
/*
    // save the compressed buffer to a file
    std::ofstream bzout;
    bzout. open ("acyclicConfigsD3.bz2", std::ios::out | std::ios::binary);
    bzout. write (bzipped, packlen);
    bzout. close ();
*/
    // decompress the configurations table
//    std::cout << "Decompressing... " << flush;
    unsigned int destlen = acyclicConfigsSize;
    capd::bzip2::BZ2_bzBuffToBuffDecompress
      (reinterpret_cast<char *> (acyclicConfigsD3), &destlen,
      reinterpret_cast<char *> (bzip2acyclicConfigsD3),
      bzip2acyclicConfigsD3size, 0, 0);
//    std::cout << "Done.\n";
/*
    // save the decompressed buffer to a file
    std::ofstream out;
    out. open ("acyclicConfigsD3.bin", std::ios::out | std::ios::binary);
    out. write ((const char *) acyclicConfigsD3, acyclicConfigsSize);
    out. close ();
*/
  }
}

// A previous version of the function: Reading the table from a file.
#define ACYCLIC_CONFIGS_D3MARKER "ChomP_acyclicConfigsD3"
void readAcyclicConfigs_previous(){
  // To avoid repeated loads of the acyclicConfigsD3 table,
  // the information if the table is already read is kept here
  static int acyclicConfigsRead=0;
  if(acyclicConfigsRead){
    return;
  }else{
    if(0==strcmp((char*)acyclicConfigsD3,ACYCLIC_CONFIGS_D3MARKER)){ // when 0 returned, texts are equal!
      std::ifstream t("acyclicConfigsD3");
      if(!t.good()){
        std::cout << "Failed to read acyclicConfigsD3.\nMake sure the acyclicConfigsD3 file is present in the current directory\n";
        exit(1);
      }
      t.read(reinterpret_cast<char*>(&acyclicConfigsD3[0]),acyclicConfigsSize);
//      fcout << "Read " << acyclicConfigsSize << " bytes from lookup table\n";
      t.close();
    }else{
//      fcout << "Found embedded lookup table for dim=3\n";
    }
    acyclicConfigsRead=1;
  }
}
#endif //_ACYCLICCONFIGS_HPP

/// @}

