// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//----------------------------------------------------------------------------------------
// bitcodes.cpp:
//----------------------------------------------------------------------------------------

#include "capd/chom/bitcodes.hpp"

int bitcode::counter=0;
int bitcode::max=0;

// Find vertex with lowest coordinates which is periodically equivalent
// This routine CREATES A NEW BITCODE
int LowestVertex(bitcode& bc, bitcode** nbc)
{
//   bc.Print();

/*
   (*nbc)=new bitcode(bc.Bits());
   int bcc[MAX_CHOM_DIM];
   bc.Coordinates(bcc);
   int maxc=Power2(cube_bits/chomDIM);

   for(int i=1;i<chomDIM;++i)
     {
 if (bcc[i]!=maxc)
   {
      for(int j=0;j<bcc[i];++j)
        {
    (*nbc)->Increment(chomDIM-i-1);
        }
   }
     }

   if ((bcc[0]!=maxc)||(periodic==1)) // periodic==1 means chomDIM-1 coordinate is NOT periodic
     {
 for(int j=0;j<bcc[0];++j)
   {
      (*nbc)->Increment(chomDIM-1);
   }
     }
*/

   (*nbc)=new bitcode(bc.Bits());
   int bcc[MAX_CHOM_DIM];
   bc.Coordinates(bcc);
   int maxc=Power2(cube_bits/chomDIM);

   for(int i=0;i<chomDIM-1;++i)
     {
 if (bcc[i]!=maxc)
   {
      for(int j=0;j<bcc[i];++j)
        {
    (*nbc)->Increment(chomDIM-i-1);
        }
   }
     }

   if ((bcc[chomDIM-1]!=maxc)||(periodic==1)) // periodic==1 means chomDIM-1 coordinate is NOT periodic
     {
 for(int j=0;j<bcc[chomDIM-1];++j)
   {
      (*nbc)->Increment(0);
   }
     }

   return 0; // Added by MM to get rid of compilation warnings
/*
   int nbcc[MAX_CHOM_DIM];
   (*nbc)->Coordinates(nbcc);
   cout << endl << "Original: " << bcc[0] << "," << bcc[1] << " , " << bcc[2] << "  :  " << bc[0] << "," << bc[1] << "  :  " << maxc <<endl;
   cout << "New     : " << nbcc[0] << "," << nbcc[1] << " , " << nbcc[2] << "  :  " << (*(*nbc))[0] << "," << (*(*nbc))[1] << endl << endl;
*/
}

bool Flat(const bitcode& bc1, const bitcode& bc2, int d)
{
   for(int i=0; i<bc1.Bits()/chomDIM; ++i)
     if (bc1[d+i*chomDIM]!=bc2[d+i*chomDIM])
       return(false);
   return(true);
}

int Ancestor(bitcode *bc1, bitcode* bc2)
{
   int i;
   for(i=0; i<cube_bits; ++i)
     {
 if ((*bc1)[bc1->bits-i-1]!=(*bc2)[bc2->bits-i-1])
   break;
     }
   return(cube_bits-i-1);
}

void bitcode::Coordinates(int* min)
{
   for(int i=0; i<chomDIM; ++i)
     min[i]=0;

   for(int k=0; k<chomDIM; ++k)
     {
 for(int i=0; i<bits/chomDIM; i++)
   if ((*this)[k+i*chomDIM]==1)
     min[chomDIM-1-k]+=Power2(i);
     }
   return;
}

void bitcode::Increment(int k)
{
   int i=k;
   while(i<bits)
     {
        if ((*this)[i]==0)
          {
      (*this)(i,1);
      break;
   }
 else
   (*this)(i,0);
 i+=chomDIM;
     }
   return;
}

void bitcode::Decrement(int k)
{
   int i=k;
   while(i<bits)
     {
        if ((*this)[i]==1)
          {
      (*this)(i,0);
      break;
   }
 else
   (*this)(i,1);
 i+=chomDIM;
     }
   return;
}

bool operator==(const bitcode& bc1, const bitcode& bc2)
{
   if (bc1.bits!=bc2.bits)
     return(0);
   if (!bc1.Bits())
     return(1);
   return(memcmp(bc1.code,bc2.code,bc1.Bytes())==0);
}

bool operator<(const bitcode& bc1, const bitcode& bc2)
{
   if (bc1.bits>bc2.bits)
     return(0);
   if (!bc1.bits)
     return(1);
   for(int i=bc1.bits-1; i>-1; i--)
     {
 if (bc1[i]<bc2[i])
   return(1);
        if (bc1[i]>bc2[i])
          return(0);
     }
   return(0);
}

void bitcode::Print() const
{
   if (!bits)
     {
        cout << "Empty bitcode.\n";
 return;
     }

   // int i; // commented out by MM to get rid of compilation warnings
   for (int i=8*Bytes()-1; i>-1; --i)
     {
 cout << (*this)[i];
 if (i%8==0)
   cout << " ";
     }
   cout << " - " << Bits() << " bits\n";
   return;
}

void bitcode::operator++()
{
   int count=0;

   for(count=0; count<bits; count++)
     {
 if ((*this)[count]==0)                  // count number of initial 1's
   break;
     }

   if(count==bits)                              // all 1's
     {
 ++bits;
 if (bits%8==1)
   {
      if (bits!=1)
        delete code;
             code=new char[Bytes()];            // reallocate with one more byte
   }
 memset(code,0,Bytes());
 (*this)(bits-1,1);
 return;
     }

   for(int j=0; j<count; ++j)
     (*this)(j,0);

   (*this)(count,1);
   return;
}

void bitcode::operator--()
{
   int count=0;

   for(count=0; count<bits; ++count)
     {
        if ((*this)[count]==1)           // count number of initial 0's
   break;
     }

   if(count==bits)                       // all 0's can't be decremented
     return;

   for(int k=0; k<count; ++k)
     {
 (*this)(k,1);
     }
   (*this)(count,0);                     // does not change number of bits
   return;
}

void bitcode::operator++(int x)
{
   if (!bits)
     return;

   char *endbit;
   int j;

   endbit=new char[Bytes()];
   memset(endbit,0,Bytes());

   for (j=0; j < Bytes(); ++j)
     {
 endbit[j] = ((code[j] & 0x01)<<7);        // first preserve the low bit from each byte
    code[j] >>= 1;                            // right-shift each byte
 code[j] &= (~(1<<7));                     // set high bit=0
     }

   for (j=0; j < Bytes()-1; ++j)
     code[j] |= endbit[j+1];                      // set high bit

   delete endbit;

   --bits;                                        // decrement the number of bits

   if (!(bits%8))                                 // need one less byte
     {
 if (bits==0)
 {
 // commented-out by Pawel Pilarczyk after a note from Tomek Kapela:
 // if the number of "bits" is zero then "Bytes()" is necessarily
 // also zero, so there is nothing that must be zero'ed in the memory
 //  memset(code,0,Bytes());
 }
 else
   {
      char* oldcode=code;
      code=new char[Bytes()];              // reallocate with one less byte
      memset(code,0,Bytes());
             for (j=0; j < Bytes(); ++j)
        code[j]=oldcode[j];
      delete oldcode;
   }
     }

   return;
}

void bitcode::operator--(int x)
{
   if (!bits)
     {
 bits=1;
 code=(char*)malloc(1);
 code[0]=0;
 return;
     }

   char *endbit;
   int j;

   endbit=new char[Bytes()];
   memset(endbit,0,Bytes());

   for (j=0; j < Bytes(); ++j)
     {
 endbit[j] = ((code[j] & (0x01<<7))>>7);   // first preserve the high bit from each byte
 code[j] <<= 1;                            // left-shift each byte
     }

   for (j=0; j < Bytes()-1; ++j)
     if ((code[j+1] & (0x01)) != endbit[j])       // if low bit is incorrect
       code[j+1] ^= (0x01);                       // change to correct value

   if ((code[0] & (0x01)) != 0)                   // if LOW bit is incorrect
     code[0] ^= (0x01);                           // change to correct value

   ++bits;                                        // increment number of bits

   if (bits%8==1)                                 // need one more byte
     {
 char* oldcode=code;
 code=new char[Bytes()];                   // reallocate with one more byte
 memset(code,0,Bytes());
        for (j=0; j < Bytes()-1; ++j)
   code[j]=oldcode[j];
 if ((code[Bytes()-1] & (0x01)) != endbit[Bytes()-2])  // if low bit is incorrect
          code[Bytes()-1] ^= (0x01);                          // change to correct value
 delete oldcode;
     }

   delete endbit;
   return;
}


