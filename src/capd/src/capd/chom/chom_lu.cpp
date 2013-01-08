// Copyright (C) 2004 by William D Kalies. All rights reserved.
// Lookup table reduction by Vidit Nanda using lookup table by Andrej Szymczak
//
// Modified by Marcio Gameiro - 04/28/2005
//-----------------------------------------------------------------------------
// chom_lu.cc:
//-----------------------------------------------------------------------------

#include "capd/chom/chom_lu.hpp"
#include "capd/chom/chom.hpp"
#include "capd/chom/list.hpp"
#include "capd/chom/bitcodes.hpp"
#include "capd/chom/cell.hpp"
#include "capd/chom/edge.hpp"
#include "capd/chom/vertex.hpp"
#include "capd/chom/ncell.hpp"
#include "capd/chom/block.hpp"
#include "capd/chom/complex.hpp"

//#define PRINT_SIZE

int gen_flag[MAX_CHOM_DIM+1];
int cube_bits=0;
int top_leaf=0;
int GEN_TOL=0;
int periodic=0;

const int LBS = 60;                     // line buffer size
const int LS = 8*1024*1024;             // LUT size
const bool DEBUG = false;
int SUBDIVISIONS=0;

// convert binary string to ulong
ulong bstrtoul (string bs)
{
  char* cptr = (char*)(bs.c_str());
  ulong i, j = 0;
  while (cptr && *cptr && strchr("01", *cptr))
    {
      i = *cptr++ - '0';
      j <<= 1;
      j |= (i & 0x01);
    }
  return(j);
}

void reduce(char* cubits, ulong xmax, ulong ymax, ulong zmax)
{
 // read acyclic configs [this code added by Pawel Pilarczyk]
 void readAcyclicConfigs ();
 readAcyclicConfigs ();
 // [end of code added by Pawel Pilarczyk]

  // cout << "Reading look up table..." << endl;

// OBTAIN LUT INFORMATION
//  ifstream Lfile("lutable");       // open LUT file
// [the above line commented-out by Pawel Pilarczyk]

/*
  if (!Lfile.good())
    {
      cout<<"Unable to access the LUT file, lutable"<<endl ;
      exit(0);
    }

  unsigned char* Lbuf = new unsigned char[LS];
  Lfile.read((char*)Lbuf, LS);
  Lfile.close();
*/
// The above code commented out by Marian Mrozek:
// - in this version acyclicConfigsD3, a common lookup table for all engines is used
  extern unsigned char *acyclicConfigsD3;
  const unsigned char* const Lbuf = acyclicConfigsD3;

  string nbrcfg="";       // neighbor congiguration binary string

  // go through the cubes again...
  //ulong index = 0;
  ulong rx, ry, rz;  // real x,y,z to check after periodic wrap-around adjustment
  // char dum;  // commented out by MM to get rid of compiler  warnings
  ulong Lindex = 0;

  // cout << "Reducing..." << endl;

  int count_cubes=0;
  int removed=1;
  while(removed)
   {
     count_cubes=0;
     removed=0;
     for(ulong i=0; i<xmax; ++i)
       {
  for(ulong j=0; j<ymax; ++j)
    {
      for(ulong k=0; k<zmax; ++k)
        {

   if (TEST(cubits,INDEX(i,j,k)))
     {
         ++count_cubes;
         nbrcfg = "";

       // loop over allowed x, y, & z increments {-1,0,1} lexicographically
       for (int xinc = -1; xinc<=1; xinc++)
         {
    for (int yinc = -1; yinc<=1; yinc++)
      {
        for (int zinc = -1; zinc <=1; zinc++)
          {
     rx=i+xinc;
     ry=j+yinc;
     rz=k+zinc;

     if (xinc==0 && yinc==0 && zinc==0) continue;

     // X Boundary
     if (periodic)
     {
         if (i==0 && xinc==-1)
      rx = xmax-1;
         if (i==xmax-1 && xinc==1)
      rx = 0;
     }
     else
     {
         if (i==0 && xinc==-1)
         {
      nbrcfg+="0";
      continue;
         }
         if (i==xmax-1 && xinc==1)
         {
      nbrcfg+="0";
      continue;
         }
     }

     // Y Boundary
     if (periodic)
     {
         if (j==0 && yinc==-1)
      ry = ymax-1;
         if (j==ymax-1 && yinc==1)
      ry = 0;
     }
     else
     {
         if (j==0 && yinc==-1)
                                     {
                                         nbrcfg+="0";
                                         continue;
                                     }
                                     if (j==ymax-1 && yinc==1)
                                     {
                                         nbrcfg+="0";
                                         continue;
                                     }
                                 }

     // Z Boundary
     if (periodic==2)
     {
         if (k==0 && zinc==-1)
      rz = zmax-1;
         if (k==zmax-1 && zinc==1)
      rz = 0;
     }
     else
                                 {
                                     if (k==0 && zinc==-1)
                                     {
                                         nbrcfg+="0";
                                         continue;
                                     }
                                     if (k==zmax-1 && zinc==1)
                                     {
                                         nbrcfg+="0";
                                         continue;
                                     }
                                 }

     // SO: if the neighbor given by (rx, ry, rz) is present,
     // then add 1 to string nbrcfg, else 0
                                 if ( TEST(cubits, INDEX(rx,ry,rz)) )
        nbrcfg += "1";
     else nbrcfg += "0";
          }
      }
         }
       // obtain LUT index using nbrcfg
       Lindex = bstrtoul(nbrcfg);

//       if(!TEST(Lbuf, Lindex))  // Changed by MM to make it work with acyclicConfigsD3
       if(TEST(Lbuf, Lindex))     // 1 in acyclicConfigsD3 means the configuration is acyclic
         {
    CLEAR(cubits, INDEX(i, j, k));
    removed=1;
         }
     }
        }
    }
       }
   }

  // Added by Marcio Gameiro
//  delete Lbuf;
// [the above line commented-out by Pawel Pilarczyk]
}

int Power2(int exponent)
{
   int i,answer=1;
   for (i=0;i<exponent;answer*=2,i++);
   return(answer);
}

void PrepRead(ifstream* in)
{
   int dim;
   (*in) >> dim;
   if (dim!=chomDIM)
     {
 cout << "Wrong dimension!" << endl << endl;
 exit(1);
     }
   (*in) >> cube_bits;
   (*in) >> top_leaf;

   // cout << "Reading " << top_leaf << " cubes with " << cube_bits << " bits... " << endl;
}

block* Read(complex* c, bitcode& bc)
{
  block* b=new block(cube_bits,c);
  for (char j=0; j<cube_bits; ++j)
    {
      BC(b)(j,bc[j]);
    }
  b->CreateCells(c);
  return(b);
}

void out_of_store()
{
   cerr << "Operator new failed: out of store.\n";
   exit(1);
}

// This is the adaptation of the original Marcio's version, which works only in dimension 3
void compute_homology(char* cubits, ulong xmax, ulong ymax, ulong zmax, int Betti[])
{

   for(int i=0; i<chomDIM+1; ++i)
     gen_flag[i]=0;

   ofstream* gout=NULL;

   int gflag=0;

   if (gflag) {
      gout = new ofstream("gen.dat");
   }

   block* nb=new block;
   complex* c=new complex(nb);

   cube_bits = 3*SUBDIVISIONS; // PUT THE NUMBER OF SUBDIVISIONS HERE
   top_leaf=Power2(cube_bits);

   int coords[3];
   bitcode bc(cube_bits);
   block* b;
   for (int i=0; i<top_leaf; ++i){
      bc.Coordinates(coords);
      if (TEST(cubits,INDEX(coords[0],coords[1],coords[2]))){
         b=Read(c,bc);
         c->InsertCube(b);
      }
      ++bc;
   }

   c->FinalCube();

   c->Homology(gout, Betti);

   delete c;

   if (gflag) {
     gout->close();
   }

}

// The following function added by MM to replace the INDEX macro  (to work with every dimension)

ulong index(int* coord, ulong* base){
  ulong ind=coord[chomDIM-1];
  for(int i=chomDIM-2;i>=0;--i){
    ind*=base[i];
    ind+=coord[i];
  }
  return ind;
}

// The following version of compute_homology added by MM to to work with every dimension

void compute_homology(char* cubits, ulong* max_size, int Betti[])
{
   for(int i=0; i<chomDIM+1; ++i)
     gen_flag[i]=0;

   ofstream* gout=NULL;

   int gflag=0;

   if (gflag) {
      gout = new ofstream("gen.dat");
   }

   block* nb=new block;
   complex* c=new complex(nb);

   // In the following line constant 3 replaced by chomDIM to make it work in every dimension ( by MM)
   cube_bits = chomDIM*SUBDIVISIONS; // PUT THE NUMBER OF SUBDIVISIONS HERE
   if(cube_bits>=32) throw std::string("chom: max depth of 31 bits exceeded\n");
   top_leaf=Power2(cube_bits);

   int coords[MAX_CHOM_DIM]; // constant 3 replaced by MAX_CHOM_DIM by MM
   bitcode bc(cube_bits);
   block* b;

   for (int i=0; i<top_leaf; ++i){
      bc.Coordinates(coords);
//      if (TEST(cubits,INDEX(coords[0],coords[1],coords[2]))){ // replaced by the following code by MM
      ulong ind=index(coords,max_size);
      if (TEST(cubits,ind)){
         b=Read(c,bc);
         c->InsertCube(b);
      }
      ++bc;
   }

   c->FinalCube();

   c->Homology(gout, Betti);

   delete c;

   if (gflag) {
     gout->close();
   }
}
