// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
// Modified by Marcio Gameiro - 04/28/2005
//-----------------------------------------------------------------------------
// complex.cpp:
//-----------------------------------------------------------------------------

#include "capd/chom/chom.hpp"
#include "capd/chom/complex.hpp"
#include "capd/chom/cell.hpp"
#include "capd/chom/edge.hpp"
#include "capd/chom/vertex.hpp"
#include "capd/chom/ncell.hpp"
#include "capd/chom/block.hpp"
#include "capd/chom/bitcodes.hpp"

#define CHL

int chomDIM=3;

//#define EZSPIRAL

void complex::Recurse(node* n, list<block*>* bl, int level)
{
   if (n==NULL)
     return;
   if (level==chomDIM)
     {
 bl->push_back((block *)n);
 return;
     }
   else
     {
 ++level;
 Recurse(n->Left,bl,level);
 Recurse(n->Right,bl,level);
 return;
     }
}

void complex::Delete(node* n, int level,int flag)
{
   if ((n==NULL)||(n==cubes.Root))
     return;
   if (level==chomDIM)
     {
 delete (block*)n;
 return;
     }
   else
     {
 ++level;
 Delete(n->Left,level,0);
 Delete(n->Right,level,0);
 if ((level==1)&&(flag))
   {
   delete (block*)n;
   }
 else
   delete n;
 return;
     }
}

block* complex::Merge(node* n)
{
   list<block*> sub_blocks;
   Recurse(n,&sub_blocks,0);

   list<block*>::iterator sbit=sub_blocks.begin();
//   if (sbit==sub_blocks.end())
//     exit(1);

   block* b=new block(BC(*sbit),this);
//    block* b=new block(*((*sbit)->bc),this);
//   assert(b->bdry_verts.Empty());
//   (b->bc)->SetAs(BC(*sbit));
   BC(b).SetAs(BC(*sbit));
   for(int i=0;i<chomDIM;++i)
     BC(b)++;
   int level=(cube_bits-BC(b).Bits())/chomDIM;
   for(int i=0;i<level*chomDIM;++i)
     BC(b)--;
   BC(b).Coordinates(min);
   for(int i=0;i<level*chomDIM;++i)
     BC(b)++;

   vertex* v;
   int vc[MAX_CHOM_DIM];
   int flag=1;
   cell_iter bvit;
   cell_iter cit;
   cobdry_iter cbit;

   while(sbit!=sub_blocks.end())
     {
 bvit=(*sbit)->bdry_verts.Begin();
 while(bvit!=(*sbit)->bdry_verts.End())
   {
             v=(vertex*)(*bvit);
      v->bc->Coordinates(vc);
      flag=1;
      for (int i=0; i<chomDIM; ++i)
        {
    if (periodic)
             flag*=(((min[i]<vc[i])&&(vc[i]<min[i]+Power2(level))));//||((vc[i]==0)||(vc[i]==Power2(cube_bits/chomDIM))));
    else
      flag*=(((min[i]<vc[i])&&(vc[i]<min[i]+Power2(level)))||((vc[i]==0)||(vc[i]==Power2(cube_bits/chomDIM))));
        }
             if (flag)
        {
    if (!(v->Interior()))
      {
         v->MarkInterior();
         DeleteVertex(v);
         b->cells[0].InsertUniqueSort(v);
      }
        }
      else
        b->bdry_verts.InsertUniqueSort(v);
      ++bvit;
   }
 for(int i=0;i<chomDIM;++i)
    {
        cit=(*sbit)->cells[i].Begin();
       while(cit!=(*sbit)->cells[i].End())
          {
             b->cells[i].InsertUniqueSort(Ptr(cit));
             ++cit;
          }
    }
 ++sbit;
     }

   cit=b->cells[0].Begin();
   while(cit!=b->cells[0].End())
     {
 cbit=((vertex*)(*cit))->Cobdry()->Begin();
//      cout << "size " << (*cit)->Cobdry()->Size() << endl;
 while(cbit!=((vertex*)(*cit))->Cobdry()->End())
    {
       ((edge*)Ptr(cbit))->MarkInterior();
//       b->cells[1].InsertUniqueSort(Ptr(cbit));
       if (b->cells[1].Find(Ptr(cbit))==b->cells[1].End())
  {
     b->cells[1].InsertUniqueSort(Ptr(cbit));
  }
       ++cbit;
    }
 ++cit;
     }

   cit=b->cells[1].Begin();
   while(cit!=b->cells[1].End())
     {
 cbit=((edge*)(*cit))->Cobdry()->Begin();
//      cout << "size " << (*cit)->Cobdry()->Size() << endl;
 while(cbit!=((edge*)(*cit))->Cobdry()->End())
    {
       ((ncell*)Ptr(cbit))->MarkInterior();
//       b->cells[2].InsertUniqueSort(Ptr(cbit));
       if (b->cells[2].Find(Ptr(cbit))==b->cells[2].End())
  {
     b->cells[2].InsertUniqueSort(Ptr(cbit));
  }
       ++cbit;
    }
 ++cit;
     }

//   cout << "size0: " << b->cells[0].Size() << endl;
//   cout << "size1: " << b->cells[1].Size() << endl;
//   cout << "size2: " << b->cells[2].Size() << endl;

   for(int i=3;i<chomDIM;++i)
     {
 cit=b->cells[i-1].Begin();
 while(cit!=b->cells[i-1].End())
   {
      cbit=((ncell*)(*cit))->Cobdry()->Begin();
//             cout << "size " << (*cit)->Cobdry()->Size() << endl;
      while(cbit!=((ncell*)(*cit))->Cobdry()->End())
        {
    ((ncell*)Ptr(cbit))->MarkInterior();
//    b->cells[i].InsertUniqueSort(Ptr(cbit));
    if (b->cells[i].Find(Ptr(cbit))==b->cells[i].End())
      {
         b->cells[i].InsertUniqueSort(Ptr(cbit));
      }
    ++cbit;
        }
      ++cit;
   }
     }

   int rflag=0;
   if (n==cubes.Root)
     {
        cubes.Root=b;
 rflag=1;
     }
   else
     {
       node* parent=n->Parent;
       if (parent->Left==n)
         parent->Left=b;
       else
         parent->Right=b;
       b->Parent=parent;
     }

   Delete(n,0,rflag);

   return(b);
}

int complex::NewVertex(bitcode& bcnp, cell** v)
{
//   assert((*v)==NULL);

   bitcode* bcl;
   node* n;

// Lower vertex in periodic case
   if (periodic)
     {
        LowestVertex(bcnp,&bcl);
     }

   if (periodic)
     n=vertices.Find(*bcl);
   else
     n=vertices.Find(bcnp);

   if (n==NULL)
     {
 if (periodic)
          (*v)=new vertex(*bcl);
        else
   (*v)=new vertex(bcnp);
 vert* vv=new vert(*v);
 vv->v=(*v);
 if (periodic)
   vertices.Insert(*bcl,vv);
 else
   vertices.Insert(bcnp,vv);
 if (periodic)
   delete bcl; // periodic case
 return(0);
     }
   else
     (*v)=((vert *)n)->v;
   if (periodic)
     delete bcl; // periodic case
   return(1);
}

cell* complex::FindVertex(bitcode& bcnp)
{
   bitcode* bcl;
   node* n;

// Lower vertex in periodic case
   if (periodic)
     {
        LowestVertex(bcnp,&bcl);
     }

   if (periodic)
     n=vertices.Find(*bcl);
   else
     n=vertices.Find(bcnp);

   if (periodic)
     delete bcl; // periodic case

   if (n==NULL)
     return(NULL);
   else
     return(((vert *)n)->v);
}

void complex::Cleanup()
{
  cell_iter cit;
  for (int i=0; i<chomDIM+1; ++i)
    {
      cit=((block *)cubes.Root)->cells[i].Begin();
      while (cit!=((block *)cubes.Root)->cells[i].End())
 {
   if (i==0)
     delete (vertex *)Ptr(cit);
   if (i==1)
     delete (edge *)Ptr(cit);
   if (i>1)
     delete (ncell *)Ptr(cit);
   ++cit;
 }
    }

  delete vertices.Root;
  delete (block*)cubes.Root;
}

void complex::Homology(ofstream* gout, int Betti[])
{
   cell_iter cit;

   // cout << "*** Homology ****" << endl;
   for (int i=0; i<chomDIM+1; ++i)
     {
 Betti[i]=0;
 cit=((block *)cubes.Root)->cells[i].Begin();
 while (cit!=((block *)cubes.Root)->cells[i].End())
   {
      ++(Betti[i]);
      ++cit;
   }
 // cout << "Betti number " << i << " is " << Betti[i] << endl;
     }

   // cout << "*****************" << endl;

   bdry_list bl;
   bdry_iter bit;
   int coords[MAX_CHOM_DIM];

   int gen_count=0;
   if (gen_flag[1])
     {
        ofstream gensize_out("gensize.dat");

// edge* e;   // commented out by MM to get rid of compiler  warnings
        cit=((block *)cubes.Root)->cells[1].Begin();
        for(int gen=0; gen<Betti[1]; ++gen)
          {
//      (*gout) << endl;
//      (*gout) << "*** 1-Generator # " << gen+1 << " ***" << endl;
      ((edge*)(*cit))->Generator(&bl,1);
      ++gen_count;

      if (bl.Size()<GEN_TOL)
        {
    cout << "Omitting 1d generator of size " << bl.Size() << " cells." << endl;
    continue;
        }
      else
        cout << "Writing 1d generator # " << gen_count << " of size " << bl.Size() << " cells." << endl;

             gensize_out << bl.Size() << endl;

      bit=bl.Begin();
      while(bit!=bl.End())
        {
           if ((*bit).Incidence()==0)
             cout << "zero1:" << endl;
           else
             {
#ifdef CHL
                (*gout) << gen_count << " ";
                if ((*bit).Incidence() >= 0)
    (*gout) << " ";
         (*gout) << (*bit).Incidence() << " ";
         ((edge*)Ptr(bit))->diagonal[0]->Coordinates(coords);
                for (int i=0; i<chomDIM; ++i)
           (*gout) << coords[i] << " ";
                ((edge*)Ptr(bit))->diagonal[1]->Coordinates(coords);
         for (int i=0; i<chomDIM; ++i)
           (*gout) << coords[i] << " ";
         (*gout) << endl;
#endif

#ifdef MATLAB
                ((edge*)Ptr(bit))->diagonal[0]->Coordinates(coords);
                for (int i=0; i<chomDIM; ++i)
           (*gout) << coords[i] << " ";
                ((edge*)Ptr(bit))->diagonal[1]->Coordinates(coords);
         for (int i=0; i<chomDIM; ++i)
           (*gout) << coords[i] << " ";
                (*gout) << (*bit).Incidence() << " " << gen_count << " " << 1 << endl;
#endif

#ifdef COB
                       (*gout) << gen_count << " (" << (*bit).Incidence() << ") [(";
         ((edge*)Ptr(bit))->diagonal[0]->Coordinates(coords);
         for (int i=0; i<chomDIM-1; ++i)
           (*gout) << coords[i] << ",";
                       (*gout) << coords[chomDIM-1] << "),(";
         ((edge*)Ptr(bit))->diagonal[1]->Coordinates(coords);
         for (int i=0; i<chomDIM-1; ++i)
           (*gout) << coords[i] << ",";
         (*gout) << coords[chomDIM-1] << ")]" << endl;
#endif

/*
         e=(edge*)Ptr(bit);
                e->diagonal[0]->Coordinates(coords);
                for (int i=0; i<chomDIM; ++i)
           (*gout) << coords[i] << " ";
                e->diagonal[1]->Coordinates(coords);
         for (int i=0; i<chomDIM; ++i)
           (*gout) << coords[i] << " ";
                (*gout) << (*bit).Incidence() << " " << gen_count << " " << 1 << endl;
*/
                       ++bit;
             }
        }
      bl.Clear();
      ++cit;
          }
     }

   for(int j=2;j<chomDIM;++j)
     {
        if (gen_flag[j])
          {
//      ncell* nc;  // commented out by MM to get rid of compiler  warnings
             cit=((block *)cubes.Root)->cells[j].Begin();
             for(int gen=0; gen<Betti[j]; ++gen)
               {
//           (*gout) << endl;
//           (*gout) << "*** " << j << "-Generator # " << gen+1 << " ***" << endl;
           ((ncell*)(*cit))->Generator(&bl,1);
    ++gen_count;

    if (bl.Size()<GEN_TOL)
             {
         cout << "Omitting " << j << "d generator of size " << bl.Size() << " cells." << endl;
         continue;
             }
           else
      cout << "Writing " << j << "d generator # " << gen_count << " of size " << bl.Size() << " cells." << endl;

           bit=bl.Begin();
           while(bit!=bl.End())
             {
                if ((*bit).Incidence()==0)
                  cout << "zero" << j << ":" << endl;
                else
                  {
#ifdef CHL
                     (*gout) << gen_count << " ";
                     if ((*bit).Incidence() >= 0)
         (*gout) << " ";
       (*gout) << (*bit).Incidence() << " ";
              ((ncell*)Ptr(bit))->diagonal[0]->Coordinates(coords);
                     for (int i=0; i<chomDIM; ++i)
                (*gout) << coords[i] << " ";
                     ((ncell*)Ptr(bit))->diagonal[1]->Coordinates(coords);
              for (int i=0; i<chomDIM; ++i)
                (*gout) << coords[i] << " ";
              (*gout) << endl;
#endif

#ifdef MATLAB
                     ((ncell*)Ptr(bit))->diagonal[0]->Coordinates(coords);
                     for (int i=0; i<chomDIM; ++i)
                (*gout) << coords[i] << " ";
                     ((ncell*)Ptr(bit))->diagonal[1]->Coordinates(coords);
              for (int i=0; i<chomDIM; ++i)
                (*gout) << coords[i] << " ";
                     (*gout) << (*bit).Incidence() << " " << gen_count << " " << j << endl;
#endif

#ifdef COB
       (*gout) << gen_count << " (" << (*bit).Incidence() << ") [(";
       ((ncell*)Ptr(bit))->diagonal[0]->Coordinates(coords);
                     for (int i=0; i<chomDIM-1; ++i)
                (*gout) << coords[i] << ",";
       (*gout) << coords[chomDIM-1] << "),(";
                     ((ncell*)Ptr(bit))->diagonal[1]->Coordinates(coords);
              for (int i=0; i<chomDIM-1; ++i)
                (*gout) << coords[i] << ",";
              (*gout) << coords[chomDIM-1] << ")]" << endl;
#endif

/*
       nc=(ncell*)Ptr(bit);
                     nc->diagonal[0]->Coordinates(coords);
                     for (int i=0; i<chomDIM; ++i)
                (*gout) << coords[i] << " ";
                     nc->diagonal[1]->Coordinates(coords);
              for (int i=0; i<chomDIM; ++i)
                (*gout) << coords[i] << " ";
                     (*gout) << (*bit).Incidence() << " " << gen_count << " " << j << endl;
*/

                     ++bit;
                  }
             }
           bl.Clear();
           ++cit;
        }
          }
     }
}

bool complex::InsertCube(block* b)
{
   bitcode* bc=new bitcode(BC(b).Bits());
   bc->SetAs(BC(b));

   cubes.Insert(*bc,b);
   if (previous_cube==NULL)
     {
       previous_cube=new bitcode(cube_bits);
       if(!previous_cube) throw std::string("chom: memory request for bitcode failed\n"); // Added by MM
       previous_cube->SetAs(bc);
       delete bc;
       return true;
     }

//     assert(previous_cube->Bits()==cube_bits);

   node* simplifiable_node;
   block* simplifiable_block;
   int levels=Ancestor(bc,previous_cube);
   while (levels>=chomDIM)
     {
 for (int j=0; j<chomDIM; ++j)
    (*previous_cube)++;
 levels-=chomDIM;
        simplifiable_node=cubes.Find(*previous_cube);
 simplifiable_block=Merge(simplifiable_node);
 Simplify(simplifiable_block);
      }

   delete previous_cube;
   previous_cube=new bitcode(cube_bits);
   if(!previous_cube) throw std::string("chom: memory request for bitcode failed\n"); // Added by MM
   previous_cube->SetAs(*bc);
   delete bc;

   return true;
}

void complex::FinalCube()
{
   int levels=previous_cube->Bits();
   node*  simplifiable_node;
   block* simplifiable_block=NULL; // initialization added by MM to get rid of compiler  warnings
   while (levels>=chomDIM)
     {
       for (int j=0; j<chomDIM; ++j)
       (*previous_cube)++;
       levels-=chomDIM;
       simplifiable_node=cubes.Find(*previous_cube);
       simplifiable_block=Merge(simplifiable_node);
       Simplify(simplifiable_block);
     }
   if (periodic)
     FinalSimplify(simplifiable_block); // periodic

   delete previous_cube;
}

void complex::FinalSimplify(block* b)
{
   vertex* v;
   cell_iter bvit=b->bdry_verts.Begin();
   while(bvit!=b->bdry_verts.End())
     {
        v=(vertex*)(*bvit);
 v->MarkInterior();
 DeleteVertex(v);
 if (b->cells[0].Find(v)==b->cells[0].End())
   {
      b->cells[0].InsertUniqueSort(v);
   }
 ++bvit;
     }

   cobdry_iter cbit;
   cell_iter cit=b->cells[0].Begin();
   while(cit!=b->cells[0].End())
     {
 cbit=((vertex*)(*cit))->Cobdry()->Begin();
//      cout << "size " << (*cit)->Cobdry()->Size() << endl;
 while(cbit!=((vertex*)(*cit))->Cobdry()->End())
    {
       ((edge*)Ptr(cbit))->MarkInterior();
//       b->cells[1].InsertUniqueSort(Ptr(cbit));
       if (b->cells[1].Find(Ptr(cbit))==b->cells[1].End())
  {
     b->cells[1].InsertUniqueSort(Ptr(cbit));
  }
       ++cbit;
    }
 ++cit;
     }

   cit=b->cells[1].Begin();
   while(cit!=b->cells[1].End())
     {
 cbit=((edge*)(*cit))->Cobdry()->Begin();
//      cout << "size " << (*cit)->Cobdry()->Size() << endl;
 while(cbit!=((edge*)(*cit))->Cobdry()->End())
    {
       ((ncell*)Ptr(cbit))->MarkInterior();
//       b->cells[2].InsertUniqueSort(Ptr(cbit));
       if (b->cells[2].Find(Ptr(cbit))==b->cells[2].End())
  {
     b->cells[2].InsertUniqueSort(Ptr(cbit));
  }
       ++cbit;
    }
 ++cit;
     }

//   cout << "size0: " << b->cells[0].Size() << endl;
//   cout << "size1: " << b->cells[1].Size() << endl;
//   cout << "size2: " << b->cells[2].Size() << endl;

   for(int i=3;i<chomDIM;++i)
     {
 cit=b->cells[i-1].Begin();
 while(cit!=b->cells[i-1].End())
   {
      cbit=((ncell*)(*cit))->Cobdry()->Begin();
//             cout << "size " << (*cit)->Cobdry()->Size() << endl;
      while(cbit!=((ncell*)(*cit))->Cobdry()->End())
        {
    ((ncell*)Ptr(cbit))->MarkInterior();
//    b->cells[i].InsertUniqueSort(Ptr(cbit));
    if (b->cells[i].Find(Ptr(cbit))==b->cells[i].End())
      {
         b->cells[i].InsertUniqueSort(Ptr(cbit));
      }
    ++cbit;
        }
      ++cit;
   }
     }

   Simplify(b);
}

void complex::Simplify(block* n)
{
//   cout << "BEGIN : Size0: " << n->cells[0].Size() << "   Size1: " << n->cells[1].Size() << "   Size2: " << n->cells[2].Size()<< endl << endl;

   cell_iter cit;

   ncell* b;
   ncell* c;
   int i;
   for(int j=0; j<chomDIM-2; ++j)
     {
 i=chomDIM-j-1;
 cit=n->cells[i].Begin();
        while (cit!=n->cells[i].End())
          {
     b=(ncell*)Ptr(cit);
     c=(ncell*)(b->FindInvertibleCobdryElement());

//     b->Cobdry()->Print();
//     cout << c << endl;

     if (c!=NULL)
       {
          b->Reduce(c);
          ++cit;
                 n->cells[i].Remove(b);
                 n->cells[i+1].Remove(c);

   if (b->NoSave())
     delete b;
   else
     {
        delete b->Cobdry();//->Clear();
        delete b->Bdry();//->Clear();
     }
                 if (c->NoSave())
     delete c;
   else
     {
        delete c->Bdry();//->Clear();
        delete c->Cobdry();//->Clear();
     }
              }
            else
       ++cit;
   }
     }

   edge* be;
//   cout << "Size0: " << n->cells[0].Size() << "   Size1: " << n->cells[1].Size() << "   Size2: " << n->cells[2].Size() << endl << endl;
   cit=n->cells[1].Begin();
   while (cit!=n->cells[1].End())
     {
        be=(edge*)Ptr(cit);
 c=(ncell*)(be->FindInvertibleCobdryElement());
// cout << "c: " << c << endl;
 if (c!=NULL)
   {
      be->Reduce(c);
      ++cit;
             n->cells[1].Remove(be);
             n->cells[2].Remove(c);

      if (be->NoSave())
        delete be;
      else
        delete be->Cobdry();//->Clear();
             if (c->NoSave())
        delete c;
      else
        {
               delete c->Bdry();//->Clear();
    delete c->Cobdry();//->Clear();
        }
          }
        else
   ++cit;
      }

   edge* cbe;
   vertex* bv;
//   cout << "Size0: " << n->cells[0].Size() << "   Size1: " << n->cells[1].Size() << "   Size2: " << n->cells[2].Size() << endl << endl;
   cit=n->cells[0].Begin();
   while (cit!=n->cells[0].End())
     {
        bv=(vertex*)Ptr(cit);
// cout << bv << endl;
// bv->Cobdry()->Print();
 cbe=(edge*)(bv->FindInvertibleCobdryElement());
 if (cbe!=NULL)
   {
      bv->Reduce(cbe);
      ++cit;
             n->cells[0].Remove(bv);
             n->cells[1].Remove(cbe);

      delete bv;

             if (cbe->NoSave())
        delete cbe;
      else
        delete cbe->Cobdry();//->Clear();
          }
        else
   ++cit;
      }
//      cout << "END : Size0: " << n->cells[0].Size() << "   Size1: " << n->cells[1].Size() << "   Size2: " << n->cells[2].Size() << endl << endl;
}
