// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// block.cpp:
//-----------------------------------------------------------------------------

#include "capd/chom/complex.hpp"
#include "capd/chom/block.hpp"
#include "capd/chom/ncell.hpp"
#include "capd/chom/edge.hpp"
#include "capd/chom/vertex.hpp"

int block::counter=0;
int block::max=0;

bitcode& BC(block* b)
{return(*(b->bc));}

void block::CreateCells(complex* c)
{
   bitcode dl(cube_bits+chomDIM); // minimum vertex -- diagonal
   dl.SetAs(this->bc);

   bitcode du(cube_bits+chomDIM); // maximum vertex -- diagonal
   du.SetAs(this->bc);
   for(int i=0; i<chomDIM; ++i)
     du.Increment(i);

   cell* new_cell=NULL;
   Create(&new_cell,dl,du,chomDIM,c,bdry_verts);
   new_cell->MarkInterior();

//   for(int i=0; i<chomDIM+1; ++i)
//     assert(cells[i].Empty());
   cells[chomDIM].Insert(new_cell);
}

int Create(cell** c, bitcode& dl, bitcode& du, int dim, complex* comp, cell_list& verts)
{
   if (dim==0)
     {
// assert(dl==du);
 cell* v=NULL;
 int flag=comp->NewVertex(dl,&v);
// cout << "Vertex: " << v << endl;
 verts.InsertUniqueSort(v);
 (*c)=v;
 return(flag);
     }

   edge* cbp=NULL;      // initialization added by MM to get rid of compiler  warnings

   cell* bbottom=NULL;
   cell* ttop=NULL;
   int flag=1;
   int bflag=1;

   bdry_list* bdry=new bdry_list;

   for(int d=0; d<chomDIM; ++d)
     {
 if (!Flat(dl,du,d))
   {
      du.Decrement(d);
      flag*=Create(&bbottom,dl,du,dim-1,comp,verts);
      du.Increment(d);
      dl.Increment(d);
      flag*=Create(&ttop,dl,du,dim-1,comp,verts);
      dl.Decrement(d);

      if (dim==1)
        {
    vertex* bottom=(vertex*)bbottom;
    vertex* top=(vertex*)ttop;
           cobdry_iter cbit=bottom->Cobdry()->Begin();
           if (flag)  //Don't search unless both vertices already exist!!
             {
                while (cbit!=bottom->Cobdry()->End())
                  {
       cbp=(edge*)Ptr(cbit);
//                          (cbp->diagonal[0])->Print();
//       (bottom->diagonal[0])->Print();
//       (cbp->diagonal[1])->Print();
//       (top->diagonal[0])->Print();

                     if ((cbp->bdry[1]==top)&&(cbp->bdry[0]==bottom)&&(!(cbp->Interior())))
//                     if ((BdryListEqual(bdry,&(cbp->Bdry())))&&(!(cbp->Interior())))
//       if ((*((cbp->diagonal[0]))==(*(bottom->diagonal[0])))&&((*(cbp->diagonal[1]))==(*(top->diagonal[0])))) // ?? need to check if NON-interior ??
                       {
//                   assert(!(cbp->Interior()));
//     cout << "breaking" << endl;
            break;
         }
       else
         {
//     Bdry()->Print();
//     (cbp->Bdry()).Print();
//            cout << "not breaking" << endl;
         }
              ++cbit;
                  }
             }
           if ((cbit==bottom->Cobdry()->End())||(!flag))
                    {
                edge* e=new edge(bottom,top);
//         cout << "Edge: " << e << endl;
         if (gen_flag[1])
    {
              e->diagonal[0]=new bitcode(bottom->bc->Bits());
              e->diagonal[0]->SetAs(bottom->bc);
              e->diagonal[1]=new bitcode(top->bc->Bits());
              e->diagonal[1]->SetAs(top->bc);;
    }
                bottom->Cobdry()->InsertUniqueSort(e,-1);
                top->Cobdry()->InsertUniqueSort(e,1);
         (*c)=e;
         delete bdry;
         return(0);
             }
           else
             {
         delete bdry;
                       (*c)=cbp;
                return(1);
             }
        }
      else
        {
    bdry->Insert(bbottom,-bflag);
           bdry->InsertUniqueSort(ttop,bflag);
           bflag=-bflag;
        }
   }
     }

   if(dim==2)
     {
 edge* top=(edge*)ttop;
// edge* bottom=(edge*)bbottom; // commented out by MM to get rid of compiler  warnings

 cell* dvl=comp->FindVertex(dl);
 cell* dvu=comp->FindVertex(du);

 ncell* f;
        cobdry_iter cbit=top->Cobdry()->Begin();
        if (flag)
          {
             while (cbit!=top->Cobdry()->End())  // Can be more efficient by looking only at non-interior
               {
//           if ((BdryListEqual(bdry,(((ncell*)Ptr(cbit))->Bdry())))&&(!(Ptr(cbit)->Interior())))
           if ((dvl==((ncell*)Ptr(cbit))->dv[0])&&(dvu==((ncell*)Ptr(cbit))->dv[1])&&(!(Ptr(cbit)->Interior())))
      {
//         assert(!(Ptr(cbit)->Interior()));
         break;
      }
           ++cbit;
        }
   }
        if ((cbit==top->Cobdry()->End())||(!flag))
          {
             f=new ncell(dim);
//      cout << "Ncell: " << f << endl;

      f->dv[0]=dvl;
      f->dv[1]=dvu;

      bdry_iter bit=bdry->Begin();
      while(bit!=bdry->End())
        {
    f->Bdry()->Insert((*bit).Cell(),(*bit).Incidence());
    ((edge*)Ptr(bit))->Cobdry()->InsertUniqueSort(f,(*bit).Incidence());
    ++bit;
        }
             if (gen_flag[dim])
        {
                  f->diagonal[0]=new bitcode(cube_bits+chomDIM);
           f->diagonal[1]=new bitcode(cube_bits+chomDIM);
           f->diagonal[0]->SetAs(dl);
           f->diagonal[1]->SetAs(du);
        }
      delete bdry;
      (*c)=f;
      return(0);
   }
        else
          {
      delete bdry;
      (*c)=Ptr(cbit);
      return(1);
   }
     }
//   else
//     {
// bdry->Insert(bbottom,-bflag);
// bdry->InsertUniqueSort(ttop,bflag);
// bflag=-bflag;
//   }

   if((dim<chomDIM)&&(dim>2))
     {
 ncell* top=(ncell*)ttop;
// ncell* bottom=(ncell*)bbottom; // commented out by MM to get rid of compiler  warnings

 cell* dvl=comp->FindVertex(dl);
 cell* dvu=comp->FindVertex(du);

 ncell* f;
        cobdry_iter cbit=top->Cobdry()->Begin();
        if (flag)
          {
             while (cbit!=top->Cobdry()->End())  // Can be more efficient by looking only at non-interior
               {
//           if ((BdryListEqual(bdry,(((ncell*)Ptr(cbit))->Bdry())))&&(!(Ptr(cbit)->Interior())))
           if ((dvl==((ncell*)Ptr(cbit))->dv[0])&&(dvu==((ncell*)Ptr(cbit))->dv[1])&&(!(Ptr(cbit)->Interior())))
      {
//         assert(!(Ptr(cbit)->Interior()));
         break;
      }
           ++cbit;
        }
   }
        if ((cbit==top->Cobdry()->End())||(!flag))
          {
             f=new ncell(dim);

      f->dv[0]=dvl;
      f->dv[1]=dvu;

      bdry_iter bit=bdry->Begin();
      while(bit!=bdry->End())
        {
    f->Bdry()->Insert((*bit).Cell(),(*bit).Incidence());
    ((ncell*)Ptr(bit))->Cobdry()->InsertUniqueSort(f,(*bit).Incidence());
    ++bit;
        }
             if (gen_flag[dim])
        {
                  f->diagonal[0]=new bitcode(cube_bits+chomDIM);
           f->diagonal[1]=new bitcode(cube_bits+chomDIM);
           f->diagonal[0]->SetAs(dl);
           f->diagonal[1]->SetAs(du);
        }
      delete bdry;
      (*c)=f;
      return(0);
   }
        else
          {
      delete bdry;
      (*c)=Ptr(cbit);
      return(1);
   }
     }
//   else
//     {
// bdry->Insert(bbottom,-bflag);
// bdry->InsertUniqueSort(ttop,bflag);
// bflag=-bflag;
//     }

//   assert((chomDIM>2)&&(chomDIM==dim));

   ncell* new_cell=new ncell(chomDIM);

   new_cell->dv[0]=comp->FindVertex(dl);
   new_cell->dv[1]=comp->FindVertex(du);

   bdry_iter bit=bdry->Begin();
   while(bit!=bdry->End())
     {
 new_cell->Bdry()->Insert((*bit).Cell(),(*bit).Incidence());
        ((ncell*)Ptr(bit))->Cobdry()->InsertUniqueSort(new_cell,(*bit).Incidence());
 ++bit;
     }
   (*c)=new_cell;
   delete bdry;
   return(0);
}

