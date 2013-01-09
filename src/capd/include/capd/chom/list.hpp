// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// list.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_LIST_HPP_ 
#define _CAPD_CHOM_LIST_HPP_ 

#include "capd/chom/chom.hpp"

//-----------------------------------------------------------------------------
// Boundry element declarations
//-----------------------------------------------------------------------------

class cell;

/*! \class bdry_elem
    \brief Boundary/coboundary element class.

    A boundary/coboundary element consists of a cell and its incidence number.
    Last modified by BK on 6/25/00.
*/
class bdry_elem{
 private:
   cell* c;
   int o;
   void operator=(const bdry_elem&);            // disable assignment operator
   friend class bdry_cell_equal;                // equality with cell* unary predicate
                                                // for certain types of sorts, see below
 public:
//   static int counter;
//   static int max;
   bdry_elem(cell* cc,int oo) : c(cc), o(oo) {} //{++counter; ++max;}
//   bdry_elem(const bdry_elem& be) : c(be.Cell()), o(be.Incidence()) {++counter; ++max;}
//   ~bdry_elem() {--counter;}
   cell* Cell() const
     {return c;}                                //!< Return a pointer to the cell in this bdry_elem.
   bool Invertible()
     {return ((o==1)||(o==-1));}                //!< True if incidence number is +1 or -1.
   int Incidence() const
     {return o;}                                //!< Return the incidence number of the cell.
   void Incidence(int oo)                         // ... but incidence number can change
     {o=oo;}                                    //!< Modify the incidence number of the cell.
   bool operator<(const bdry_elem& be)  const;    // ordering based on cell* only
   bool operator==(const bdry_elem& be) const     // equality based on cell* only
     {return(c==be.c);}                         //!< Equality operator for sorting.
};

/*! \class bdry_cell_equal
    \brief Unary predicate for equality of bdry_elem according to cell*.

    Last modified by BK on 6/25/00.
*/
class bdry_cell_equal{
 private:
   cell* c;
 public:
   explicit bdry_cell_equal(cell* cc) : c(cc) {}
   bool operator()(const bdry_elem& be) const
     {return be.c==c;}
};

//-----------------------------------------------------------------------------
// Boundary/coboundary list declarations with iterators
//-----------------------------------------------------------------------------

typedef list<bdry_elem>::iterator bdry_iter;

/*! \class bdry_list
    \brief List of boundary/coboundary elements.

    Last modified by BK on 7/4/00
*/
class bdry_list{
 private:
   list<bdry_elem> l;
   bdry_list(const bdry_list&) {}        // no copy constructor
   void operator=(const bdry_list&) {}   // no assignment operator
 public:
   bdry_list() {}
   ~bdry_list() {Clear();}
   bdry_iter Find(cell*);         //!< Check if a cell is in the list, if so return an iterator.
   bool Contains(cell*);          //!< Check if a cell is in the list.
   void Insert(cell*,int);        //!< Insert a bdry_elem into the list.
   void InsertUniqueSort(cell*,int);    //!< Insert a bdry_elem into the list and sort by pointer.
   bool Remove(cell*);            //!< Remove a cell from the list.
   void Remove(bdry_iter&);       //!< Remove the cell at this location in the list.
   void Clear();                  //!< Remove all elements from the list.
   bool Empty() const;            //!< Check if list is empty.
   int  Size() const;             //!< Return the number of bdry_elems in the list.
   void Print();                  //!< Print the list.
   bdry_iter Begin();             //!< Return an iterator at the beginning of the list.
   bdry_iter End();               //!< Return an iterator at the end of the list.
};

typedef bdry_list cobdry_list;
typedef bdry_iter cobdry_iter;

/*! \fn BdryListInsert(bdry_list*, cell*, int);
    \brief Inserts into bdry_list adding incidence numbers.

    Last modified by BK on 5/5/00.
*/
void BdryListInsert(bdry_list*, cell*, int);

/*! \fn BdryListEqual(bdry_list* bl1, bdry_list* bl2);
    \brief Compares two bdry_lists and is used in cell creation to prevent duplication.

    Last modified by BK on 5/5/00.
*/
bool BdryListEqual(bdry_list* bl1, bdry_list* bl2);

// dereference for generic bdry/cobdry lists
cell* Ptr(bdry_iter&);

// Inline member function definitions for bdry_list

inline void bdry_list::Insert(cell *c, int o)
{
//   bdry_elem be(c,o);
//   l.push_back(be);
   l.push_back(bdry_elem(c,o));
}

inline void bdry_list::InsertUniqueSort(cell *c, int o)
{
//   bdry_elem be(c,o);
//   l.push_back(be);
   l.push_back(bdry_elem(c,o));
//   l.sort();
//   bdry_iter p=unique(l.begin(),l.end());      // should not be required!
//   l.erase(p,l.end());
}

inline void bdry_list::Remove(bdry_iter& it)
{
   l.erase(it);
}

inline void bdry_list::Clear()
{
   l.erase(l.begin(),l.end());
}

inline bdry_iter bdry_list::Find(cell *c)
{
   return find_if(l.begin(),l.end(),bdry_cell_equal(c));
}

inline bool bdry_list::Contains(cell *c)
{
   return(find_if(l.begin(),l.end(),bdry_cell_equal(c))!=l.end());
}

inline bool bdry_list::Empty() const
{
   return l.empty();
}

inline int bdry_list::Size() const
{
   return l.size();
}

inline bdry_iter bdry_list::Begin()
{
   return l.begin();
}
inline bdry_iter bdry_list::End()
{
   return l.end();
}

//-----------------------------------------------------------------------------
// General cell list declarations with iterators
//-----------------------------------------------------------------------------

typedef list<cell*>::iterator cell_iter;

/*! \class cell_list
    \brief List of cells.

    Last modified by BK on 7/4/00.
*/
class cell_list{
 private:
   list<cell*> l;
   cell_list(const cell_list&) {}       // no copy constructor
   void operator=(const cell_list&) {}  // no assignment operator
 public:
   cell_list() {}
   cell_iter Find(cell*);        //!< Check if a cell is in the list, if so return an iterator.
   bool Contains(cell*);         //!< Check if a cell is in the list.
   void Insert(cell*);           //!< Insert a cell into the list.
   void InsertUniqueSort(cell*); //!< Insert a cell into the list and sort by pointer and uniquify.
   void InsertSort(cell*);       //!< Insert a cell into the list and sort by pointer.
   bool Remove(cell*);           //!< Remove a cell from the list.
   void Remove(cell_iter&);      //!< Remove the cell at this location in the list.
   void Clear();                 //!< Clear all cells from the list.
   bool Empty() const;           //!< Check if the list is empty.
   int  Size() const;            //!< Return the length of the list.
   void Print();                 //!< Print the list.
   cell_iter Begin();            //!< Return an iterator to the beginning of the list.
   cell_iter End();              //!< Return an iterator to the end of the list.
};

// dereference for generic cell lists
cell* Ptr(cell_iter&);

// Inline member function definitions for cell_list

inline void cell_list::Clear()
{
   l.erase(l.begin(),l.end());
}

inline void cell_list::Insert(cell* c)
{
   l.push_back(c);
}

inline void cell_list::InsertSort(cell* c)
{
   l.push_back(c);
//   l.sort();
}

inline void cell_list::InsertUniqueSort(cell* c)
{
   l.push_back(c);
//   l.sort();
//   cell_iter p=unique(l.begin(),l.end());  // this is required!
//   l.erase(p,l.end());
}

inline void cell_list::Remove(cell_iter& it)
{
   l.erase(it);
}

inline cell_iter cell_list::Find(cell* c)
{
   return find(l.begin(),l.end(),c);
}

inline bool cell_list::Contains(cell* c)
{
   return(find(l.begin(),l.end(),c)!=l.end());
}

inline bool cell_list::Empty() const
{
   return l.empty();
}

inline int cell_list::Size() const
{
   return l.size();
}

inline cell_iter cell_list::Begin()
{
   return l.begin();
}

inline cell_iter cell_list::End()
{
   return l.end();
}

#endif // _CAPD_CHOM_LIST_HPP_ 


