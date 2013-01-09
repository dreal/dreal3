/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file flatmatr.h
///
/// This file contains the definition of a simple matrix class which is
/// stored in a single vector, but its elements can be accessed in the
/// double indexing style, e.g., M[0][2].
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on August 25, 2006. Last revision: October 8, 2008.


#ifndef _CAPD_HOMOLOGY_FLATMATR_H_ 
#define _CAPD_HOMOLOGY_FLATMATR_H_ 

#include <new>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------ FLAT MATRIX -------------------
// --------------------------------------------------

/// This class defines a simple data structure for a flat 2-dim square matrix
/// whose entries are stored in a single array. Additional classes for a row
/// and a constant row are defined within this class which allow to use the
/// usual double indexing to get to the entries of the matrix, both for
/// reading only and for modifying the entries, e.g., M[0][1].
template <class element>
class flatMatrix
{
public:
	/// The main constructor. The size of the matrix
	/// (the number of rows and collumns) must be given
	/// at initialization.
	flatMatrix (int size): n (size), tab (new element [n * n]) {return;}

	/// The copy constructor which copies all the entries of the matrix.
	flatMatrix (const flatMatrix<element> &M):
		n (M. n), tab (new element [n * n])
	{
		int memSize = n * n;
		for (int i = 0; i < memSize; ++ i)
			tab [i] = M. tab [i];
		return;
	}

	/// The assignment operator. It is permitted only for matrices
	/// of the same size. It copies all the entries of the matrix.
	flatMatrix &operator = (const flatMatrix<element> &M)
	{
		if (n != M. n)
			throw "Different matrix sizes in operator =.";
		int memSize = n * n;
		for (int i = 0; i < memSize; ++ i)
			tab [i] = M. tab [i];
		return *this;
	}

	/// The destructor which deallocates the memory.
	~flatMatrix () {delete [] tab;}

	/// The class that represents a single row of the matrix.
	class row
	{
	public:
		/// The constructor of a row of the matrix.
		row (int _offset, element *_v):
			offset (_offset), v (_v) {}

		/// Returns a reference to the element at the given position.
		element &operator [] (int j) {return v [offset + j];}

	protected:
		/// The offset in the vector of all the entries
		/// of the matrix.
		int offset;

		/// A reference to the vector that stores all the entries
		/// of the matrix.
		element *v;
	};

	/// Returns a row of the matrix.
	row operator [] (int i)
		{return row (n * i, tab);}

	/// The class that represents a constant single row of the matrix.
	class const_row
	{
	public:
		/// The constructor of a constant row of the matrix.
		const_row (int _offset, const element *_v):
			offset (_offset), v (_v) {}

		/// Returns a reference to the element at the given position.
		const element &operator [] (int m) {return v [offset + m];}

	protected:
		/// The offset in the vector of all the entries
		/// of the matrix.
		int offset;

		/// A reference to the vector that stores all the entries
		/// of the matrix.
		const element *v;
	};

	/// Returns a constant row of the matrix.
	const_row operator [] (int i ) const
		{return const_row (n * i, tab);}

	/// Clears all the entries of the matrix with the provided value.
	void clear (const element &elem)
	{
		int size = n * n;
		for (int i = 0; i < size; ++ i)
			tab [i] = elem;
		return;
	}

	/// Swaps the memory of two flat matrices.
	void swap (flatMatrix<element> &M)
	{
		int this_n = n;
		element *this_tab = tab;
		n = M. n;
		tab = M. tab;
		M. n = this_n;
		M. tab = this_tab;
		return;
	}

	/// Returns the address of the memory buffer with the elements
	/// of the matrix for reading only.
	const element *memory () const {return tab;}

	/// Returns the address of the memory buffer with the elements
	/// of the matrix for reading and writing.
	element *memory () {return tab;}

protected:
	/// The size of the matrix.
	int n;

	/// The array of elements.
	element *tab;

}; /* class flatMatrix */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_FLATMATR_H_ 

/// @}

