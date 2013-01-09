/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file fibheap.h
///
/// This file contains the definition of a Fibonacci heap
/// optimized for good memory usage.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on August 13, 2007. Last revision: January 23, 2010.


#ifndef _CAPD_HOMOLOGY_FIBHEAP_H_ 
#define _CAPD_HOMOLOGY_FIBHEAP_H_ 


#include "capd/homology/multitab.h"
//#include "capd/homology/pool.h"


namespace capd {
namespace homology {


// --------------------------------------------------
// ----------------- FIBONACCI HEAP -----------------
// --------------------------------------------------

/// This template contains the definition of a Fibonacci heap
/// that can be used as an efficient priority queue,
/// for example, in the Dijxtra graph algorithm.
/// Note that if the "Delete" function is used then the elements
/// must support the arithmetic subtraction of 1 to create a value
/// that is strictly smaller than the given one (like the integers).
/// This is a very specialized implementation which does not support
/// the "Union" operation.
/// Moreover, the "Delete" or "ExtractMinimum" don't actually free the
/// memory used by the deleted elements in this implementation.
/// See the description of the functions in this class for more information.
template <class element>
class FibonacciHeap
{
public:
	/// The type of a pointer to a node in the Fibonacci heap.
	typedef int_t NodePtr;

	/// The value used for a NULL pointer.
	static const int_t NullPtr;

private:
	/// The structure that holds a graph node for the graph
	/// representation of a Fibonacci heap.
	struct Node
	{
		/// The value of the element that is used to compare
		/// the elements.
		element key;

		/// A mark bit which indicates whether the node has lost
		/// a child since the last time it was made a child of
		/// another node.
		bool mark;

		/// The degree of the node, i.e., the number of its children.
		/// Nodes that have been removed from the heap have the
		/// degree set to -1.
		int_t degree;

		/// The number of this node 
		int_t number;

		/// A pointer to the parent node.
		NodePtr parent;

		/// A pointer to one of the children nodes.
		NodePtr child;

		/// A pointer to the left sibling node.
		NodePtr left;

		/// A pointer to the right sibling node.
		NodePtr right;
	};

public:
	/// The constructor of an empty Fibonacci heap.
	/// The maximal number of elements may be given if it is known.
	FibonacciHeap (int_t maxSize = 0);

	/// The destructor of a Fibonacci heap.
	~FibonacciHeap ();

	/// Inserts an element into the heap.
	/// Returns the number of the node which is to be used
	/// for decreasing the key or removing this element from the heap.
	/// The numbers are returned in the ascending order, starting at 0.
	int_t Insert (const element &value);

	/// Returns the number of the node that contains the minimum.
	/// This is the number given to the node at its insertion.
	int_t Minimum () const;

	/// Returns the value of the node with the given number.
	const element &Value (int_t number) const;

	// Adds another heap to this one. Destroys the other one.
	// WARNING: Because of the node memory allocation strategy used
	// in this implementation of Fibonacci heaps, the complexity
	// of computing the union is O(n) instead of O(1).
	// Even worse, this operation is not yet implemented... Sorry!
//	void Union (FibonacciHeap<element> &h);

	/// Extracts the minimum from the heap. The element is removed
	/// from the heap and its value is returned.
	element ExtractMinimum ();

	/// Decreases the key of the element identified by the given number
	/// to the new value.
	void DecreaseKey (int_t number, const element &value);

	/// Removes the element identified by the given number from the heap.
	void Delete (int_t number);

private:
	/// The copy constructor is not allowed.
	FibonacciHeap (const FibonacciHeap<element> &);

	/// The assignment operator is not allowed.
	FibonacciHeap<element> &operator = (const FibonacciHeap<element> &);

	/// A pointer to the minimal element in the list of roots.
	NodePtr minRoot;

	/// The total number of nodes inserted to the heap and allocated
	/// in the multitable "nodes".
	int_t nodeCount;

	/// The array of nodes which hold the elements inserted to the heap
	/// in this order. The indices of these elements are returned
	/// while inserting them to the heap and can be used to access
	/// these nodes directly, e.g., in order to decrease their keys
	/// or delete them from the heap.
	multitable<Node> nodes;

	/// The minimal value that ever appeared in the heap. This value
	/// minus 1 is used as a substitute for the minus infinity while
	/// deleting elements from the heap with the use of the "Delete"
	/// function.
	element minValue;

	// The pool of nodes used for the Fibonacci heap.
//	static pool<typename FibonacciHeap<element>::Node> *p;

	// The number of Fibonacci heaps in use.
//	static int_t heapsInUse;

	/// Consolidates the Fibonacci heap by joining roots of equal degree.
	void Consolidate ();

	/// An auto-expandable array used by the "Consolidate" procedure.
	multitable<NodePtr> auxArray;

	/// The size of the prepared data in the array.
	int_t arrayPrepared;

	/// Cuts the tree.
	void Cut (const typename FibonacciHeap<element>::NodePtr &x,
		const typename FibonacciHeap<element>::NodePtr &y);

	/// Does a cascading cut of the tree.
	void CascadingCut (typename FibonacciHeap<element>::NodePtr y);

	/// Shows a graph starting at the given node using DFS.
	void showGraph (std::ostream &out, int_t depth,
		const typename FibonacciHeap<element>::NodePtr &x) const;

public:
	/// Operator << shows the heap to the output stream.
	/// Essentially, this might be useful for debugging purposes only.
	friend inline std::ostream &operator << (std::ostream &out,
		const FibonacciHeap<element> &h)
	{
		out << "Fibonacci heap (min root = " << h. minRoot << "):\n";
		NodePtr rootPtr = h. minRoot;
		if (rootPtr == NullPtr)
			return out;
		do
		{
			h. showGraph (out, 0, rootPtr);
			rootPtr = h. nodes [rootPtr]. right;
		} while (rootPtr != h. minRoot);
		return out;
	} /* operator << */

}; /* class FibonacciHeap */

template <class element>
const int_t FibonacciHeap<element>::NullPtr (-1);

//template <class element>
//pool<typename FibonacciHeap<element>::Node> *FibonacciHeap<element>::p = 0;

//template <class element>
//int_t FibonacciHeap<element>::heapsInUse = 0;

// --------------------------------------------------

template <class element>
void FibonacciHeap<element>::showGraph (std::ostream &out, int_t depth,
	const typename FibonacciHeap<element>::NodePtr &x) const
{
	// show this node
	for (int_t i = 0; i < depth; ++ i)
		out << "|   ";
	out << "+-- [" << nodes [x]. number << ": " << nodes [x]. key << "]";
	if (nodes [x]. left != NullPtr)
		out << " left=" << nodes [x]. left;
	if (nodes [x]. right != NullPtr)
		out << " right=" << nodes [x]. right;
	if (nodes [x]. parent != NullPtr)
		out << " parent=" << nodes [x]. parent;
	if (nodes [x]. child != NullPtr)
		out << " child=" << nodes [x]. child;
	out << " deg=" << nodes [x]. degree << "\n";

	// show all the children trees
	NodePtr child = nodes [x]. child;
	if (child == NullPtr)
		return;
	do
	{
		showGraph (out, depth + 1, child);
		child = nodes [child]. right;
	} while (child != nodes [x]. child);
	return;
} /* FibonacciHeap::showGraph */

template <class element>
inline FibonacciHeap<element>::FibonacciHeap (int_t maxSize):
	minRoot (NullPtr), nodeCount (0), nodes (maxSize), arrayPrepared (0)
{
	// allocate a new pool for elements if this is the first heap
//	if (!heapsInUse)
//		p = new pool<typename FibonacciHeap<element>::Node>;

	// increase the number of heaps in use
//	++ heapsInUse;

	return;
} /* FibonacciHeap::FibonacciHeap */

template <class element>
inline FibonacciHeap<element>::~FibonacciHeap ()
{
	// decrease the number of heaps in use
//	-- heapsInUse;

	// delete the pool for elements if this was the last heap
//	if (!heapsInUse)
//		delete p;

	return;
} /* FibonacciHeap::~FibonacciHeap */

template <class element>
inline FibonacciHeap<element>::FibonacciHeap (const FibonacciHeap<element> &)
{
	throw "Copy constructor for a Fibonacci heap not implemented.";
	return;
} /* FibonacciHeap::FibonacciHeap */

template <class element>
inline FibonacciHeap<element> &FibonacciHeap<element>::operator =
	(const FibonacciHeap<element> &)
{
	throw "Assignment operator for a Fibonacci heap not implemented.";
	return *this;
} /* FibonacciHeap::operator = */

template <class element>
inline int_t FibonacciHeap<element>::Insert (const element &value)
{
	// allocate memory for the new node
	NodePtr nodePtr = nodeCount;

	// update the minimal value
	if (!nodeCount)
		minValue = value;
	else if (value < minValue)
		minValue = value;

	// fill in the fields of the new node
	Node &node = nodes [nodePtr];
	node. key = value;
	node. mark = false;
	node. degree = 0;
	node. number = nodeCount;
	node. parent = NullPtr;
	node. child = NullPtr;

	// insert the node to the unordered bidirectional list of roots
	if (minRoot == NullPtr)
	{
		node. left = nodePtr;
		node. right = nodePtr;
	}
	else
	{
		node. left = nodes [minRoot]. left;
		node. right = minRoot;
		nodes [node. left]. right = nodePtr;
		nodes [node. right]. left = nodePtr;
	}

	// make a correction to the pointer to the minimal root if necessary
	if ((minRoot == NullPtr) || (value < nodes [minRoot]. key))
		minRoot = nodePtr;

	// return the number of the new node and increase the number of nodes
	return nodeCount ++;
} /* FibonacciHeap::Insert */

template <class element>
inline int_t FibonacciHeap<element>::Minimum () const
{
	return minRoot;
} /* FibonacciHeap::Minimum */

template <class element>
inline const element &FibonacciHeap<element>::Value (int_t number) const
{
	return nodes [number]. key;
} /* FibonacciHeap::Value */

/*
template <class element>
inline void FibonacciHeap<element>::Union (FibonacciHeap<element> &h)
{
	// if the other heap is empty, then do nothing
	if (h. minRoot == NullPtr)
		return;

	// if this heap is empty, then just copy the data
	if (minRoot == NullPtr)
	{
		minRoot = h. minRoot;
		nodeCount = h. nodeCount;
		minValue = h. minValue;
		return;
	}

	// copy the nodes from the other heap to this one and update links
	// TODO

	// join the root lists
	// TODO

	// update the node count
	nodeCount += h. nodeCount;

	// update the minimal key value
	if (h. minValue < minValue)
		minValue = h. minValue;

	// make the other heap empty
	h. minRoot = NullPtr;
	h. nodeCount = 0;
	throw "The union of Fibonacci heaps not implemented, yet.";
	return;
}*/ /* FibonacciHeap::Union */

template <class element>
inline void FibonacciHeap<element>::Consolidate ()
{
	// do nothing if the heap is empty
	if (minRoot == NullPtr)
		return;

	// for each node in the root list of the heap...
	NodePtr node = minRoot;
	int_t maxDegree = 0;
	do
	{
		// take the node for the loop and get its degree
		NodePtr x = node;
		int_t d = nodes [x]. degree;

		// prepare the next node from the root list for the next time
		node = nodes [node]. right;

		// expand the auxiliary array if necessary
		while (arrayPrepared <= d)
			auxArray [arrayPrepared ++] = NullPtr;

		// update the strict upper limit on the degree used
		if (maxDegree <= d)
			maxDegree = d + 1;

		// join this tree with another one of the same degree if any
		while (auxArray [d] != NullPtr)
		{
			// take the node of the same degree as x
			NodePtr y = auxArray [d];

			// swap the node pointers if necessary
			if (nodes [y]. key < nodes [x]. key)
			{
				NodePtr tmp = x;
				x = y;
				y = tmp;
			}

			// clear the mark of the node y
			nodes [y]. mark = false;

			// make the node y a child of the node x
			nodes [y]. parent = x;
			NodePtr child = nodes [x]. child;
			if (child == NullPtr)
			{
				nodes [x]. child = y;
				nodes [y]. left = y;
				nodes [y]. right = y;
			}
			else
			{
				nodes [y]. left = child;
				nodes [y]. right = nodes [child]. right;
				nodes [child]. right = y;
				nodes [nodes [y]. right]. left = y;
			}
			++ nodes [x]. degree;

			// clear the entry which stored the node of degree d
			auxArray [d] = NullPtr;

			// increase the degree to the degree of x
			++ d;

			// expand the auxiliary array if necessary
			if (arrayPrepared <= d)
				auxArray [arrayPrepared ++] = NullPtr;

			// update the strict upper limit on the degree used
			if (maxDegree <= d)
				maxDegree = d + 1;
		}

		// put this node in the array
		auxArray [d] = x;

	} while (node != minRoot);

	// reconstruct the root list from the auxiliary array
	minRoot = NullPtr;
	for (int_t d = 0; d < maxDegree; ++ d)
	{
		// skip entries of the array which don't point to nodes
		if (auxArray [d] == NullPtr)
			continue;

		// take the node pointer of the array
		NodePtr nodePtr = auxArray [d];
		auxArray [d] = NullPtr;
		Node &node = nodes [nodePtr];

		// link this node to the root list
		if (minRoot == NullPtr)
		{
			node. left = nodePtr;
			node. right = nodePtr;
		}
		else
		{
			node. left = minRoot;
			node. right = nodes [minRoot]. right;
			nodes [node. left]. right = nodePtr;
			nodes [node. right]. left = nodePtr;
		}

		// update the pointer to the minimal root node if necessary
		if ((minRoot == NullPtr) ||
			(node. key < nodes [minRoot]. key))
		{
			minRoot = nodePtr;
		}
	}
	return;
} /* FibonacciHeap::Consolidate */

template <class element>
inline element FibonacciHeap<element>::ExtractMinimum ()
{
	// determine the node with the minimum to extract
	NodePtr nodePtr = minRoot;
	Node &node = nodes [minRoot];

	// make the children of the node become root nodes
	// and attach them to the root list
	NodePtr child = node. child;
	if (child != NullPtr)
	{
		// clear the child pointer in the parent
		node. child = NullPtr;

		// clear the parent pointers in the children
		while (nodes [child]. parent != NullPtr)
		{
			nodes [child]. parent = NullPtr;
			child = nodes [child]. right;
		}

		// attach the children to the root list
		NodePtr leftChild = child;
		NodePtr rightChild = nodes [child]. right;
		NodePtr leftRoot = nodePtr;
		NodePtr rightRoot = node. right;
		nodes [leftRoot]. right = rightChild;
		nodes [rightRoot]. left = leftChild;
		nodes [leftChild]. right = rightRoot;
		nodes [rightChild]. left = leftRoot;
	}

	// make the min root pointer point at any other node
	// and remove the node from the root list
	if (node. right != nodePtr)
	{
		minRoot = node. right;
		nodes [minRoot]. left = node. left;
		nodes [node. left]. right = minRoot;
	}
	else
		minRoot = NullPtr;

	// reset the fields in the node to avoid any confusion in the future
	node. left = NullPtr;
	node. right = NullPtr;
	node. parent = NullPtr;
	node. child = NullPtr;
	node. degree = -1;

	// consolidate the heap
	Consolidate ();

	return node. key;
} /* FibonacciHeap::ExtractMinimum */

template <class element>
inline void FibonacciHeap<element>::Cut
	(const typename FibonacciHeap<element>::NodePtr &x,
	const typename FibonacciHeap<element>::NodePtr &y)
{
	// remove x from the children of y:
	// case 1: if x is the only child of y
	nodes [x]. parent = NullPtr;
	if (nodes [x]. right == x)
	{
		nodes [y]. child = NullPtr;
	}
	//case 2: if there are also other children of y
	else
	{
		NodePtr leftChild = nodes [x]. left;
		NodePtr rightChild = nodes [x]. right;
		nodes [y]. child = rightChild;
		nodes [leftChild]. right = rightChild;
		nodes [rightChild]. left = leftChild;
	}

	// update the degree of y
	-- nodes [y]. degree;

	// add x to the root list of the heap
	NodePtr leftRoot = minRoot;
	NodePtr rightRoot = nodes [minRoot]. right;
	nodes [x]. left = leftRoot;
	nodes [x]. right = rightRoot;
	nodes [leftRoot]. right = x;
	nodes [rightRoot]. left = x;

	// clear the marking of the node x if any
	nodes [x]. mark = false;

	return;
} /* FibonacciHeap::Cut */

template <class element>
inline void FibonacciHeap<element>::CascadingCut
	(typename FibonacciHeap<element>::NodePtr y)
{
	// do the cascading cut while the node has a parent
	while (!(nodes [y]. parent == NullPtr))
	{
		// if this is the first time the node lost its child,
		// then just mark the node and exit the cascading cut
		if (!nodes [y]. mark)
		{
			nodes [y]. mark = true;
			return;
		}

		// cut the node and continue the cascading cut
		// with its parent
		NodePtr z = nodes [y]. parent;
		Cut (y, z);
		y = z;
	}
	return;
} /* FibonacciHeap::CascadingCut */

template <class element>
inline void FibonacciHeap<element>::DecreaseKey (int_t number,
	const element &value)
{
	// translate the number to a node pointer
	NodePtr x (number);

	// ignore this action if the node is no longer in the heap
	if (nodes [x]. degree == -1)
		return;

	// update the minimal value in the heap
	if (value < minValue)
		minValue = value;

	// update the value of the node
	nodes [x]. key = value;

	// cut the tree so that the node x is in the root list
	NodePtr y = nodes [x]. parent;
	if ((y != NullPtr) && (value < nodes [y]. key))
	{
		Cut (x, y);
		CascadingCut (y);
	}

	// update the pointer to the minimal node in the root list
	if (value < nodes [minRoot]. key)
		minRoot = x;

	return;
} /* FibonacciHeap::DecreaseKey */

template <class element>
inline void FibonacciHeap<element>::Delete (int_t number)
{
	element value = minValue;
	DecreaseKey (number, value - 1);
	ExtractMinimum ();
	minValue = value;
	return;
} /* FibonacciHeap::Delete */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_FIBHEAP_H_ 

/// @}

