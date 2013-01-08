/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file localvar.h
///
/// This file contains the definition of a template of a class
/// whose object can define a local value of a given variable,
/// and restores the original value upon destruction.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on June 12, 2008. Last revision: June 13, 2008.


#ifndef _CAPD_HOMOLOGY_LOCALVAR_H_ 
#define _CAPD_HOMOLOGY_LOCALVAR_H_ 


namespace capd {
namespace homology {


// --------------------------------------------------
// -------------------- LOCALVAR --------------------
// --------------------------------------------------

/// Local variable guardian.
/// This template contains the definition of a class whose object
/// remembers the previous value of a variable provided upon initialization,
/// sets the new value, and restores the previous value upon destruction.
/// This corresponds to certain extent to a local variable in Perl.
template <class varType>
class local_var
{
public:
	/// The constructor of a local variable guardian.
	local_var (varType &_variable);

	/// The constructor of a local variable guardian
	/// which assigns a new value upon initialization.
	local_var (varType &_variable, const varType &_newValue);

	/// The destructor of a local variable guardian.
	~local_var ();

private:
	/// Reference to the global variable.
	varType &var;

	/// The original value of the variable which is going to be
	/// restored upon destruction of the guardian object.
	const varType value;

}; /* class local_var */

// --------------------------------------------------

template <class varType>
inline local_var<varType>::local_var (varType &_variable):
	var (_variable), value (_variable)
{
	return;
} /* local_var */

template <class varType>
inline local_var<varType>::local_var (varType &_variable,
	const varType &_newValue): var (_variable), value (_variable)
{
	_variable = _newValue;
	return;
} /* local_var */

template <class varType>
inline local_var<varType>::~local_var ()
{
	var = value;
	return;
} /* ~local_var */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_LOCALVAR_H_ 

/// @}

