/////////////////////////////////////////////////////////////////////////////
///
/// @file arg.h
///
/// This file contains the definition of a class which can be used
/// to parse the command line of a program and to set variables according
/// to the command-line arguments.
///
/// The way of using the features defined in this header file
/// is very simple and intuitive.
///
/// First, one must define in one's program an object
/// of the type "arguments" which will collect and process the command line.
///
/// Then one should use some of the several functions "arg",
/// "argswitch", and "arghelp" to bind various arguments with specific
/// variables. For example, 'arg (argObject, "i", increase, 1);'
/// makes the program react to the switch "-i" appearing in the command line
/// and sets the value of the variable "increase" to what follows "-i",
/// either without space, or after a space, but if no value is provided
/// then the default value "1" is used.
///
/// At the end of arguments' definitions, it is recommended to use
/// the function "arghelp (argObject);" to add the arguments typical
/// for the user asking the program to display help information
/// (like "--help"), but this step is not obligatory.
///
/// After all the arguments have been defined, one might also call
/// the function "argstreamprepare (argObject);" (which is actually
/// a macro) to set up some additional arguments related to the streams
/// of the class "outputstream" defined in "chomp/system/textfile.h".
/// In particular, this call adds the useful feature that if the user
/// adds the argument "--log filename" to the command-line then all the
/// output displayed to the screen (directed to "sout") is additionally
/// logged to the given file.
///
/// Eventually, one should call the method "analyze" of the arguments
/// object, e.g. "int argresult = argObject. analyze (argc, argv);",
/// followed by another macro "argstreamset ();" which sets the streams
/// defined with the macro "argstreamprepare".
///
/// The returned value "argresult" indicates what happened during the
/// processing of the command line arguments: 0 means "all good",
/// 1 means "help requested", and a negative value means
/// "some error(s) occurred".
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// You may want to include "textfile.h" and "timeused.h" before this file.
// Started on March 3, 2002. Last revision: March 9, 2007.


#ifndef _CAPD_AUXIL_ARG_H_
#define _CAPD_AUXIL_ARG_H_

//#include "capd/homology/config.h"

#include <iostream>
#include <iomanip>
#include <cstring>
#include <sstream>
#include <cctype>
#include <ctime>

namespace capd {
namespace auxil {

// the main front-end class defined in this file
class arguments;


// --------------------------------------------------
// -------------------- argflags --------------------
// --------------------------------------------------

/// This is a helper class which defines specific flags
/// indicating various types of command-line arguments
/// and the state of interpreting them.
class argflags
{
public:
	/// A list of specific names for the flags.
	enum names {obligatory = 0x01, hasdefault = 0x02,
		filled = 0x04, breakinterpreting = 0x08,
		toomany = 0x10, missingvalue = 0x20,
		readerror = 0x40, ignorevalue = 0x80};

	/// The constructor. All flags are initially cleared (unset).
	argflags (): n (0) {}

	/// The destructor.
	~argflags () {}

	/// Sets the given flag.
	void set (int flag) {n |= flag;}

	/// Unsets (clears) the given flag.
	void unset (int flag) {n &= ~flag;}

	/// Returns true if any of the given flags is set or false otherwise.
	bool get (int flag) const {return !!(n & flag);}

private:
	/// The interger variable that stores the flags.
	int n;

}; /* argflags */


// --------------------------------------------------
// ------------------- argelement -------------------
// --------------------------------------------------

/// This is a helper class which defines common properties
/// of a command-line argument bound with any type of a variable.
class argelement
{
public:
	/// The constructor.
	argelement (const char *_name);

	/// The destructor.
	virtual ~argelement ();

	/// Returns the name of the command-line argument.
	const char *getname () const;

	/// Returns the argument's value string from the argument string
	/// or returns 0 if it is not this argument.
	char *getvalue (char *str);

	/// Sets the value of this argument according to the string.
	/// If necessary, the next argument may be used.
	/// Returns: 0 = Ok, -1 = Error, 1 = next used.
	virtual int setvalue (char *str, char *next) = 0;

	/// Restores the previous argument value (except for tables).
	virtual void restore () = 0;

	/// Outputs the argument element to the output stream.
	virtual void show (std::ostream &out) const = 0;

	/// Resets the flags.
	void resetflags ();

	/// Sets the given flag.
	void set (int flag);

	/// Unsets (clears) the given flag.
	void unset (int flag);

	/// Returns the value of the given flag.
	bool get (int flag) const;

private:
	/// The argument name (without '-').
	/// This string dynamically allocated.
	char *name;

	/// The flags associated with this argument.
	argflags flags;

}; /* class argelement */

inline argelement::argelement (const char *_name): flags ()
{
	if (!_name || !*_name)
		name = NULL;
	else
	{
		name = new char [strlen (_name) + 1];
		strcpy (name, _name);
	}
	return;
} /* argelement::argelement */

inline argelement::~argelement ()
{
	if (name)
		delete [] name;
	return;
} /* argelement::~argelement */

inline const char *argelement::getname () const
{
	return name;
} /* argelement::getname */

inline void argelement::resetflags ()
{
	flags. unset (argflags::filled);
	flags. unset (argflags::readerror);
	flags. unset (argflags::toomany);
	flags. unset (argflags::missingvalue);
	return;
} /* argelement::resetflags */

inline void argelement::set (int flag)
{
	flags. set (flag);
	return;
} /* argelement::set */

inline void argelement::unset (int flag)
{
	flags. unset (flag);
	return;
} /* argelement::unset */

inline bool argelement::get (int flag) const
{
	return flags. get (flag);
} /* argelement::get */

inline std::ostream &operator << (std::ostream &out, const argelement &p)
{
	p. show (out);
	return out;
} /* operator << */


// --------------------------------------------------
// -------------------- argunit ---------------------
// --------------------------------------------------

/// This is a helper class which defines one command-line argument
/// which is bound with some specific variable.
/// It is an extension of the "argelement" class defined in terms
/// of a template whose parameter is the type of the variable
/// which is to be set based on the value provided in the command line.
template <class type>
class argunit: public argelement
{
public:
	/// The constructor of a command line argument bound with one
	/// variable.
	argunit (const char *_name, type &_value);

	/// The constructor of a command line argument bound with one
	/// variable which has a default value if none found in the
	/// command line.
	argunit (const char *_name, type &_value, type defaultvalue);

	/// The constructor of a command line argument bound with
	/// an array of the given size.
	argunit (const char *_name, type *_value, int &_count,
		int _size);

	/// The constructor of a command line argument bound with
	/// an array of the given size; a default value is provided.
	argunit (const char *_name, type *_value, int &_count,
		int _size, type defaultvalue);

	/// Sets the argument value from the text string.
	int setvalue (char *str, char *next);

	/// Restores the previous argument value (except for tables).
	void restore ();

	/// Displays the value and some information.
	void show (std::ostream &out) const;

private:
	/// A reference to the variable which is bound to this
	/// command line argument.
	type &value;

	/// The default value of the variable if any.
	type defaultvalue;

	/// The original value of the variable (before reading the
	/// command line).
	type previousvalue;

	/// A pointer to the array bound with the variable.
	type *table;

	/// A pointer to the number of elements currently present
	/// in the array.
	int *count;

	/// The initial value of the number of elements in the array.
	int previouscount;

	/// The size of the array if any.
	int size;

}; /* class argunit */

template <class type>
inline argunit<type>::argunit (const char *_name, type &_value):
	argelement (_name), value (_value), previousvalue (_value),
	table (NULL)
{
	return;
} /* argunit<type>::argunit */

template <class type>
inline argunit<type>::argunit (const char *_name, type &_value,
	type _defaultvalue):
	argelement (_name), value (_value), defaultvalue (_defaultvalue),
	previousvalue (_value), table (NULL)
{
	set (argflags::hasdefault);
	return;
} /* argunit<type>::argunit */

template <class type>
inline argunit<type>::argunit (const char *_name, type *_value,
	int &_count, int _size):
	argelement (_name), value (*_value), previousvalue (*_value),
	table (_value), count (&_count), previouscount (_count),
	size (_size)
{
	return;
} /* argunit<type>::argunit */

template <class type>
inline argunit<type>::argunit (const char *_name, type *_value,
	int &_count, int _size, type _defaultvalue):
	argelement (_name), value (*_value), defaultvalue (_defaultvalue),
	previousvalue (*_value), table (_value),
	count (&_count), previouscount (_count), size (_size)
	
{
	set (argflags::hasdefault);
	return;
} /* argunit<type>::argunit */

/// A template for reading a variable from a string.
/// Returns 0 on success, -1 on failure.
template <class type>
inline int readfromstring (char *str, type &t)
{
	std::istringstream s (str);
	try
	{
		s >> t;
		if (!s)
			return -1;
	}
	catch (...)
	{
		return -1;
	}
	return 0;
} /* readfromstring */

/// A specialization of the above template for interpreting a string
/// as a string (no processing is necessary).
inline int readfromstring (char *str, char *&t)
{
	t = str;
	return 0;
} /* readfromstring */

/// A specialization of the above template for interpreting a string
/// as a const string (no processing is necessary).
// This function was added by Tomek Kapela. His remark
// justifying this addition: "e.g to replace default constant C strings".
inline int readfromstring (char *str, const char *&t)
{
	t = str;
	return 0;
} /* readfromstring */

/// A specialization of the above template for reading a bool type.
inline int readfromstring (char *str, bool &t)
{
	switch (*str)
	{
		case 'T':
		case 't':
		case 'Y':
		case 'y':
		case '1':
			t = true;
			return 0;
		case 'F':
		case 'f':
		case 'N':
		case 'n':
		case '0':
			t = false;
			return 0;
		default:
			return -1;
	}
} /* readfromstring */

template <class type>
inline int argunit<type>::setvalue (char *str, char *next)
{
	// determine the string from which the value should be read
	int usenext = 0;
	char *s;
	if (str && *str)
		s = str;
	else
	{
		if (next && *next && ((*next != '-') ||
			std::isdigit (next [1])))
		{
			s = next;
			usenext = 1;
		}
		else
			s = NULL;
	}

	// read the element from the string if available
	int result = -1;
	type element;
	if (s)
		result = readfromstring (s, element);

	// if could not read the string, try the default value
	if (result < 0)
	{
		if (get (argflags::hasdefault))
		{
			element = defaultvalue;
			usenext = 0;
		}
		else
		{
			if (s)
				set (argflags::readerror);
			else
				set (argflags::missingvalue);
			return 0;
		}
	}

	// put the element to its place
	if (table)
		// if there is still room in the table, put the element there
		if (*count < size)
			table [(*count) ++] = element;
		// if the table is full, indicate it
		else
		{
			set (argflags::toomany);
			set (argflags::filled);
		}
	else
	{
		value = element;
		set (argflags::filled);
	}

	return usenext;
} /* argunit<type>::setvalue */

template <class type>
void argunit<type>::restore ()
{
	if (!table)
		value = previousvalue;
	else
		*count = previouscount;
	resetflags ();
	return;
} /* argunit<type>::restore */

template <class type>
void argunit<type>::show (std::ostream &out) const
{
	if (get (argflags::obligatory))
		out << "Oblig. ";
	if (getname () && *getname ())
	{
		if (get (argflags::ignorevalue))
			out << "Switch";
		else
			out << "Param.";
		out << " '-" << getname () << "'";
	}
	else
		out << "Word";
	if (!table && get (argflags::filled))
		out << " set to '" << value << "'";
	else if (table && *count)
	{
		for (int i = 0; i < *count; ++ i)
			out << (i ? ", " : " set to '") << table [i];
		out << "'";
		if (get (argflags::toomany))
			out << " [too many!]";
	}
	else
		out << " not found";
	if (get (argflags::hasdefault))
		out << " (default: '" << defaultvalue << "')";
	else
		out << " (no default value)";
	out << "." << std::endl;
	return;
} /* argunit<type>::show */


// --------------------------------------------------
// ------------------- arguments --------------------
// --------------------------------------------------

/// The objects of this class gather the expected command-line arguments
/// and decode them. It is recommended that you use the various functions
/// called "arg" to enqueue the arguments into the list of arguments.
/// When the list is complete, one just calls the "analyze" method of
/// the class. Detailed instructions are gathered in the "arg.txt" file.
/// The program "argtest.cpp" and most CHomP programs very well illustrate
/// how to use various features of this class.
class arguments
{
public:
	/// The default constructor.
	arguments ();

	/// The destructor.
	~arguments ();

	/// Adds an argument to the end of the list.
	void add (argelement *p);

	/// Removes all the arguments with this name from the list
	/// and return the number of removed items.
	int remove (char *name);

	/// Analyzes the arguments from the command line strings.
	/// Returns a negative value in case of error (the negation
	/// of the number of errors) and displays error messages
	/// to the given output stream. Returns 1 if it is requested
	/// to stop the program (and show help information, for instance).
	/// Returns 0 otherwise.
	int analyze (int argc, char *argv [],
		std::ostream &out = std::cerr);

	/// Resets the flags and returns previous argument values
	/// (except for tables).
	void reset ();

	/// Displays the arguments actually decoded (for debugging purpose).
	friend std::ostream &operator << (std::ostream &out,
		arguments &p);

private:
	/// The number of arguments in the table.
	int n;

	/// The allocated length of the table of arguments.
	int length;

	/// The table of pointers to specific arguments.
	argelement **tab;

	/// Increases the tables if necessary.
	void inctable ();

}; /* class arguments */

inline arguments::arguments ()
{
	n = 0;
	length = 0;
	tab = NULL;
	return;
} /* arguments::arguments */

inline void arguments::add (argelement *p)
{
	inctable ();
	tab [n ++] = p;
	return;
} /* arguments::add */

// --------------------------------------------------

/// Adds a command line argument. The actual argument name consists of the
/// dash and its name provided to the function. If name == 0, then the value
/// of this argument is read directly from the command line without any
/// preceding string. The value variable is filled in by the value read
/// from the command line string using the operator >>.
template <class type>
inline void arg (arguments &a, const char *name, type &value)
{
	argunit<type> *p = new argunit<type> (name, value);
	a. add (p);
	return;
} /* arg */

/// Adds a command line argument with a default value. The name must be
/// nonempty. If the name of the argument appears but its value is not
/// specified, then the default value is used instead.
template <class type>
inline void arg (arguments &a, const char *name, type &value,
	type defaultvalue)
{
	argunit<type> *p = new argunit<type> (name, value, defaultvalue);
	a. add (p);
	return;
} /* arg */

/// A specialization of the above for C-style strings.
inline void arg (arguments &a, const char *name, char *&value,
	const char *defaultvalue)
{
	argunit<char *> *p =
		new argunit<char *> (name, value,
			const_cast<char *> (defaultvalue));
	a. add (p);
	return;
} /* arg */

/// Adds a command line argument whose repeated occurrences fill in
/// consecutive elements of the given array. The counter indicates
/// the position in the array. The given size of the array will
/// not be exceeded.
template <class type>
inline void arg (arguments &a, const char *name, type *value,
	int &count, int size)
{
	argunit<type> *p = new argunit<type> (name, value, count, size);
	a. add (p);
	return;
} /* arg */

/// A version of the above with a default value of the arguments.
template <class type>
inline void arg (arguments &a, const char *name, type *value,
	int &count, int size, type defaultvalue)
{
	argunit<type> *p = new argunit<type> (name, value, count, size,
		defaultvalue);
	a. add (p);
	return;
} /* argoblig */

/// Defines an obligatory command line argument. If this argument
/// does not appear, then an error is displayed and error code is returned
/// by the analysis procedure.
template <class type>
inline void argoblig (arguments &arg, const char *name, type &value)
{
	argunit<type> *p = new argunit<type> (name, value);
	p -> set (argflags::obligatory);
	arg. add (p);
	return;
} /* argoblig */

/// A version of the above with the default value provided.
template <class type>
inline void argoblig (arguments &arg, const char *name, type &value,
	type defaultvalue)
{
	argunit<type> *p = new argunit<type> (name, value, defaultvalue);
	p -> set (argflags::obligatory);
	arg. add (p);
	return;
} /* argoblig */

/// A version of the above for reading an array of argument values.
inline void argoblig (arguments &arg, const char *name, char *&value,
	const char *defaultvalue)
{
	argunit<char *> *p =
		new argunit<char *> (name, value, (char *) defaultvalue);
	p -> set (argflags::obligatory);
	arg. add (p);
	return;
} /* argoblig */

/// Adds an argument whose appearence interrupts the analysis of the
/// command line and makes the analyzing function return the value of 1.
/// This is useful for arguments whose appearence should make the program
/// ignore all the remaining arguments, e.g., to display help information.
template <class type>
inline void argbreak (arguments &arg, const char *name, type &value)
{
	argunit<type> *p = new argunit<type> (name, value);
	p -> set (argflags::breakinterpreting);
	p -> set (argflags::ignorevalue);
	arg. add (p);
	return;
} /* argbreak */

/// A version of the above with the default value provided.
template <class type>
inline void argbreak (arguments &arg, const char *name, type &value,
	type defaultvalue)
{
	argunit<type> *p = new argunit<type> (name, value, defaultvalue);
	p -> set (argflags::breakinterpreting);
	p -> set (argflags::ignorevalue);
	arg. add (p);
	return;
} /* argbreak */

/// A version of the above for the C-style string.
inline void argbreak (arguments &arg, const char *name, char *&value,
	const char *defaultvalue)
{
	argunit<char *> *p =
		new argunit<char *> (name, value, (char *) defaultvalue);
	p -> set (argflags::breakinterpreting);
	p -> set (argflags::ignorevalue);
	arg. add (p);
	return;
} /* argbreak */

/// A version of the above which ignores the value of the argument.
inline void argbreak (arguments &arg, const char *name)
{
	char *dummystring = NULL;
	argunit<char *> *p = new argunit<char *> (name, dummystring);
	p -> set (argflags::breakinterpreting);
	p -> set (argflags::ignorevalue);
	arg. add (p);
	return;
} /* argbreak */

/// Defines a command line argument which is a switch, that is, there is no
/// value given for it in the command line. The appearence of this argument
/// sets the predefined default value to the given variable.
template <class type>
inline void argswitch (arguments &arg, const char *name, type &value,
	const type &defaultvalue)
{
	argunit<type> *p = new argunit<type> (name, value, defaultvalue);
	p -> set (argflags::ignorevalue);
	arg. add (p);
	return;
} /* argswitch */

/// A version of the above for the C-style string.
inline void argswitch (arguments &arg, const char *name, char *&value,
	const char *defaultvalue)
{
	argunit<char *> *p =
		new argunit<char *> (name, value, (char *) defaultvalue);
	p -> set (argflags::ignorevalue);
	arg. add (p);
	return;
} /* argswitch */

/// Defines an ignored switch (no value is set when this argument appears).
inline void argswitch (arguments &arg, const char *name)
{
	char *dummystring = NULL;
	argunit<char *> *p = new argunit<char *> (name, dummystring);
	p -> set (argflags::ignorevalue);
	arg. add (p);
	return;
} /* argswitch */

/// Adds the typical arguments which should make the program display help
/// information. If help is requested, the command line analysis is
/// interrupted, and the procedure returns the value 1.
inline void arghelp (arguments &a)
{
	argbreak (a, "?");
	argbreak (a, "h");
	argbreak (a, "H");
	argbreak (a, "-help");
	return;
} /* arghelp */

/// Returns the entire command line as a single string.
inline std::string commandline (int argc, char *argv [])
{
  std::string s;
  for (int i = 0; i < argc; ++ i)
  {
    if (i)
      s += ' ';
    s += argv [i];
  }
  return s;
} /* commandline */

/// Retrieves the current time as a pointer to a C-style string.
inline const char *currenttime (void)
{
  std::time_t t;
  std::time (&t);
  return std::asctime (std::localtime (&t));
} /* currenttime */

// --------------------------------------------------

#ifdef CAPD_OUTPUTSTREAM

/// Adds typical command line arguments for manipulating output streams.
/// This is an internal function used by the macro "algstreamprepare".
inline void argstreams (arguments &a, char *&logfilename, char *&seqfilename,
	bool &quiet, bool &debug)
{
	arg (a, "-log", logfilename);
	arg (a, "-seq", seqfilename);
	argswitch (a, "-quiet", quiet, true);
	argswitch (a, "-debug", debug, true);
	return;
} /* argstreams */

/// Sets the parameters of the output streams depending on the
/// file names acquired from the command line.
/// This is an internal function used by the macro "algstreamset".
inline void setstreams (const char *logfilename, char *seqfilename,
	bool quiet, bool debug)
{
	if (debug)
	  capd::sbug. show = true;
	if (quiet)
	{
	  capd::sout. show = false;
		capd::scon. show = false;
		capd::sbug. show = false;
	}
	if (logfilename)
	{
	  capd::slog. logfile (logfilename);
		capd::slog. keepforever ();
		capd::sout. logfile (slog);
		capd::serr. logfile (slog);
		if (debug)
		  capd::sbug. logfile (slog);
	}
	if (seqfilename)
	  capd::sseq. logfile (seqfilename);
#ifdef CAPD_TIMEUSED
	program_time = sout;
#endif
	return;
} /* setstreams */

#ifndef algstreamprepare
/// This macrodefinition sets up command line arguments for the analysis
/// of typical arguments related to the output streams defined in the
/// module "textfile.h".
#define argstreamprepare(a) \
char *arg_logfilename = NULL; \
char *arg_seqfilename = NULL; \
char *arg_computername = NULL; \
bool arg_quiet = false; \
bool arg_debug = false; \
arg (a, "-comp", arg_computername); \
argstreams (a, arg_logfilename, arg_seqfilename, arg_quiet, arg_debug);
#endif

#ifndef argstreamset
/// This macrodefinition sets up the streams defined in the module
/// "textfile.h", based on the analyzed command line arguments
/// defined by the macrodefinition "algstreamprepare(a)".
#define argstreamset() \
setstreams (arg_logfilename, arg_seqfilename, arg_quiet, arg_debug); \
capd::slog << commandline (argc, argv) << "\n\n"; \
if (arg_computername) capd::slog << "Running on " << arg_computername << ". "; \
capd::slog << "Start time: " << currenttime () << '\n';
#endif

#endif
/* */


} // namespace auxil
} // namespace capd

#endif // _CAPD_AUXIL_ARG_H_

/// @}

