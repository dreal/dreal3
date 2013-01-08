/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file words.h
///
/// This file contains a definition of the class "word" which is used
/// to store a string and has some additional properties.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on May 5, 2002. Last revision: February 21, 2007.


#ifndef _CAPD_HOMOLOGY_WORDS_H_ 
#define _CAPD_HOMOLOGY_WORDS_H_ 

#include "capd/homology/config.h"
#include "capd/homology/integer.h"
#include "capd/homology/textfile.h"
#include "capd/homology/hashsets.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <fstream>
#include <sstream>

namespace capd {
namespace homology {


// the data types defined within this file
class word;

/// The default type of a set of words.
typedef hashedset<word> words;


// --------------------------------------------------
// ---------------------- word ----------------------
// --------------------------------------------------

/// A word, that is, a string with very few properties.
class word
{
public:
	/// Default constructor of an empty word.
	word ();

	/// Constructor of a word based on a given C-style string.
	word (const char *s);

	/// Copy constructor.
	word (const word &w);

	/// Destructor.
	~word ();

	/// Assignment operator.
	word &operator = (const word &w);

	/// Returns the length of the word (without the ending zero char).
	int length () const;

	/// Returns a pointer to the contents of the word.
	const char *text () const;

	/// Returns a pointer to the contents of the word.
	operator const char * () const;

	/// Word concatenation operator.
	word &operator += (const word &w);

	/// Word concatenation operator.
	word operator + (const word &w) const;

	/// Returns the value of the number contained in the word;
	/// allows a preceding '+'.
	operator int () const;

private:
	/// The length of the word (without the terminating zero character).
	int len;

	/// A memory buffer containing the word.
	char *txt;

}; /* class word */

// --------------------------------------------------

inline word::word ()
{
	len = 0;
	txt = NULL;
	return;
} /* word::word */

inline word::word (const char *s)
{
	len = s ? strlen (s) : 0;
	if (!len)
		txt = NULL;
	else
	{
		txt = new char [len + 1];
		if (!txt)
			throw "Not enough memory to create a word.";
		strcpy (txt, s);
	}
	return;
} /* word::word */

inline word::word (const word &w)
{
	len = w. len;
	if (!len)
		txt = NULL;
	else
	{
		txt = new char [len + 1];
		if (!txt)
			throw "Not enough memory to copy a word.";
		strcpy (txt, w. txt);
	}
	return;
} /* word::word */

inline word::~word ()
{
	if (txt)
		delete [] txt;
	return;
} /* word::~word */

inline word &word::operator = (const word &w)
{
	if (txt)
		delete [] txt;
	len = w. len;
	if (w. txt)
	{
		txt = new char [len + 1];
		if (!txt)
			throw "Not enough memory to copy a word.";
		strcpy (txt, w. txt);
	}
	else
		txt = NULL;
	return *this;
} /* operator = */

inline int word::length () const
{
	return len;
} /* length */

inline const char *word::text () const
{
	return txt;
} /* text */

inline word::operator const char * () const
{
	return txt;
} /* operator int */

inline word &word::operator += (const word &w)
{
	if (!len)
	{
		*this = w;
		return *this;
	}
	if (!w. len)
		return *this;
	int newlen = len + w. len;
	char *newtxt = new char [newlen + 1];
	strcpy (newtxt, txt);
	strcat (newtxt, w. txt);
	delete [] txt;
	txt = newtxt;
	len = newlen;
	return *this;
} /* operator += */

inline word word::operator + (const word &w) const
{
	word new_w (*this);
	new_w += w;
	return new_w;
} /* operator + */

inline word::operator int () const
{
	if (!len)
		return 0;
	char *s = txt;
	if (*s == '+')
		++ s;
	int num;
	std::istringstream str (s);
	str >> num;
	if (!str)
		return 0;
	else
		return num;
} /* operator int */

// --------------------------------------------------

inline int_t hashkey1 (const word &w)
{
	int len = w. length ();
	if (!len)
		return 13;
	const char *txt = w. text ();
	int_t code = (static_cast<int_t> (txt [0]) << 7) ^
		(static_cast<int_t> (txt [len - 1]));
	if (len > 3)
		code ^= static_cast<int_t> (txt [2]) << 15;
	return code;
} /* word::hashkey1 */

inline int_t hashkey2 (const word &w)
{
	int len = w. length ();
	if (!len)
		return 7;
	const char *txt = w. text ();
	int_t code = (static_cast<int_t> (txt [0])) ^
		(static_cast<int_t> (txt [len - 1] << 17));
	if (len > 4)
		code ^= static_cast<int_t> (txt [3]) << 8;
	return code;
} /* word::hashkey2 */

/// Compares two words. Returns 1 if they are the same, 0 otherwise.
inline int operator == (const word &w1, const word &w2)
{
	if (w1. length () != w2. length ())
		return 0;
	if (!w1. length ())
		return 1;
	return !strcmp ((const char *) w1, (const char *) w2);
} /* operator == */

/// Compares two words. Returns 0 if they are the same, 1 otherwise.
inline int operator != (const word &w1, const word &w2)
{
	return !(w1 == w2);
} /* operator != */

/// Compares a word with a C-style string.
inline int operator == (const word &w, const char *c)
{
	if (!w. length ())
		return (!c || !*c);
	return !strcmp ((const char *) w, c);
} /* operator == */

/// Compares a word with a C-style string.
inline int operator != (const word &w, const char *c)
{
	return !(w == c);
} /* operator != */

/// Compares a C-style string with a word.
inline int operator == (const char *c, const word &w)
{
	return (w == c);
} /* operator == */

/// Compares a C-style string with a word.
inline int operator != (const char *c, const word &w)
{
	return (w != c);
} /* operator != */

// --------------------------------------------------

/// Compares two words in an alphabetical way (by ASCII codes).
/// Returns 1 if the first word precedes the second one, 0 otherwise.
inline int operator < (const word &w1, const word &w2)
{
	const char *c1 = (const char *) w1;
	const char *c2 = (const char *) w2;

	while (*c1 && *c2 && ((*c1) == (*c2)))
	{
		++ c1;
		++ c2;
	}
	return ((*c1) < (*c2));
} /* operator < */

/// Compares two words in an alphabetical way (by ASCII codes).
/// Returns 1 if the second word precedes the first one, 0 otherwise.
inline int operator > (const word &w1, const word &w2)
{
	return (w2 < w1);
} /* operator > */

/// Compares two words in an alphabetical way (by ASCII codes).
/// Returns 1 if the second word does not precede the first one, 0 otherwise.
inline int operator <= (const word &w1, const word &w2)
{
	return !(w1 > w2);
} /* operator <= */

/// Compares two words in an alphabetical way (by ASCII codes).
/// Returns 1 if the first word does not precede the second one, 0 otherwise.
inline int operator >= (const word &w1, const word &w2)
{
	return !(w1 < w2);
} /* operator >= */


// --------------------------------------------------

/// Appends the string value of a given element to a word.
/// The operator << is used to produce this string value.
template <class type>
word &operator << (word &w, const type &elem)
{
	std::ostringstream s;
	s << elem;
	w += s. str (). c_str ();
	return w;
} /* operator << */


// --------------------------------------------------

/// Writes the given word to an output stream.
inline std::ostream &operator << (std::ostream &out, const word &w)
{
	if (w. length ())
		out << (const char *) w;
	return out;
} /* operator << */

/// Reads a word from an input stream.
inline std::istream &operator >> (std::istream &in, word &w)
{
	char buf [256 + 1];
	int pos = 0;
	int ch = in. peek ();
	while ((ch != ' ') && (ch != '\r') && (ch != '\n') && (ch != '\t') &&
		(ch != EOF))
	{
		buf [pos ++] = in. get ();
		ch = in. peek ();
		if (pos >= 256)
			break;
	}
	buf [pos] = '\0';
	w = word (buf);
	return in;
} /* operator >> */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_WORDS_H_ 

/// @}

