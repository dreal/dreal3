/////////////////////////////////////////////////////////////////////////////
///
/// @file OutputStream.h
///
/// This file contains definition of some output
/// streams that can be used instead the standard ones (sout, serr)
/// which support logging to a file or suppressing messages to the screen.
///
/// @author Pawel Pilarczyk, Tomasz Kapela
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk and Tomasz Kapela.
//
// This file constitutes a part of the Homology Library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// Started in July 1997. Last revision: September 5, 2009.

#ifndef _CAPD_AUXIL_OUTPUTSTREAM_H_
#define _CAPD_AUXIL_OUTPUTSTREAM_H_
#include <iostream>
#include <fstream>

namespace capd {
namespace auxil {

// --------------------------------------------------
// ----------------- OUTPUT STREAM ------------------
// --------------------------------------------------

/// This class defines an output stream for replacing the standard 'cout'.
/// It has the additional features of flushing the output after every
/// operation, suppressing the output, or logging the output to a file.
class OutputStream {
public:
	/// The default constructor.
	OutputStream(std::ostream &_out = std::cout, bool _show = true,
			bool _flush = false);

	/// The destructor.
	~OutputStream();

	/// Turns on logging to a file.
	/// If the file exists and erase is true, its contents is ereased.
	void logfile(const char *filename, bool erase = true);

	/// Turns on logging to a file.
	/// If the file exists and erase is true, its contents is ereased.
	void logfile(const std::string & filename, bool erase = true){
		logfile(filename.c_str(), erase);
	}


	/// Turns on logging to the same file as some other stream.
	void logfile(const OutputStream &other);

	/// If this variable is set to true then everything that is
	/// written to this stream is also written to 'cout'.
	/// If this variable is set to false then the screen output
	/// is suppressed, while logging can still be turned on.
	bool show;

	/// If this variable is set to true then everything that is
	/// written to this stream is also written to the log file.
	bool log;

	/// If this variable is set to true then both the output stream
	/// 'cout' and the log file are flashed after every write operation.
	/// Note that this may slow down the output significantly if the
	/// log file is located on a network drive.
	bool flush;

	/// Returns a pointer to the stream which is working as a log file.
	/// Returns 0 if no such stream is bound with this output stream.
	std::ofstream *getlogstream(void);

	/// A reference to the main output stream bound with this stream.
	std::ostream &out;

	/// Makes this stream keep the allocated file open for ever, and not
	/// close it even in the destructor. It is assumed then that the
	/// file will be closed automatically by the operating system.
	void keepforever(void);

	/// Local mute of the stream.
	/// This class defines an object which makes the stream mute
	/// by suppressing output to both the screen and the log file
	/// and restores its setting when the object is destroyed.
	struct mute {
		mute(OutputStream &_stream) :
			stream(_stream), show(_stream. show), log(_stream. log) {
			stream. show = false;
			stream. log = false;
			return;
		}
		~mute() {
			stream. show = show;
			stream. log = log;
			return;
		}
		OutputStream &stream;
		bool show;
		bool log;
	};

protected:
	/// A pointer to the log file stream.
	std::ofstream *logstream;

	/// This variable is set to true if this log file pointer was copied
	/// from another output stream, and therefore it should not be
	/// deleted by this stream.
	bool copied;

}; /* class OutputStream */

// --------------------------------------------------

inline OutputStream::OutputStream(std::ostream &_out, bool _show, bool _flush) :
	out(_out) {
	show = _show;
	flush = _flush;
	log = false;
	logstream = NULL;
	copied = false;
	return;
} /* OutputStream::OutputStream */

inline void OutputStream::logfile(const char *filename, bool erase /*= true*/) {
	if (logstream && !copied)
		delete logstream;
	copied = false;
	logstream =  new std::ofstream(filename, erase? std::ios::out : std::ios::app);
	if (!logstream || !*logstream) {
		out << "WARNING: Can't create '" << filename
				<< "'. Logging to a file has been turned off." << std::endl;
		if (logstream)
			delete logstream;
		logstream = NULL;
	} else
		log = true;
	return;
} /* OutputStream::logfile */

inline void OutputStream::logfile(const OutputStream &other) {
	if (!copied && logstream)
		delete logstream;
	logstream = other. logstream;
	if (logstream) {
		copied = true;
		log = true;
	}
	return;
} /* OutputStream::logfile */

inline OutputStream::~OutputStream() {
	if (!copied && logstream)
		delete logstream;
} /* OutputStream::~OutputStream */

inline std::ofstream *OutputStream::getlogstream(void) {
	return logstream;
} /* OutputStream::getlogstream */

inline void OutputStream::keepforever(void) {
	copied = true;
	return;
} /* OutputStream::getlogstream */

/// The operator << for writing any kind of object to the output stream.
/// This object is written using the operator << of the standard stream.
template<typename type>
inline OutputStream &operator <<(OutputStream &out, const type &object) {
	if (out. flush) {
		if (out. show)
			out. out << object << std::flush;
		if (out. log && out. getlogstream())
			(*(out. getlogstream())) << object << std::flush;
	} else {
		if (out. show)
			out. out << object;
		if (out. log && out. getlogstream())
			(*(out. getlogstream())) << object;
	}
	return out;
} /* operator << */

/// A specialization of the operator << for writing a C-style string
/// to the output stream.
inline OutputStream &operator <<(OutputStream &out, const char *object) {
	if (out. flush) {
		if (out. show)
			out. out << object << std::flush;
		if (out. log && out. getlogstream())
			(*(out. getlogstream())) << object << std::flush;
	} else {
		if (out. show)
			out. out << object;
		if (out. log && out. getlogstream())
			(*(out. getlogstream())) << object;
	}
	return out;
} /* operator << */

/// A specialization of the operator << for putting manipulators
/// (like std::endl, std::flush) to the output stream.
inline OutputStream &operator <<(OutputStream &out,
		std::ostream& (*object)(std::ostream&)) {
	if (out. flush) {
		if (out.show)
			out.out << object << std::flush;
		if (out.log && out.getlogstream())
			(*(out.getlogstream())) << object << std::flush;
	} else {
		if (out.show)
			out.out << object;
		if (out.log && out.getlogstream())
			(*(out.getlogstream())) << object;
	}
	return out;
} /* operator << */

// --------------------------------------------------
}
} // end of namespace capd::auxil


#endif /* OUTPUTSTREAM_H_ */
