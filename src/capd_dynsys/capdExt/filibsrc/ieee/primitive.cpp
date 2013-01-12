/*                                                                           
**  fi_lib++  --- A fast interval library (Version 2.0)                     
**                                                                  
**  Copyright (C) 2001:                                                        
**                                                     
**  Werner Hofschuster, Walter Kraemer                               
**  Wissenschaftliches Rechnen/Softwaretechnologie (WRSWT)  
**  Universitaet Wuppertal, Germany                                           
**  Michael Lerch, German Tischler, Juergen Wolff von Gudenberg       
**  Institut fuer Informatik                                         
**  Universitaet Wuerzburg, Germany                                           
** 
**  This library is free software; you can redistribute it and/or
**  modify it under the terms of the GNU Library General Public
**  License as published by the Free Software Foundation; either
**  version 2 of the License, or (at your option) any later version.
**
**  This library is distributed in the hope that it will be useful,
**  but WITHOUT ANY WARRANTY; without even the implied warranty of
**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
**  Library General Public License for more details.
**
**  You should have received a copy of the GNU Library General Public
**  License along with this library; if not, write to the Free
**  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
*/
#include <ieee/primitive.hpp>
#include <new>

#if defined(__GNUC__) && __GNUC__ < 3
#include <strstream>
#else
#include <sstream>
#endif
#include <cstdio>

/** uses code from fi_lib. please read "licenses/filib.license". **/

namespace filib
{
	/**
	 * Internal functions to compute special numbers
	 **/

	double primitive::computeMin() 
	{
		a_diee f;
		f.ieee.sign  = 0x0;
		f.ieee.expo  = 0x0;
		f.ieee.mant0 = 0x0;
		f.ieee.mant1 = 0x1;
		return f.f;
	}

	double primitive::computeMinNorm() 
	{
		a_diee f;
		f.ieee.sign  = 0x0;
		f.ieee.expo  = 0x1;
		f.ieee.mant0 = 0x0;
		f.ieee.mant1 = 0x0;
		return f.f;
	}

	double primitive::computeMax() 
	{
		a_diee f;
		f.ieee.sign  = 0x0;
		f.ieee.expo  = 0x7FE;
		f.ieee.mant0 = 0xFFFFF;
		f.ieee.mant1 = 0xFFFFFFFF;
		return f.f;
	}

	double primitive::computePosInf() 
	{
		a_diee f;
		f.ieee.sign  = 0x0;
		f.ieee.expo  = 0x7FF;
		f.ieee.mant0 = 0x0;
		f.ieee.mant1 = 0x0;
		return f.f;
	}

	double primitive::computeNegInf() 
	{
		a_diee f;
		f.ieee.sign  = 0x1;
		f.ieee.expo  = 0x7FF;
		f.ieee.mant0 = 0x0;
		f.ieee.mant1 = 0x0;
		return f.f;
	}

	double primitive::computeQNaN() 
	{
		a_diee f;
		f.ieee.sign  = 0x0;
		f.ieee.expo  = 0x7FF;
		f.ieee.mant0 = 0x80000;
		f.ieee.mant1 = 0x0;
		return f.f;
	}

	/**
	 * pred/succ table stuff
	 **/

	#if defined(FILIB_PRED_SUCC_TABLES)

	primitive::PredSuccTable::PredSuccTable() 
	{
		a_diee f;
		f.ieee.sign  = 0;
		f.ieee.mant0 = 0;
		f.ieee.mant1 = 0;

		try
		{
			ULP = new double[2048];

			for( size_t i=0; i<2048; i++ )
			{
				f.ieee.expo = i;
				ULP[i] = primitive::ulp(f.f);
    	
				/**
				 * std::cout << i << ": \t";
				 * primitive::bitImage(ULP[i], std::cout);
				 * std::cout << std::endl;
				 **/
			}
		}
		catch(std::bad_alloc const &)
		{
			std::cerr 
				<< "filib.0: primitive::PredSuccTable::PredSuccTable():" << std::endl
				<< "panic: caught exception bad_alloc, out of memory" << std::endl;
			std::terminate();
		}
	}

	primitive::PredSuccTable::~PredSuccTable() 
	{
		delete [] ULP;
	}

	primitive::PredSuccTable primitive::psTable;

	#endif /** FILIB_PRED_SUCC_TABLES **/

	/**
	 * Instantiation of static members of class primitive
	 **/
	double primitive::min     = computeMin();  
	double primitive::minNorm = computeMinNorm();  
	double primitive::max     = computeMax();
	double primitive::posInf  = computePosInf();
	double primitive::negInf  = computeNegInf();
	double primitive::qNaN    = computeQNaN();

	/**
	 * I/O
	 **/
	void primitive::print(double const & x, std::ostream &os) 
	{
		if (x == NEG_INFTY())
			os << "-INF";
		else if (x == POS_INFTY())
			os << "+INF";
		else if (isNaN(x))
			os << "NaN";
		else
			os << x;
	}

	void primitive::bitImage(double const & d, std::ostream &os) 
	{
		basicBitImage(d, os);
		os << std::endl;
	}

	void primitive::basicBitImage(double const & d, std::ostream &os) 
	{
		a_diee f;
		f.f = d;

		int i;

		os << (f.ieee.sign == 1 ? '1' : '0') << ':';
  
		i = 11;

		while (i--)
			os << ((f.ieee.expo & (1 << i)) ? '1' : '0');
		os << ':';
  
		i = 20;

		while (i--)
			os << ((f.ieee.mant0 & (1 << i)) ? '1' : '0');

		i = 32;

		while (i--)
			os << ((f.ieee.mant1 & (1 << i)) ? '1' : '0');
	}

	void primitive::basicHexImage(double const & d, std::ostream &os) 
	{
		a_diee f;
		f.f = d;

		os << (f.ieee.sign == 1 ? '1' : '0') << ':';
  
		char expBuf[4];

		std::sprintf(expBuf,"%03x",f.ieee.expo);

		os << (&expBuf[0]) << ':';

		char mant0Buf[6];
		std::sprintf(mant0Buf,"%05x",f.ieee.mant0);

		os << (&mant0Buf[0]);

		char mant1Buf[9];
		std::sprintf(mant1Buf,"%08x",f.ieee.mant1);

		os << (&mant1Buf[0]);
	}

	void primitive::basicBitImage(float const & d, std::ostream &os) 
	{
		a_fiee f;
		f.f = d;

		int i;

		os << (f.ieee.sign == 1 ? '1' : '0') << ':';
  
		i = 8;

		while (i--)
			os << ((f.ieee.expo & (1 << i)) ? '1' : '0');
		os << ':';
  
		i = 23;

		while (i--)
			os << ((f.ieee.mant & (1 << i)) ? '1' : '0');
	}

	void primitive::basicHexImage(float const & d, std::ostream &os) 
	{
		a_fiee f;
		f.f = d;

		os << (f.ieee.sign == 1 ? '1' : '0') << ':';
  
		char expBuf[3];

		std::sprintf(expBuf,"%02x",f.ieee.expo);

		os << (&expBuf[0]) << ':';

		char mantBuf[7];
		std::sprintf(mantBuf,"%06x",f.ieee.mant);

		os << (&mantBuf[0]);
	}

	double const primitive::zero_pred = primitive::compose(1,1,0,0);
	double const primitive::zero_succ = primitive::compose(0,1,0,0);
	double const primitive::one_pred  = primitive::compose(0,1022,0xFFFFF,0xFFFFFFFF);
	double const primitive::one_succ  = primitive::compose(0,1023,0,1);

	float const primitive::zero_fpred = primitive::composef(1,1,0);
	float const primitive::zero_fsucc = primitive::composef(0,1,0);
	float const primitive::one_fpred   = primitive::composef(0,126,(1<<23)-1);
	float const primitive::one_fsucc   = primitive::composef(0,127,1);

	template <>
	double constructFromBitSet<double>(std::istream & in) throw(interval_io_exception)
	{
		unsigned char signBit[1];
		unsigned char expBits[11];
		unsigned char mantBits[52];
		readBitSet(in,1,signBit);
		readChar(in,':');
		readBitSet(in,11,expBits);
		readChar(in,':');
		readBitSet(in,52,mantBits);
	
		unsigned int sign  = signBit[0];
		unsigned int exp   = 0;
	
		for ( int i = 0; i < 11; ++i )
		{
			exp <<= 1;
			exp |= expBits[i];
		}

		unsigned int mant0 = 0;

		for ( int i = 0; i < 20; ++i )
		{
			mant0 <<= 1;
			mant0 |= mantBits[i];
		}
	
		unsigned int mant1 = 0;

		for ( int i = 20; i < 52; ++i )
		{
			mant1 <<= 1;
			mant1 |= mantBits[i];
		}

		return primitive::compose(sign,exp,mant0,mant1);
	}

	template <>
	float constructFromBitSet<float>(std::istream & in) throw(interval_io_exception)
	{
		unsigned char signBit[1];
		unsigned char expBits[8];
		unsigned char mantBits[23];

		readBitSet(in,1,signBit);
		readChar(in,':');
		readBitSet(in,8,expBits);
		readChar(in,':');
		readBitSet(in,23,mantBits);
	
		unsigned int sign  = signBit[0];
		unsigned int exp   = 0;
	
		for ( int i = 0; i < 8; ++i )
		{
			exp <<= 1;
			exp |= expBits[i];
		}

		unsigned int mant = 0;

		for ( int i = 0; i < 23; ++i )
		{
			mant <<= 1;
			mant |= mantBits[i];
		}
	
		return primitive::composef(sign,exp,mant);
	}

	template <>
	double constructFromHexSet<double>(std::istream & in) throw(interval_io_exception)
	{
		unsigned char signHex[1];
		unsigned char expHex[3];
		unsigned char mantHex[5+8];
		readHexSet(in,1,signHex);
		readChar(in,':');
		readHexSet(in,3,expHex);
		readChar(in,':');
		readHexSet(in,5+8,mantHex);
	
		unsigned int sign  = signHex[0];
		unsigned int exp   = 0;
	
		for ( int i = 0; i < 3; ++i )
		{
			exp <<= 4;
			exp |= expHex[i];
		}

		unsigned int mant0 = 0;

		for ( int i = 0; i < 5; ++i )
		{
			mant0 <<= 4;
			mant0 |= mantHex[i];
		}
	
		unsigned int mant1 = 0;

		for ( int i = 5; i < 5+8; ++i )
		{
			mant1 <<= 4;
			mant1 |= mantHex[i];
		}

		if ( 
			sign >= (1 << 1) ||
			exp >= (1 << 11)
		)
			throw interval_io_exception("invalid number in hex image");

		return primitive::compose(sign,exp,mant0,mant1);
	}

	template <>
	float constructFromHexSet<float>(std::istream & in) throw(interval_io_exception)
	{
		unsigned char signHex[1];
		unsigned char expHex[2];
		unsigned char mantHex[6];
		readHexSet(in,1,signHex);
		readChar(in,':');
		readHexSet(in,2,expHex);
		readChar(in,':');
		readHexSet(in,6,mantHex);
	
		unsigned int sign  = signHex[0];
		unsigned int exp   = 0;
	
		for ( int i = 0; i < 2; ++i )
		{
			exp <<= 4;
			exp |= expHex[i];
		}

		unsigned int mant = 0;

		for ( int i = 0; i < 6; ++i )
		{
			mant <<= 4;
			mant |= mantHex[i];
		}

		if ( 
			sign >= (1 << 1) ||
			exp >= (1 << 8) ||
			mant >= (1 << 23) 
		)
			throw interval_io_exception("invalid number in hex image");
	
		return primitive::composef(sign,exp,mant);
	}

	template<>
	int whitespace<char>::isSpace(int arg)
	{
		return isspace(arg);
	}

	static double checkedToDouble(std::string const & s)
	throw(interval_io_exception)
	{
		char * endptr = 0;
		char const * nptr = s.c_str();
		double val = strtod(s.c_str(),&endptr);

		if ( endptr != (nptr+s.length()) )
			throw interval_io_exception(std::string("Failed parsing string, wanted value, got ")+s+" .");

		return val;
	}
	template <>
	double inferFromString<double,false>(std::string const & s)
	throw(interval_io_exception)
	{
		return primitive::basic_pred(checkedToDouble(s)) ;
	}
	template <>
	double inferFromString<double,true>(std::string const & s)
	throw(interval_io_exception)
	{
		return primitive::basic_succ(checkedToDouble(s)) ;

	}
	template <>
	float inferFromString<float,false>(std::string const & s)
	throw(interval_io_exception)
	{
		float tval = static_cast<float>(checkedToDouble(s));
		
		if ( tval == 0 )
			return primitive::composef(1,1,0);
		else if ( tval > 0 )
			return tval * primitive::composef(0,126,(1<<23)-1);
		else
			return tval * primitive::composef(0,127,1);		
	}
	template <>
	float inferFromString<float,true>(std::string const & s)
	throw(interval_io_exception)
	{
		float tval = static_cast<float>(checkedToDouble(s));
		
		if ( tval == 0 )
			return primitive::composef(0,1,0);
		else if ( tval < 0 )
			return tval * primitive::composef(0,126,(1<<23)-1);
		else
			return tval * primitive::composef(0,127,1);		
	}

	void readBitSet(
		std::istream & in, 
		unsigned int n0,
		unsigned char * s) throw(interval_io_exception)
	{
		size_t pos = 0;
		size_t n = n0;

		while ( n-- )
		{
			char c = in.get();
		
			if ( in.good() )
			{
				if ( c == '0' )
					s[pos++] = 0;
				else if ( c == '1' )
					s[pos++] = 1;
				else
				{
					char ct = c;
					in.putback(c);
					throw interval_io_exception(std::string("unexpected character ")+ct+" while reading bitstring");
				}
			}
			else
				throw interval_io_exception("stream bad while reading bitstring");
		}
	}

	void readHexSet(
		std::istream & in, 
		unsigned int n0,
		unsigned char * s) throw(interval_io_exception)
	{
		size_t pos = 0;
		size_t n = n0;

		while ( n-- )
		{
			char c = in.get();
		
			if ( in.good() )
			{
				switch(c)
				{
					case '0':
					case '1':
					case '2':
					case '3':
					case '4':
					case '5':
					case '6':
					case '7':
					case '8':
					case '9':
						s[pos++] = c-'0';
						break;
					case 'a':
					case 'A':
						s[pos++] = 10;
						break;
					case 'b':
					case 'B':
						s[pos++] = 11;
						break;
					case 'c':
					case 'C':
						s[pos++] = 12;
						break;
					case 'd':
					case 'D':
						s[pos++] = 13;
						break;
					case 'e':
					case 'E':
						s[pos++] = 14;
						break;
					case 'f':
					case 'F':
						s[pos++] = 15;
						break;
					default:
						char ct = c;
						in.putback(c);
						throw interval_io_exception(std::string("unexpected character ")+ct+" while reading hexstring");
						break;
				}
			}
			else throw interval_io_exception("stream bad while reading hexstring");
		}
	}

	void readChar(std::istream& in, char c0) throw(interval_io_exception)
	{
		char c = in.get();
		
		if ( c != c0 )
		{
			char ct = c;
			in.putback(c);
			throw interval_io_exception(std::string("unexpected char ")+ct+" in readChar while expecting "+c0);
		}
	}

	template <>
	float constructFromBitSet<float>(std::string & in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in.c_str());
		#else
		std::istringstream istr(in);
		#endif
		return constructFromBitSet<float>(istr);
	}
	template <>
	double constructFromBitSet<double>(std::string & in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in.c_str());
		#else
		std::istringstream istr(in);
		#endif
		return constructFromBitSet<double>(istr);
	}

	template <>
	float constructFromBitSet<float>(char const * in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in);
		#else
		std::istringstream istr(in);
		#endif
		return constructFromBitSet<float>(istr);
	}
	template <>
	double constructFromBitSet<double>(char const * in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in);
		#else
		std::istringstream istr(in);
		#endif
		return constructFromBitSet<double>(istr);
	}

	template <>
	float constructFromHexSet<float>(std::string & in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in.c_str());
		#else
		std::istringstream istr(in);
		#endif
		return constructFromHexSet<float>(istr);
	}
	template <>
	double constructFromHexSet<double>(std::string & in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in.c_str());
		#else
		std::istringstream istr(in);
		#endif
		return constructFromHexSet<double>(istr);
	}

	template <>
	float constructFromHexSet<float>(char const * in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in);
		#else
		std::istringstream istr(in);
		#endif
		return constructFromHexSet<float>(istr);
	}
	template <>
	double constructFromHexSet<double>(char const * in) throw(interval_io_exception)
	{
		#if defined(__GNUC__) && __GNUC__ < 3
		std::istrstream istr(in);
		#else
		std::istringstream istr(in);
		#endif
		return constructFromHexSet<double>(istr);
	}
} /** namespace filib **/
