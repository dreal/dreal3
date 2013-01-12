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
#if !defined(TIMER_H)
#define TIMER_H

#include <cassert>

#if defined(_linux) || defined(__FreeBSD__)
#define UNIX_TIME
#endif

#if defined(UNIX_TIME)
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#else
#include <ctime>
#endif

/**
 timer class
 */
class timer
{
	#if !defined(UNIX_TIME)
	public:
		/**
		 default constructor, construct idle timer.
		 */
		timer() : state(fresh)
		{}

		/**
		 start timer
		 */
		void start()
		{
			assert(state != running);
			begin = std::clock();
			state = running;
		}

		/**
		 stop timer
		 */
		void stop()
		{
			assert(state == running);
			end = std::clock();
			state = stopped;
		}

		/**
		 * get user time in seconds
		 **/
		double secs_elapsed() const
		{
			assert(state == stopped);

			return 
				static_cast<double>(end-begin)/
				static_cast<double>(CLOCKS_PER_SEC);
		}
		
		/**
		  get megaflops
		 */
		double mflops(double const num_ops)
		{
			return num_ops / secs_elapsed() / 1e6;
		}
		
	private:
		enum {fresh, running, stopped} state;
		clock_t begin;
		clock_t end;
	#else
	public:
		/**
		 default constructor, construct idle timer.
		 */
		timer() : state(fresh)
		{}

		/**
		 start timer
		 */
		void start()
		{
			assert(state != running);
			rusage usage;
			getrusage(RUSAGE_SELF,&usage);
			begin = usage.ru_utime;
			state = running;
		}

		/**
		 stop timer
		 */
		void stop()
		{
			assert(state == running);
			rusage usage;
			getrusage(RUSAGE_SELF,&usage);
			end = usage.ru_utime;
			state = stopped;
		}

		/**
		 * get user time in seconds
		 **/
		double secs_elapsed() const
		{
			assert(state == stopped);

			timeval result;

			result.tv_sec = end.tv_sec-begin.tv_sec;
			result.tv_usec = end.tv_usec-begin.tv_usec;
			
			if ( result.tv_usec < 0 )
			{
				--(result.tv_sec);
				result.tv_usec += 1000000;
			}

			return static_cast<double>(result.tv_sec) + 
				static_cast<double>(result.tv_usec)/1000000.0;
		}
		
		/**
		  get megaflops
		 */
		double mflops(double const num_ops)
		{
			return num_ops / secs_elapsed() / 1e6;
		}
		
	private:
		enum {fresh, running, stopped} state;
		timeval begin;
		timeval end;
	#endif
};
#endif
