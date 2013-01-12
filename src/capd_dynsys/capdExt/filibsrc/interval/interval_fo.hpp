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
#if ! defined(INTERVAL_FO)
#define INTERVAL_FO
	
#include <functional>
	
namespace filib
{
	/** unary function object **/
	template <typename ResT, typename ArgT>
	struct unary_virtual_fo : public std::unary_function<ResT,ArgT>
	{
		virtual ~unary_virtual_fo() {}
		virtual ResT operator()(ArgT const &) const = 0;
	};
	
	/** binary function object **/
	template <typename ResT, typename ArgT1, typename ArgT2>
	struct binary_virtual_fo : public std::binary_function<ResT,ArgT1,ArgT2>
	{
		virtual ~binary_virtual_fo() {}
		virtual ResT operator()(ArgT1 const &, ArgT2 const &) const = 0;
	};

	/** unary p/m **/
	template <typename N, rounding_strategy K, interval_mode E>
	struct unary_plus_fo :
		public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()(interval<N,K,E> const & a) const 
		{
			return (+a);
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct unary_minus_fo :
		public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()(interval<N,K,E> const & a) const 
		{
			return (-a);
		}
	};
	
	/** plus section **/
	template <typename N, rounding_strategy K, interval_mode E>
	struct plus_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a+b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct plus_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a+b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct plus_argtype_interval_fo
		: public binary_virtual_fo< interval<N,K,E>, N, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(N const & a, interval<N,K,E> const & b) const
		{
			return a+b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct plus_upd_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a+=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct plus_upd_interval_interval_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			interval<N,K,E> c = a;
			return c+=b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct plus_upd_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a+=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct plus_upd_interval_argtype_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			interval<N,K,E> c = a;
			return c+=b;
		}
	};
	
	/** minus section **/
	template <typename N, rounding_strategy K, interval_mode E>
	struct minus_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a-b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct minus_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a-b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct minus_argtype_interval_fo
		: public binary_virtual_fo< interval<N,K,E>, N, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(N const & a, interval<N,K,E> const & b) const
		{
			return a-b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct minus_upd_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a-=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct minus_upd_interval_interval_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			interval<N,K,E> c = a;
			return c-=b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct minus_upd_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a-=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct minus_upd_interval_argtype_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			interval<N,K,E> c = a;
			return c-=b;
		}
	};

	/** multiplies section **/
	template <typename N, rounding_strategy K, interval_mode E>
	struct multiplies_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a*b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct multiplies_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a*b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct multiplies_argtype_interval_fo
		: public binary_virtual_fo< interval<N,K,E>, N, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(N const & a, interval<N,K,E> const & b) const
		{
			return a*b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct multiplies_upd_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a*=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct multiplies_upd_interval_interval_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			interval<N,K,E> c = a;
			return c*=b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct multiplies_upd_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a*=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct multiplies_upd_interval_argtype_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			interval<N,K,E> c = a;
			return c*=b;
		}
	};

	/** divides section **/
	template <typename N, rounding_strategy K, interval_mode E>
	struct divides_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a/b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct divides_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a/b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct divides_argtype_interval_fo
		: public binary_virtual_fo< interval<N,K,E>, N, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(N const & a, interval<N,K,E> const & b) const
		{
			return a/b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct divides_upd_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a/=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct divides_upd_interval_interval_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			interval<N,K,E> c = a;
			return c/=b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct divides_upd_interval_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return a/=b;
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct divides_upd_interval_argtype_copy_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			interval<N,K,E> c = a;
			return c/=b;
		}
	};

	/** utility section **/	
	template <typename N, rounding_strategy K, interval_mode E>
	struct inf_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return inf(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sup_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return sup(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct isPoint_fo : public unary_virtual_fo <bool, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a) const
		{
			return isPoint(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct isInfinite_fo : public unary_virtual_fo <bool, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a) const
		{
			return isInfinite(a);
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct isEmpty_fo : public unary_virtual_fo <bool, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a) const
		{
			return isEmpty(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct hasUlpAcc_fo : public binary_virtual_fo <bool, interval<N,K,E>, unsigned int >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, unsigned int const & b) const
		{
			return hasUlpAcc(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct diam_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return diam(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct relDiam_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return relDiam(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct rad_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return rad(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct mag_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return mag(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct abs_fo : public unary_virtual_fo <interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return abs(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct imin_fo : public binary_virtual_fo <interval<N,K,E>, interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return imin(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct imax_fo : public binary_virtual_fo <interval<N,K,E>, interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return imax(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct dist_fo : public binary_virtual_fo <N, interval<N,K,E>, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return dist(a,b);
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct mid_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return mid(a);
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct mig_fo : public unary_virtual_fo <N, interval<N,K,E> >
	{
		virtual N operator()
		(interval<N,K,E> const & a) const
		{
			return mig(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct blow_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, N >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, N const & b) const
		{
			return blow(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct intersect_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return intersect(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct hull_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return hull(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct hull_argtype_interval_fo
		: public binary_virtual_fo< interval<N,K,E>, N, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(N const & a, interval<N,K,E> const & b) const
		{
			return hull(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct hull_argtype_argtype_fo
		: public binary_virtual_fo< interval<N,K,E>, N, N >
	{
		virtual interval<N,K,E> operator()
		(N const & a, N const & b) const
		{
			return hull<N,K,E>(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct disjoint_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return disjoint(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct in_fo
		: public binary_virtual_fo< bool,  N, interval<N,K,E> >
	{
		virtual bool operator()
		(N const & a, interval<N,K,E> const & b) const
		{
			return in(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct interior_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return interior(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct proper_subset_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return proper_subset(a,b);
		}
	};

	template <typename N, rounding_strategy K, interval_mode E>
	struct subset_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return subset(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct smaller_equal_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a <=b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct proper_superset_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return proper_superset(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct superset_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return superset(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct greater_equal_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a >=b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct seq_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return seq(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct equality_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a == b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sne_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return sne(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct inequality_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return a != b;
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sge_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return sge(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sgt_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return sgt(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sle_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return sle(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct slt_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return slt(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct ceq_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return ceq(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct cne_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return cne(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct cge_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return cge(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct cgt_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return cgt(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct cle_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return cle(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct clt_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return clt(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct peq_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return peq(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct pne_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return pne(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct pge_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return pge(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct pgt_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return pgt(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct ple_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return ple(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct plt_fo
		: public binary_virtual_fo< bool,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual bool operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return plt(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct acos_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return acos(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct acosh_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return acosh(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct acot_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return acot(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct acoth_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return acoth(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct asin_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return asin(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct asinh_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return asinh(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct atan_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return atan(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct atanh_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return atanh(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct cos_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return cos(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct cosh_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return cosh(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct cot_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return cot(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct coth_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return coth(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct exp_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return exp(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct exp10_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return exp10(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct exp2_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return exp2(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct expm1_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return expm1(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct log_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return log(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct log10_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return log10(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct log1p_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return log1p(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct log2_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
#if ! defined(__CYGWIN__)
			return log2(a);
#else
			return log_2(a);
#endif
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct power_interval_integer_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, int >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, int const & b) const
		{
			return power(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct pow_interval_interval_fo
		: public binary_virtual_fo< interval<N,K,E>,  interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a, interval<N,K,E> const & b) const
		{
			return pow(a,b);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sin_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return sin(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sinh_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return sinh(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sqr_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return sqr(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct sqrt_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return sqrt(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct tan_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return tan(a);
		}
	};
	
	template <typename N, rounding_strategy K, interval_mode E>
	struct tanh_fo
		: public unary_virtual_fo< interval<N,K,E>, interval<N,K,E> >
	{
		virtual interval<N,K,E> operator()
		(interval<N,K,E> const & a) const
		{
			return tanh(a);
		}
	};

	template <typename N>
	struct pred_fo : public unary_virtual_fo<N,N>
	{
		virtual N operator()(N const & a) const
		{ return primitive::pred(a); }
	};

	template <typename N>
	struct succ_fo : public unary_virtual_fo<N,N>
	{
		virtual N operator()(N const & a) const
		{ return primitive::succ(a); }
	};
}
#endif
