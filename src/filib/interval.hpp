/*********************************************************************/
/*                                                                   */
/*   fi_lib  --- A fast interval library (Version 1.2)               */
/*                                                                   */
/*  Authors:                                                         */
/*  --------                                                         */
/*  Werner Hofschuster, Walter Kraemer                               */
/*  Wissenschaftliches Rechnen/Softwaretechnologie                   */
/*  Universitaet Wuppertal, Germany                                  */
/*                                                                   */ 
/*  Copyright:                                                       */
/*  ----------                                                       */
/*  Copyright (C) 1997-2000 Institut fuer Wissenschaftliches Rechnen */
/*                          und Mathematische Modellbildung (IWRMM)  */
/*                                           and                     */
/*                          Institut fuer Angewandte Mathematik      */
/*                          Universitaet Karlsruhe, Germany          */
/*            (C) 2000-2005 Wiss. Rechnen/Softwaretechnologie        */
/*                          Universitaet Wuppertal, Germany          */
/*                                                                   */
/*  This library is free software; you can redistribute it and/or    */
/*  modify it under the terms of the GNU Library General Public      */
/*  License as published by the Free Software Foundation; either     */
/*  version 2 of the License, or (at your option) any later version. */
/*                                                                   */
/*  This library is distributed in the hope that it will be useful,  */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of   */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.             */
/*  See the GNU Library General Public License for more details.     */
/*                                                                   */
/*  You should have received a copy of the GNU Library General Public*/
/*  License along with this library; if not, write to the Free       */
/*  Foundation, Inc., 59 Temple Place, Suite 330, Boston,            */
/*  MA  02111-1307  USA                                              */
/*                                                                   */
/*********************************************************************/

#include "fi_lib.h"
#include <iostream>
#include <iomanip>

/* ------------------------------------------------------------------- */
/* --- assignment                                                  --- */
/* ------------------------------------------------------------------- */

interval _interval (double x) {
  interval w;

  w.INF = x;
  w.SUP = x;

  return w;
}

interval _interval (double x, double y) {
  interval w;

  if (x > y) {
    std::cout << "Error: Invalid arguments in function _interval" << std::endl;
  }
  w.INF = x;
  w.SUP = y;

  return w;
}

/* ------------------------------------------------------------------- */
/* --- IO (input/output)                                           --- */
/* ------------------------------------------------------------------- */

std::istream& operator>> (std::istream& is, interval& a) {
  double help, ioconst;

  ioconst = (1e17-1)*1e27;

  is >> help;
  if ((help<-ioconst) || (help>ioconst)) 
    a.INF = q_pred(q_pred(help));
  else
    a.INF = q_pred(help);
                         
  is >> help;
  if ((help<-ioconst) || (help>ioconst)) 
    a.SUP = q_succ(q_succ(help));
  else
    a.SUP = q_succ(help);
 
  return is;
}

std::ostream& operator<< (std::ostream& os, interval a) {
  interval help;

  help.INF = q_pred(q_pred(a.INF));
  help.SUP = q_succ(q_succ(a.SUP));

  std::ios_base::fmtflags aktform = std::cout.flags();
  os << "[" << std::setprecision(15) << std::setw(23) << std::setiosflags(std::ios::scientific);
  os <<  help.INF;
  std::cout.flags(aktform);
  os << "," << std::setprecision(15) << std::setw(23) << std::setiosflags(std::ios::scientific);
  os << help.SUP;
  std::cout.flags(aktform);
  os << " ]";

  return os;
}

/* ------------------------------------------------------------------- */
/* --- interval arithmetic (basic operations)                      --- */
/* ------------------------------------------------------------------- */

interval operator+ (interval a, interval b) {
  return add_ii (a, b);
}

interval operator+ (interval a, double b) {
  return add_id (a, b);
}

interval operator+ (double a, interval b) {
  return add_di (a, b);
}

interval operator+ (interval a) {
  return a;
}

interval operator- (interval a, interval b) {
  return sub_ii (a, b);
}

interval operator- (interval a, double b) {
  return sub_id (a, b);
}

interval operator- (double a, interval b) {
  return sub_di (a, b);
}

interval operator- (interval a) {
  return _interval (-a.SUP, -a.INF);
}

interval operator* (interval a, interval b) {
  return mul_ii (a, b);
}

interval operator* (interval a, double b) {
  return mul_id (a, b);
}

interval operator* (double a, interval b) {
  return mul_di (a, b);
}

interval operator/ (interval a, interval b) {
  return div_ii (a, b);
}

interval operator/ (interval a, double b) {
  return div_id (a, b);
}

interval operator/ (double a, interval b) {
  return div_di (a, b);
}

/* ------------------------------------------------------------------- */
/* --- interval arithmetic (logical operations)                    --- */
/* ------------------------------------------------------------------- */

int operator== (interval a, interval b) {
  return ieq_ii (a, b);
}

int operator== (interval a, double b) {
	return ieq_ii (a, _interval(b));
}

interval operator| (interval a, interval b) {
  return hull (a, b);
}

int operator<= (double a, interval b) {
  return in_di (a, b);
}

int in (double a, interval b) {
	return in_di (a, b);
}

int in (interval a, interval b) {
	return in_ii (a, b);
}

interval operator& (interval a, interval b) {
  return intsec (a, b);
}

int operator< (interval a, interval b) {
  return in_ii (a, b);
}

int operator< (double a, interval b) {
  if (b.INF<a && a<b.SUP) return 1; else return 0;
}

int operator>= (interval a, double b) {
  if (a.INF<=b && b<=a.SUP) return 1; else return 0;
}

int operator> (interval a, double b) {
  if (a.INF<b && b<a.SUP) return 1; else return 0;
}

int operator!= (interval a, interval b) {
  if (!(a.INF==b.INF && a.SUP==b.SUP)) return 1; else return 0;     
}

int operator<= (interval a, interval b) {
  if (b.INF<=a.INF && a.SUP<=b.SUP) return 1; else return 0;
}  

int operator>= (interval a, interval b) {
  if (b.INF>=a.INF && a.SUP>=b.SUP) return 1; else return 0; 
}

int operator> (interval a, interval b) {
  if (b.INF>a.INF && a.SUP>b.SUP) return 1; else return 0; 
}

/* ------------------------------------------------------------------- */
/* --- utilities, mid, diam, ...                                   --- */
/* ------------------------------------------------------------------- */

double inf (interval a) {
  return a.INF;
}

double sup (interval a) {
  return a.SUP;
}

double mid (interval a) {
  return q_mid (a);
}

int disjoint (interval a, interval b) {
  return dis_ii (a, b);
}

double diam (interval a) {
  return q_diam (a);
}


double drel (interval a)
{ if ((a.SUP<=-q_minr) || (q_minr<=a.INF)) {
    if (a.INF > 0) return diam(a)/a.INF;
    else           return diam(a)/(-a.SUP);
  } else {
    return diam(a);
  }
}


interval blow ( interval x, double eps) {
	interval y;
	y = (1.0 +eps) * x - eps*x;
	return (_interval(q_pred(y.INF),q_succ(y.SUP)));
}

/* ------------------------------------------------------------------- */
/* --- interval arithmetic (elementary functions)                  --- */
/* ------------------------------------------------------------------- */

interval exp (interval a) {
  return j_exp (a);
}

interval expm (interval a) {
  return j_expm (a);
}

interval sinh (interval a) {
  return j_sinh (a);
}

interval cosh (interval a) {
  return j_cosh (a);
}

interval coth (interval a) {
  return j_coth (a);
}

interval tanh (interval a) {
  return j_tanh (a);
}

interval log (interval a) {
  return j_log (a);
}

interval ln (interval a) {
  return j_log (a);
}

interval lg1p (interval a) {
  return j_lg1p (a);
}

interval sqrt (interval a) {
  return j_sqrt (a);
}

interval sqr (interval a) {
  return j_sqr (a);
}

interval asnh (interval a) {
  return j_asnh (a);
}

interval asinh (interval a) {
  return j_asnh (a);
}

interval acsh (interval a) {
  return j_acsh (a);
}

interval acosh (interval a) {
  return j_acsh (a);
}

interval acth (interval a) {
  return j_acth (a);
}

interval acoth (interval a) {
  return j_acth (a);
}

interval atnh (interval a) {
  return j_atnh (a);
}

interval atanh (interval a) {
  return j_atnh (a);
}

interval asin (interval a) {
  return j_asin (a);
}

interval acos (interval a) {
  return j_acos (a);
}

interval acot (interval a) {
  return j_acot (a);
}

interval atan (interval a) {
  return j_atan (a);
}

interval sin (interval a) {
  return j_sin (a);
}

interval cos (interval a) {
  return j_cos (a);
}

interval cot (interval a) {
  return j_cot (a);
}

interval tan (interval a) {
  return j_tan (a);
}

interval exp2 (interval a) {
  return j_exp2 (a);
}

interval ex10 (interval a) {
  return j_ex10 (a);
}

interval log2 (interval a) {
  return j_log2 (a);
}

interval lg10 (interval a) {
  return j_lg10 (a);
}

interval erf (interval a) {
  return j_erf (a);
}
  
interval erfc (interval a) {
  return j_erfc (a);
}

