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
#include <iomanip>
#include <vector>
#include <functional>

#include "../bench/Timer.h"

#include "xinewton.h"
#include "interval.h"
#include "autodiff.h"

using namespace xinewton;
using namespace std;


template<>
class MCT<interval, interval>
{
public:
  typedef interval value_type;
};

template<>
class MCT<interval, double>
{
public:
  typedef interval value_type;
};


template<>
class MCT<double, interval>
{
public:
  typedef interval value_type;
};

template<> 
class TypePrinter<interval>
{
public:
  static void printType(ostream &os) 
  {
    os << "interval";
  }
};

  

template<class Arg, class Result, class Expr>
class ETUnFun: public unary_function<Arg, Result>
{
  Expr expr;
  
public:
  ETUnFun(Expr expr_): expr(expr_) { }

  result_type operator()(argument_type x) 
  {
    return expr.eval(x);
  }
};

template<class Arg, class Result, class Expr>
class ETUnFunDeriv: public unary_function<Arg, Result>
{
  Expr expr;
  
public:
  ETUnFunDeriv(Expr expr_): expr(expr_) { }

  result_type operator()(argument_type x) 
  {
    return expr.evalDeriv(x);
  }
};



template <class Expr>
ETUnFun<typename Expr::value_type, typename Expr::value_type, Expr>
genFun(const Expr expr) 
{
  typedef typename Expr::value_type value_type;
  return ETUnFun<value_type, value_type, Expr>(expr);
}

template <class Expr>
ETUnFunDeriv<typename Expr::value_type, typename Expr::value_type, Expr>
genDeriv(const Expr expr) 
{
  typedef typename Expr::value_type value_type;
  return ETUnFunDeriv<value_type, value_type, Expr>(expr);
}


varType(interval, ivar);
varType(double, dvar);


#define FUN0 (sqr(x) - 3.0*x)
#define FUN1 (power(x,4) - 12.0*power(x,3) + 47.0*sqr(x) - 60.0*x)
#define FUN2 (power(x,3) - 2.0*sqr(x) - 5.0*x + 6.0)
#define FUN3 (cosh(x)+10*sqr(x)*sqr(sin(x))-34)
#define FUN4 (sqr(sin(x)) - cos(sqr(x)))
#define FUN5 (power(x,7)-power(x,4)-12.0)
#define FUN6 ((power(x,4)-10.0*power(x,3)-13.0*sqr(x)+118.0*x+120.0)/(sqr(x)+2.0))
#define FUN7 ((sqr(x)-1.0)/(sqr(x)+1.0))

// real zero at x = -1.16715
#define FUN8 (0.33*power(x,3))

int main() 
{
  filib::fp_traits<double>::setup();

  interval::precision(5);
  cout << setprecision(5);


  XINewton<interval> newton0;
  XINewton<interval> newton1;
  XINewton<interval> newton2;
  XINewton<interval> newton3;
  XINewton<interval> newton4;
  XINewton<interval> newton5;
  XINewton<interval> newton6;
  XINewton<interval> newton7;
  
  ivar x;

  interval xxx = FUN8.evalDeriv(interval(1.0));
  cout << xxx << endl;
  xxx.bitImage(cout);
  
  Timer timer;

  timer.Start();
  for (int i=0; i<10000; i++) {
    //newton0.allZeros(genFun(FUN0), genDeriv(FUN0), interval(-100, 100), 1e-15);
    newton1.allZeros(genFun(FUN1), genDeriv(FUN1), interval(-100, 100), 1e-15);
    //newton2.allZeros(genFun(FUN2), genDeriv(FUN2), interval(-100, 100), 1e-15);
    //newton3.allZeros(genFun(FUN3), genDeriv(FUN3), interval(-100, 100), 1e-15);
    //newton4.allZeros(genFun(FUN4), genDeriv(FUN4), interval(-10, 10), 1e-15);
    //newton5.allZeros(genFun(FUN5), genDeriv(FUN5), interval(-100, 100), 1e-15);
    //newton6.allZeros(genFun(FUN8), genDeriv(FUN8), interval(-100, 100), 1e-15);
    //newton7.allZeros(genFun(FUN7), genDeriv(FUN7), interval(-100, 100), 1e-15); 
  }
  
  timer.Stop();
  
  
  //newton0.printZeros();
  newton1.printZeros();
  //newton2.printZeros();
  //newton3.printZeros();
  //newton4.printZeros();
  //newton5.printZeros();
  //newton6.printZeros();
  //newton7.printZeros();
  
  cout << timer.SecsElapsed() << " sec." << endl;

  return 0;
}






