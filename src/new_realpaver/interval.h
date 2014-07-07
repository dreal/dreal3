#pragma once

#include <cfloat>
#include <climits>
#include <cmath>
#include <iostream>
#include <limits>
#include <string>
#include "interval/interval.hpp"

namespace realpaver {

void ROUND_UPWARD();
void ROUND_DOWNWARD();

class interval {
 public:
    double inf;
    double sup;

    static double const HALF_PI;
    static double const HALF_PI_3;
    static double const HALF_PI_5;
    static double const HALF_PI_7;
    static double const PI;
    static double const PI_2;
    static double const PI_4;
    static double const DBL_INFINITY;
    static interval const empty;
    static interval const realline;
    static void init() { filib::fp_traits<double>::setup(); }
    typedef filib::interval<double, filib::pred_succ_rounding, filib::i_mode_extended> filib_interval;
    interval() : inf(-DBL_INFINITY),
                 sup(+DBL_INFINITY) { }
    explicit interval(double const x) : inf(x), sup(x) { }
    interval(double const i, double const s) : inf(i), sup(s) { }
    explicit interval(filib_interval const & i) : inf(i.inf()), sup(i.sup()) { }
    interval(interval const & i) : inf(i.inf), sup(i.sup) { }
    interval(std::istream & in);
    interval(std::string const & s);
    bool isEmpty() const { return !(inf <= sup); }
    bool equals(interval const & i) const { return (inf == i.inf && sup == i.sup) || (isEmpty() && i.isEmpty()); }
    bool diff(interval const & i) const { return !equals(i); }
    bool includes(double const x) const { return (inf <= x) && (x <= sup); }
    bool includes(interval const & i) const { return (inf <= i.inf) && (i.sup <= sup); }
    friend bool includes(interval const & i, double const x) { return i.includes(x); }
    friend bool includes(interval const & i, interval const & j) { return i.includes(j); }
    bool lt(double const x) const      { return sup   < x; }
    bool lt(interval const & i) const  { return sup   < i.inf; }
    bool lte(double const x) const     { return sup   <= x; }
    bool lte(interval const & i) const { return sup   <= i.inf; }
    bool gt(double const x) const      { return x     < inf; }
    bool gt(interval const & i) const  { return i.sup < inf; }
    bool gte(double const x) const     { return x     <= inf; }
    bool gte(interval const & i) const { return i.sup <= inf; }
    friend bool operator<(interval const & i, double const x)      { return i.lt(x); }
    friend bool operator<(interval const & i, interval const & j)  { return i.lt(j); }
    friend bool operator<=(interval const & i, double const x)     { return i.lte(x); }
    friend bool operator<=(interval const & i, interval const & j) { return i.lte(j); }
    friend bool operator>(interval const & i, double const x)      { return i.gt(x); }
    friend bool operator>(interval const & i, interval const & j)  { return i.gt(j); }
    friend bool operator>=(interval const & i, double const x)     { return i.gte(x); }
    friend bool operator>=(interval const & i, interval const & j) { return i.gte(j); }
    bool includesStrictly(double const x) const { return (inf < x) && (x < sup); }
    bool includesStrictly(interval const & i) const { return (inf < i.inf) && (i.sup < sup); }
    friend bool includesStrictly(interval const & i, double const x) { return i.includesStrictly(x); }
    friend bool includesStrictly(interval const & i, interval const & j) { return i.includesStrictly(j); }
    bool isPoint() const { return inf == sup; }
    bool isInt() const { return isPoint() && static_cast<int>(inf) == inf; }
    bool isZero() const { return inf == 0.0 && sup == 0.0; }
    bool boundZero() const { return inf == 0.0 || sup == 0.0; }
    bool disjointWith(interval const & i) const { return (sup < i.inf) || (i.sup < inf); }
    friend bool disjointWith(interval const & i, interval const & j) { return i.disjointWith(j); }
    bool overlaps(interval const & i) const { return (i.inf <= sup) && (inf <= i.sup); }
    friend bool overlaps(interval const & i, interval const & j) { return i.overlaps(j); }
    bool infinite() const { return (inf == -DBL_INFINITY) || (sup == +DBL_INFINITY); }
    bool finite() const { return !infinite(); }
    double width() const { return sup - inf; }
    bool isCanonical() const;
    double distance(interval const & i) const;
    bool isRealline() const;
    interval & setRealline();
    double midpoint() const;
    bool improved(interval const & old, double imp) const;
    interval & set(interval const & i) { inf = i.inf; sup = i.sup; return *this; }
    interval & set(filib_interval const & i) { inf = i.inf(); sup = i.sup(); return *this; }
    interval & set(double i, double s) { inf = i; sup = s; return *this; }
    interval & setPoint(double p) { inf = sup = p; return *this; }
    interval & setZero() { inf = sup = 0.0; return *this; }
    interval & setOne() { inf = sup = 1.0; return *this; }
    interval & setEmpty() { inf = +DBL_INFINITY; sup = -DBL_INFINITY; return *this; }
    bool equal_digits(interval const & i, int const n) const;
    void trunc();
    std::ostream & display(std::ostream & out, interval const & /* i */,
                           int const /* digits */, int const /* mode*/) const {
        // TODO(soonhok): implement
        return out;
    }
    friend std::ostream & operator<<(std::ostream & out, interval const & i);
    friend std::istream & operator>>(std::istream & in, interval & i);
    // Binary arithmetic operations
    interval & add        (interval const & i);
    interval & add_r      (double   const   x);
    interval & sub        (interval const & i);
    interval & sub_i_r    (double   const   x);
    interval & sub_r_i    (double   const   x);
    interval & mul        (interval const & i);
    interval & mul_r      (double   const   x);
    interval & div        (interval const & i);
    interval & div_i_r    (double   const   x);
    interval & div_r_i    (double   const   x);
    interval & div_rpos_i (interval const & i);
    interval & div_rneg_i (interval const & i);
    interval & pow        (interval const & n);
    // Unary arithmetic operations
    interval & neg      ();
    interval & sqr      ();
    interval & sqrt     ();
    // Elementary functions
    interval & exp      ();
    interval & log      ();
    interval & sin      ();
    interval & cos      ();
    interval & tan      ();
    interval & cosh     ();
    interval & sinh     ();
    interval & tanh     ();
    interval & asin     ();
    interval & acos     ();
    interval & atan     ();
    interval & asinh    ();
    interval & acosh    ();
    interval & atanh    ();
    interval & matan    ();
    interval & safesqrt ();
    interval & atan2    (interval const & x);
    interval & nthroot  (interval const & n);
    interval & abs      ();
    interval & min      (interval const & i);
    interval & max      (interval const & i);
    interval & inter    (interval const & i);
    interval & hull     (interval const & i);
    interval & minus (interval const & i);
    // static functions
    static interval add     (interval i, interval const & j) { return i.add(j); }
    static interval add_i_r (interval i, double   const & x)   { return i.add_r(x); }
    static interval add_r_i (double   const & x, interval i)   { return i.add_r(x); }
    static interval sub     (interval i, interval const & j) { return i.sub(j); }
    static interval sub_i_r (interval i, double   const & x)   { return i.sub_i_r(x); }
    static interval sub_r_i (double   const & x, interval i)   { return i.sub_r_i(x); }
    static interval mul     (interval i, interval const & j) { return i.mul(j); }
    static interval mul_i_r (interval i, double const x)       { return i.mul_r(x); }
    static interval mul_r_i (double const x, interval i)       { return i.mul_r(x); }
    static interval div     (interval i, interval const & j) { return i.div(j); }
    static interval div_i_r (interval i, double const x)       { return i.div_i_r(x); }
    static interval div_r_i (double const x, interval i)       { return i.div_r_i(x); }
    static interval pow     (interval i, interval const & n)   { return i.pow(n); }
    static interval neg     (interval i) { return i.neg(); }
    static interval sqr     (interval i) { return i.sqr(); }
    static interval sqrt    (interval i) { return i.sqrt(); }
    static interval exp     (interval i) { return i.exp(); }
    static interval log     (interval i) { return i.log(); }
    static interval sin     (interval i) { return i.sin(); }
    static interval cos     (interval i) { return i.cos(); }
    static interval tan     (interval i) { return i.tan(); }
    static interval cosh    (interval i) { return i.cosh(); }
    static interval sinh    (interval i) { return i.sinh(); }
    static interval tanh    (interval i) { return i.tanh(); }
    static interval asin    (interval i) { return i.asin(); }
    static interval acos    (interval i) { return i.acos(); }
    static interval atan    (interval i) { return i.atan(); }
    static interval asinh   (interval i) { return i.sinh(); }
    static interval acosh   (interval i) { return i.acosh(); }
    static interval atanh   (interval i) { return i.atanh(); }
    static interval matan   (interval i) { return i.matan(); }
    static interval safesqrt(interval i) { return i.safesqrt(); }
    static interval atan2   (interval y, interval const & x) { return y.atan2(x); }
    static interval nthroot (interval i, interval const & n) { return i.nthroot(n); }
    static interval abs     (interval i) { return i.abs(); }
    static interval min     (interval i, interval const & j) { return i.min(j); }
    static interval max     (interval i, interval const & j) { return i.max(j); }
    static interval inter   (interval i, interval const & j) { return i.inter(j); }
    static interval minus   (interval i, interval const & j) { return i.minus(j); }
    // friends
    friend interval add     (interval const & i, interval const & j) { return interval::add(i, j); }
    friend interval add_i_r (interval const & i, double const & x) { return interval::add_i_r(i, x); }
    friend interval add_r_i (double const & x, interval i) { return interval::add_r_i(x, i); }
    friend interval sub     (interval const & i, interval const & j) { return interval::sub(i, j); }
    friend interval sub_i_r (interval const & i, double const & x) { return interval::sub_i_r(i, x); }
    friend interval sub_r_i (double const & x, interval i) { return interval::sub_r_i(x, i); }
    friend interval mul     (interval const & i, interval const & j) { return interval::mul(i, j); }
    friend interval mul_i_r (interval const & i, double const x) { return interval::mul_i_r(i, x); }
    friend interval mul_r_i (double const x, interval i) { return interval::mul_r_i(x, i); }
    friend interval div     (interval const & i, interval const & j) { return interval::div(i, j); }
    friend interval div_i_r (interval const & i, double const x) { return interval::div_i_r(i, x); }
    friend interval div_r_i (double const x, interval i) { return interval::div_r_i(x, i); }
    friend interval pow     (interval const & i, interval const & n) { return interval::pow(i, n); }
    friend interval neg     (interval const & i) { return interval::neg(i); }
    friend interval sqr     (interval const & i) { return interval::sqr(i); }
    friend interval sqrt    (interval const & i) { return interval::sqrt(i); }
    friend interval exp     (interval const & i) { return interval::exp(i); }
    friend interval log     (interval const & i) { return interval::log(i); }
    friend interval sin     (interval const & i) { return interval::sin(i); }
    friend interval cos     (interval const & i) { return interval::cos(i); }
    friend interval tan     (interval const & i) { return interval::tan(i); }
    friend interval cosh    (interval const & i) { return interval::cosh(i); }
    friend interval sinh    (interval const & i) { return interval::sinh(i); }
    friend interval tanh    (interval const & i) { return interval::tanh(i); }
    friend interval asin    (interval const & i) { return interval::asin(i); }
    friend interval acos    (interval const & i) { return interval::acos(i); }
    friend interval atan    (interval const & i) { return interval::atan(i); }
    friend interval asinh   (interval const & i) { return interval::asinh(i); }
    friend interval acosh   (interval const & i) { return interval::acosh(i); }
    friend interval atanh   (interval const & i) { return interval::atanh(i); }
    friend interval matan   (interval const & i) { return interval::matan(i); }
    friend interval safesqrt(interval const & i) { return interval::safesqrt(i); }
    friend interval nthroot (interval const & i, interval const & n) { return interval::nthroot(i, n); }
    friend interval abs     (interval const & i) { return interval::abs(i); }
    friend interval min     (interval const & i, interval const & j) { return interval::min(i, j); }
    friend interval max     (interval const & i, interval const & j) { return interval::max(i, j); }
    friend interval atan2   (interval const & y, interval const & x) { return interval::atan2(y, x); }
    friend interval inter   (interval const & i, interval const & j) { return interval::inter(i, j); }
    friend interval minus   (interval const & i, interval const & j) { return interval::minus(i, j); }
    interval & operator= (interval const & i) { inf = i.inf; sup = i.sup; return *this; }
    interval & operator= (double const x)     { setPoint(x); return *this; }
    interval   operator- () const             { return neg(*this); }
    interval & operator+=(interval const & i) { return add(i); }
    interval & operator-=(interval const & i) { return sub(i); }
    interval & operator*=(interval const & i) { return mul(i); }
    interval & operator/=(interval const & i) { return div(i); }
    interval & operator+=(double const x) { return add_r(x); }
    interval & operator-=(double const x) { return sub_i_r(x); }
    interval & operator*=(double const x) { return mul_r(x); }
    interval & operator/=(double const x) { return div_i_r(x); }
    friend bool     operator==(interval const & i, interval const & j) { return i.equals(j); }
    friend bool     operator!=(interval const & i, interval const & j) { return !i.equals(j); }
    friend interval operator+(interval i, interval const & j) { i += j; return i; }
    friend interval operator-(interval i, interval const & j) { i -= j; return i; }
    friend interval operator*(interval i, interval const & j) { i *= j; return i; }
    friend interval operator/(interval i, interval const & j) { i /= j; return i; }
    friend interval operator+(interval i, double const x) { i += x; return i; }
    friend interval operator-(interval i, double const x) { i -= x; return i; }
    friend interval operator*(interval i, double const x) { i *= x; return i; }
    friend interval operator/(interval i, double const x) { i /= x; return i; }
    friend interval operator+(double const x, interval i) { i += x; return i; }
    friend interval operator-(double const x, interval i) { i.sub_r_i(x); return i; }
    friend interval operator*(double const x, interval i) { i *= x; return i; }
    friend interval operator/(double const x, interval i) { i.div_r_i(x); return i; }
};

/* Returns x-offset in dest=[a,b], offset := step*(b-a), step integer */
double translate (double x, interval & dest, int rounding,
                  interval const & step, interval const & offset);

std::ostream & operator<<(std::ostream & out, interval const & i);
std::istream & operator>>(std::istream & in, interval & i);
}
