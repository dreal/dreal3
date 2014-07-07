#include <algorithm>
#include <cfenv>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <limits>
#include <stdexcept>
#include <string>
#include <sstream>
#include "new_realpaver/interval.h"
#include "interval/filib.hpp"

using std::cerr;
using std::cout;
using std::endl;
using std::istream;
using std::numeric_limits;
using std::ostream;
using std::stod;
using std::streampos;
using std::string;
using std::stringstream;
using std::invalid_argument;

namespace realpaver {

void ROUND_UPWARD() { std::fesetround(FE_UPWARD); }
void ROUND_DOWNWARD() { std::fesetround(FE_DOWNWARD); }

double splitPoint(double x, double y, int h, int n) {
    double a = std::max(x, DBL_MIN);
    double b = std::min(y, DBL_MAX);
    if (a == b) { /* [r,r] || [-oo,MinReal] || [MaxReal,+oo] */
        return a;
    } else if (b == nextafter(a, +interval::DBL_INFINITY)) {  /* [r,r+] || [-oo,succ MinReal] */
        /* || [pred MaxReal,+oo] */
        if (x == (-interval::DBL_INFINITY)) {
            return DBL_MIN;
        } else if (y == interval::DBL_INFINITY) {
            return DBL_MAX;
        } else {
            return a;
        }
    } else {                            /* [r,s] with s > r+ */
        double div = static_cast<double>(n) / static_cast<double>(h);
        double c = a * (1.0 - div) + b * div;
        if (c > a && c < b) {
            return c;
        } else {
            return nextafter(a, +interval::DBL_INFINITY);
        }
    }
}

bool interval::isCanonical() const {
    // [-oo, min]
    if ((inf == -DBL_INFINITY) &&
        (sup == DBL_MIN))
        return true;
    // [max, oo]
    if ((sup == +DBL_INFINITY) &&
        (inf == DBL_MAX))
        return true;
    // [x, nextafter(x)]
    if (sup <= nextafter(inf, +DBL_INFINITY))
        return true;
    return false;
}

double interval::distance(interval const & i) const {
    if (sup < i.inf) { return i.inf - sup; }
    if (i.sup < inf) { return inf - i.sup; }
    return 0.0;
}

bool interval::isRealline() const {
    return inf == -DBL_INFINITY && sup == +DBL_INFINITY;
}

interval & interval::setRealline() {
    // [-oo, +oo]
    inf = -DBL_INFINITY;
    sup = +DBL_INFINITY;
    return *this;
}

double interval::midpoint() const {
    if (isRealline()) { return 0.0; }
    return splitPoint(inf, sup, 2, 1);
}

bool interval::improved(interval const & old, double imp) const {
    if (equals(old)) return false;
    if (old.inf == -DBL_INFINITY && inf != -DBL_INFINITY)
        return true;
    if (old.sup == +DBL_INFINITY && sup != +DBL_INFINITY)
        return true;
    if (old.finite() && (width() < imp * old.width()))
        return true;
    return false;
}

double const interval::HALF_PI = std::asin(1.0);
double const interval::PI = 2 * HALF_PI;
double const interval::PI_2 = 2 * PI;
double const interval::PI_4 = 4 * PI;
double const interval::HALF_PI_3 = 3 * HALF_PI;
double const interval::HALF_PI_5 = 5 * HALF_PI;
double const interval::HALF_PI_7 = 7 * HALF_PI;
double const interval::DBL_INFINITY = numeric_limits<double>::infinity();
interval const interval::empty = interval(interval::DBL_INFINITY, -interval::DBL_INFINITY);
interval const interval::realline = interval();

interval::interval(std::istream & in) {
    in >> std::ws; // remove whitespaces
    char c = in.get();
    if (c == '[') {
        // [lb, ub]
        ROUND_DOWNWARD();
        in >> inf;
        if (in.fail()) { throw invalid_argument("interval(std::istream & in): lb is not a number"); }
        in >> std::ws;
        c = in.get();
        if (c != ',') { throw invalid_argument("interval(std::istream & in): ',' expected"); }
        in >> std::ws;
        ROUND_UPWARD();
        in >> sup;
        if (in.fail()) { throw invalid_argument("interval(std::istream & in): ub is not a number"); }
        in >> std::ws;
        c = in.get();
        if (c != ']') { throw invalid_argument("interval(std::istream & in): ']' expected"); }
    } else {
        // number
        in.unget();
        streampos pos = in.tellg();
        ROUND_DOWNWARD();
        in >> inf;
        if (in.fail()) { throw invalid_argument("interval(std::istream & in): not a number"); }
        in.seekg(pos);
        ROUND_UPWARD();
        in >> sup;
        if (in.fail()) { throw invalid_argument("interval(std::istream & in): not a number"); }
    }
}

interval::interval(std::string const & s) {
    stringstream ss(s);
    *this = interval(ss);
}

// Binary arithmetic operations
bool interval::equal_digits(interval const & i, int const n) const {
    if (n < 0 || infinite() || i.infinite()) { return equals(i); }
    double factor = 1.0;
    for (int k = 0; k < n; ++k) { factor *= 10.0; }
    double const tmp_inf1 = std::trunc(inf * factor) / factor;
    double const tmp_sup1 = std::trunc(sup * factor) / factor;
    double const tmp_inf2 = std::trunc(i.inf * factor) / factor;
    double const tmp_sup2 = std::trunc(i.sup * factor) / factor;
    return tmp_inf1 == tmp_inf2 && tmp_sup1 == tmp_sup2;
}

// i = [a,d] -->  i := [ceil(a),floor(b)]
// Only for bounds within [LONG_MIN,LONG_MAX] for safety reasons
void interval::trunc() {
    if (static_cast<double>(LONG_MIN) <= inf &&
        inf <= static_cast<double>(LONG_MAX)) {
        inf = ceil(inf);
    }
    if (static_cast<double>(LONG_MIN) <= sup &&
        sup <= static_cast<double>(LONG_MAX)) {
        sup = floor(sup);
    }
}

interval & interval::add(interval const & i) {
    ROUND_DOWNWARD();
    inf += i.inf;
    ROUND_UPWARD();
    sup += i.sup;
    return *this;
}

interval & interval::add_r(double const x) {
    ROUND_DOWNWARD();
    inf += x;
    ROUND_UPWARD();
    sup += x;
    return *this;
}

interval & interval::sub(interval const & i) {
    if (this == &i) {
        setZero();
        return *this;
    }
    ROUND_DOWNWARD();
    inf -= i.sup;
    ROUND_UPWARD();
    sup -= i.inf;
    return *this;
}

interval & interval::sub_i_r(double const x) {
    ROUND_DOWNWARD();
    inf -= x;
    ROUND_UPWARD();
    sup -= x;
    return *this;
}

interval & interval::sub_r_i(double const x) {
    ROUND_DOWNWARD();
    inf = x - sup;
    ROUND_UPWARD();
    sup = x - inf;
    return *this;
}

interval & interval::mul(interval const & i) {
    filib_interval fi(inf, sup);
    filib_interval fj(i.inf, i.sup);
    set(fi * fj);
    return *this;
}

interval & interval::mul_r(double const x) {
    if (x == 0.0) {
        inf = sup = 0.0;
    } else if (x > 0.0) {
        ROUND_DOWNWARD();
        inf *= x;
        ROUND_UPWARD();
        sup *= x;
    } else {
        double const tmp_inf = inf;
        ROUND_DOWNWARD();
        inf = sup * x;
        ROUND_UPWARD();
        sup = tmp_inf * x;
    }
    return *this;
}

interval & interval::div(interval const & i) {
    if (this == &i) {
        setOne();
        return *this;
    }
    filib_interval fi(inf, sup);
    filib_interval fj(i.inf, i.sup);
    set(fi / fj);
    return *this;
}

interval & interval::div_i_r(double const x) {
    if (x ==0.0) {
        setRealline();
    } else if (x > 0.0) {
        ROUND_DOWNWARD();
        inf = inf / x;
        ROUND_UPWARD();
        sup = sup / x;
    } else {
        double const tmp_inf = inf;
        ROUND_DOWNWARD();
        inf = sup * x;
        ROUND_UPWARD();
        sup = tmp_inf * x;
    }
    return *this;
}

interval & interval::div_r_i(double const x) {
    if (x == 0.0) { /* x=[0,0] */
        if (includes(0.0)) {
            setRealline();
        } else {
            setPoint(0.0);
        }
    } else if (includes(0.0)) {
        /* The problem is to manage divisions by 0 */
        if (isZero()) { /* i=[0,0] */
            setRealline();
        } else if (inf == 0.0) { /* i=[0,b], b>0 */
            if (x > 0.0) { /* [r,r]/[0,b]=[r/b,+oo] */
                ROUND_DOWNWARD();
                set(x/sup, +DBL_INFINITY);
            } else { /* x is negative */
                ROUND_UPWARD();
                set(-DBL_INFINITY, x/sup);
            }
        } else if (sup == 0.0) { /* i=[a,0], a<0 */
            if (x > 0.0) { /* [r,r]/[b,0]=[-oo,r/b] */
                ROUND_UPWARD();
                set(-DBL_INFINITY, x/inf);
            } else { /* x is negative */ /* [r,r]/[b,0]=[r/b,+oo] */
                ROUND_DOWNWARD();
                set(x/inf, +DBL_INFINITY);
            }
        } else { /* i=[a,b], a<0<b */
            setRealline();
        }
    } else { /* i does not contain 0 and x!=0 => standard division */
        if (x > 0.0) {
            double const tmp_inf = inf;
            ROUND_DOWNWARD();
            inf = x / sup;
            ROUND_UPWARD();
            sup = x / tmp_inf;
        } else {
            ROUND_DOWNWARD();
            inf = x/inf;
            ROUND_UPWARD();
            sup = x/sup;
        }
    }
    return *this;
}

interval & interval::pow(interval const & n) {
    filib_interval f1(inf, sup);
    filib_interval f2(n.inf, n.sup);
    set(filib::pow(f1, f2));
    return *this;
}

// Unary arithmetic operations
interval & interval::neg() {
    double tmp_inf = inf;
    ROUND_DOWNWARD();
    inf = -sup;
    ROUND_UPWARD();
    sup = -tmp_inf;
    return *this;
}
interval & interval::sqr() {
    if (inf >= 0.0) {
        ROUND_DOWNWARD();
        inf = inf * inf;
        ROUND_UPWARD();
        sup = sup * sup;
    } else if (sup <= 0.0) {
        double const tmp_inf = inf;
        ROUND_DOWNWARD();
        inf = sup * sup;
        ROUND_UPWARD();
        sup = tmp_inf * tmp_inf;
    } else if (-inf < sup) {
        inf = 0.0;
        ROUND_UPWARD();
        sup = sup*sup;
    } else {
        ROUND_UPWARD();
        sup = inf * inf;
        inf = 0.0;
    }
    return *this;
}

interval & interval::sqrt() {
    filib_interval f1(std::max(0.0, inf), sup);
    set(interval(::filib::sqrt(f1)));
    return *this;
}

// Elementary functions
interval & interval::exp() {
    filib_interval f1(inf, sup);
    set(interval(::filib::exp(f1)));
    return *this;
}

interval & interval::log() {
    filib_interval f1(inf, sup);
    set(interval(::filib::log(f1)));
    return *this;
}

interval & interval::sin() {
    filib_interval f1(inf, sup);
    set(interval(::filib::sin(f1)));
    return *this;
}

interval & interval::cos() {
    filib_interval f1(inf, sup);
    set(interval(::filib::cos(f1)));
    return *this;
}

interval & interval::tan() {
    filib_interval f1(inf, sup);
    set(interval(::filib::tan(f1)));
    return *this;
}

interval & interval::cosh() {
    filib_interval f1(inf, sup);
    set(interval(::filib::cosh(f1)));
    return *this;
}

interval & interval::sinh() {
    filib_interval f1(inf, sup);
    set(interval(::filib::sinh(f1)));
    return *this;
}

interval & interval::tanh() {
    filib_interval f1(inf, sup);
    set(interval(::filib::tanh(f1)));
    return *this;
}

interval & interval::asin() {
    filib_interval f1(inf, sup);
    set(interval(::filib::asin(f1)));
    return *this;
}

interval & interval::acos() {
    filib_interval f1(inf, sup);
    set(interval(::filib::acos(f1)));
    return *this;
}

interval & interval::atan() {
    filib_interval f1(inf, sup);
    set(interval(::filib::atan(f1)));
    return *this;
}

interval & interval::asinh() {
    filib_interval f1(inf, sup);
    set(interval(::filib::asinh(f1)));
    return *this;
}

interval & interval::acosh() {
    filib_interval f1(inf, sup);
    set(interval(::filib::acosh(f1)));
    return *this;
}

interval & interval::atanh() {
    filib_interval f1(inf, sup);
    set(interval(::filib::atanh(f1)));
    return *this;
}

interval & interval::matan() {
    // matan(x) = atn(sqrt(x))/sqrt(x) if x > 0
    // = log ((1 + sqrt(-x)) / (1 - sqrt(-x))) / (2 * sqrt(-x)) if x < 0
    // = 1 if x = 0
    double x_ub = sup;
    double x_lb = inf;
    setEmpty();
    /* atn(sqrt(x))/sqrt(x) if x > 0 */
    if (x_ub > 0.0) {
        interval const sqrt_x = sqrt(interval(std::max(x_lb, DBL_EPSILON), x_ub));
        set(atan(sqrt_x) / sqrt_x); // = atan(sqrt(x)) / sqrt(x) */
    }
    /* log ((1 + sqrt(-x)) / (1 - sqrt(-x))) / (2 * sqrt(-x)) if x < 0 */
    if (x_lb < 0.0) {
        interval const x = interval(x_lb, std::min(x_ub, -DBL_EPSILON));
        interval const sqrt_neg_x = sqrt(-x);
        interval const aux = ((1 + sqrt_neg_x) / (1 - sqrt_neg_x)) / (2 * sqrt_neg_x);
        hull(aux);
    }
    /* 1 if x = 0 */
    if (includes(0.0)) { hull(interval(1.0)); }
    return *this;
}

interval & interval::safesqrt() {
    if (inf < 0.0) {
        inf = 0.0;
    }
    return sqrt();
}

interval & interval::atan2(interval const & x) {
    // Due to the floating-point error, use the following definition:
    // atan2(y,x) = arctan(y/x) if x > 0 (1)
    // = arctan(y/x) + pi if y >= 0, x < 0 (2)
    // = arctan(y/x) - pi if y < 0, x < 0 (3)
    // = + pi/2 if y > 0, x = 0 (4)
    // = - pi/2 if y < 0, x = 0 (5)
    // = undefined if y = 0, x = 0 (6)
    // Another definition is
    // atan2(y,x) = 2 arctan ( y / [sqrt(x^2 + y^2) + x] )
    double x_ub = x.sup;
    double x_lb = x.inf;
    double y_ub = sup;
    double y_lb = inf;
    setEmpty();
    // atan2(y,x) = arctan(y/x) if x > 0 (1)
    if (x_ub > 0.0) {
        interval aux;
        aux.setEmpty();
        interval const x_temp(std::max(x_lb, DBL_EPSILON), x_ub);
        set(atan(*this / x_temp));
    }
    // atan2(y,x) = arctan(y/x) + pi if y >= 0, x < 0 (2)
    if (y_ub >= 0.0 && x_lb < 0.0) {
        interval const x_temp(x_lb, std::min(x_ub, -DBL_EPSILON));
        interval const y_temp(std::max(y_lb, 0.0), y_ub);
        interval const aux = PI + atan(y_temp / x_temp);
        hull(aux);
    }
    // atan2(y,x) = arctan(y/x) - pi if y < 0, x < 0 (3)
    if (y_lb < 0.0 && x_lb < 0.0) {
        interval const x_temp(x_lb, std::min(x_ub, -DBL_EPSILON));
        interval const y_temp(y_lb, std::min(y_ub, -DBL_EPSILON));
        interval const aux = -PI + atan(y_temp / x_temp);
        hull(aux);
    }
    // atan2(y,x) = + pi/2 if y > 0, x = 0 (4)
    if (y_ub > 0.0 && x.includes(0.0)) { hull(interval(HALF_PI)); }
    // atan2(y,x) = - pi/2 if y < 0, x = 0 (5)
    if (y_lb < 0.0 && x.includes(0.0)) { hull(interval(-HALF_PI)); }
    return *this;
}

// result := n-th root of i
// computes only the positive part for even exponent and positive interval
interval & interval::nthroot(interval const & n) {
    // TODO(soonhok): make sure that n is a point?
    int const e = static_cast<int>(n.inf);
    if (e % 2 == 1) {
        if (inf > 0.0) {
            /* result := exp(log(i)/n) */
            log(); /* aux1 := log(i) */
            div(n); /* aux2 := log(i)/n */
            exp(); /* result := exp(log(x)/n) */
        } else if (sup < 0.0) {
            /* result := -exp(log(-i)/n) */
            neg(); /* aux1 := -i */
            log(); /* aux2 := log(-i) */
            div(n); /* aux3 := log(-i)/n */
            exp(); /* aux4 := exp(log(-i)/n) */
            neg(); /* result := -exp(log(-i)/n) */
        } else {
            // i contains 0
            /* computation of left bound */
            if (inf != 0.0) { inf = std::exp(std::log(-inf) / n.inf); }
            /* computation of right bound */
            if (sup != 0.0) { sup = std::exp(std::log(sup) / n.inf); }
        }
    } else {
        // exponent even
        if (sup < 0.0) {
            setEmpty();
        } else if (inf > 0.0) {
            /* only positive interval computed */
            if (e == 2) {
                sqrt();
            } else {
                log(); div_i_r(n.inf); exp();
            }
        } else {
            if (sup == 0.0) {
                setPoint(0.0);
            } else {
                interval aux(sup);
                if (e == 2) {
                    aux.sqrt();
                } else {
                    aux.log();
                    aux.div_i_r(n.inf);
                    aux.exp();
                }
                inf = -sup;
                sup = aux.sup;
            }
        }
    }
    return *this;
}

// result := absolute value (i)
interval & interval::abs() {
    if (inf >= 0.0) {
        // do nothing
    } else if (sup <= 0.0) {
        set(-sup, -inf);
    } else {
        sup = std::max(-inf, sup);
        inf = 0;
    }
    return *this;
}

// result := min(i,j)
interval & interval::min(interval const & i) {
    inf = std::min(inf, i.inf);
    sup = std::min(sup, i.sup);
    return *this;
}

// result := max(i,j)
interval & interval::max(interval const & i) {
    inf = std::max(inf, i.inf);
    sup = std::max(sup, i.sup);
    return *this;
}

interval & interval::inter(interval const & i) {
    inf = std::max(inf, i.inf);
    sup = std::min(sup, i.sup);
    return *this;
}

interval & interval::hull(interval const & i) {
    inf = std::min(inf, i.inf);
    sup = std::max(sup, i.sup);
    return *this;
}

// result := hull (this \ i)
interval & interval::minus(interval const & i) {
    if (i.includes(*this)) {
        // this:   |-------|
        // i   : |-----------|
        setEmpty();
    } else if (i.inf <= inf && includesStrictly(i.sup)) {
        // this:    |--------|
        // i   : |-------|
        //               |---|
        inf = i.sup;
    } else if (i.sup >= sup && includesStrictly(i.inf)) {
        // this: |-------|
        // i   :     |-------|
        //       |---|
        sup = i.inf;
    } else {
        /* i1 and i2 disjoint, or     */
        /* share only one bound, or   */
        /* i2 strictly included in i1 */
        /* no element removed from i1 */
    }
    return *this;
}

/* Returns x - offset in dest=[a,b], offset := step*(b-a), step integer */
double translate(double x, interval & dest, int rounding,
                 interval & step, interval & offset) {
    /* a <= x-step*(b-a) <= b  =>  (x-a)/(b-a) >= step >= (x-b)/(b-a) */
    /* step := 1 + floor( (x-b)/(b-a) ) the smallest integer          */
    /* greater than (x-b)/(b-a)                                       */
    if (dest.includes(x)) {
        step.setPoint(0.0);
        offset.setPoint(0.0);
        return x;
    } else {
        interval wdest;
        double bound;
        ROUND_DOWNWARD();
        wdest.inf = dest.sup - dest.inf;
        ROUND_UPWARD();
        wdest.sup = dest.sup - dest.inf;
        interval xi(x);
        interval bi(dest.sup);

        /* (x-b)/(b-a) must be rounded downward since step >= (x-b)/(b-a) */
        interval aux1 = sub(xi, bi);      /* aux1 := x - b */
        interval aux2 = div(aux1, wdest); /* aux2 := (x-b)/(b-a) */
        step.setPoint(1.0 + floor(aux2.inf));
        offset = mul_r_i(step.inf, wdest);
        aux1 = sub(xi, offset);
        // TODO(soonhoK): fix this
        // if (rounding == ROUND_VALUE_DOWN) {
        if (rounding == 0) {
            bound = aux1.inf;
        } else {
            bound = aux1.sup;
        }
        if (bound < dest.inf) {
            return dest.inf;
        } else if (bound > dest.sup) {
            return dest.sup;
        } else {
            return bound;
        }
    }
}

ostream & operator<<(ostream & out, interval const & i) {
    if (i.isEmpty()) { out << "empty"; return out; }
    if (i.isPoint()) { out << i.inf; return out; }
    ROUND_DOWNWARD();
    out << "[" << std::setprecision(20) << i.inf;
    ROUND_UPWARD();
    out << ", " << std::setprecision(20) << i.sup << "]";
    return out;
}
istream & operator>>(istream & in, interval & i) {
    i = interval(in);
    return in;
}

}
