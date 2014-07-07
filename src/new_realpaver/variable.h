#pragma once

#include <string>
#include "new_realpaver/container.h"
#include "new_realpaver/unionInterval.h"

namespace realpaver {

class variable {
private:
    bool _decision;
    bool _integer;
    bool _real;
    bool _rel_prec; // true -> rel, false -> abs
    double _prec;
    unsigned int _constrained;
    unionInterval _domain;

public:
    std::string const _name;
    variable(std::string const & s) : _name(s) { }
    bool isDecision() const { return _decision; }
    bool isInteger() const { return _integer; }
    bool isReal() const { return _real; }
    bool isRelPrec() const { return _rel_prec; }
    bool isAbsPrec() const { return !_rel_prec; }
    double getPrec() const { return _prec; }
    unionInterval getDomain() const { return _domain; }
    unsigned getConstrained() const { return _constrained; }

    void setDecision(bool const b = true) { _decision = b; }
    void setInteger(bool const b = true) { _integer = b; }
    void setReal(bool const b = true) { _real = b; }
    void setRelPrec(bool const b = true) { _rel_prec = b; }
    void setAbsPrec(bool const b = true) { _rel_prec = !b; }
    void setPrec(double const p) { _prec = p; }
    void getDomain(unionInterval const & u) { _domain = u; }
    void setConstrained(unsigned int const c) { _constrained = c; }
    void incConstrained() { ++_constrained; }
    void decConstrained() { if (_constrained != 0) --_constrained; }

    friend std::ostream & operator<<(std::ostream & out, variable const & v) {
        out << v._name;
        return out;
    }
};
}
