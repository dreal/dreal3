#pragma once

#include "realpaver/interval.h"
#include "realpaver/variable.h"
#include "realpaver/box.h"
#include "realpaver/projection.h"

namespace realpaver {

class erep {
private:
    std::vector<erep*> _childs;
    int                _var;
    unsigned int       _ref;
    std::string        _cst;

public:
    erep();
    erep(int const v);
    erep(std::string const & s, interval const & i);
    erep(erep const & e);
    void copy(erep const & e);
    void replace(int const v, erep e);
    int countNode();

    bool eval(box const & b);
    bool project(box const & b);
    bool isDerivable();
    bool deriv_num();
    erep deriv_symb(int v);

    std::vector<erep*> getChilds() const { return _childs; }
    erep*              getLeft()   const { return _childs[0]; }
    erep*              getRight()  const { return _childs[1]; }
    erep*              getSub()    const { return _childs[0]; }
    unsigned int       getArity()  const { return _childs.size(); }
    unsigned int       getRef()    const { return _ref; }


};

}
