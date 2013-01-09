#include "capd/vectalg/mplib.h"
#include "capd/geomset/MatrixAffineSet.hpp"

#ifdef __HAVE_MPFR__
namespace capd{
namespace geomset{
  template class MatrixAffineSet<capd::MpIMatrix >;
}}
#endif
