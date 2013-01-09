#if !defined(_HANDLE_UNEXPECTED_TERMINATE_)
#define _HANDLE_UNEXPECTED_TERMINATE_

#include <iostream>
#include <cstdlib>
#include "capd/auxil/ofstreamcout.h"

extern ofstreamcout fcout;

void handle_unexpected() {
  fcout << "unexpected exception thrown" << std::endl;
  exit(1);
}

void handle_terminate() {
  fcout << "terminate() called" << std::endl;
  exit(1);
}

#endif //_HANDLE_UNEXPECTED_TERMINATE_


