#ifndef _CAPD_BITSET_EMBDIMEXCEPTION_H_ 
#define _CAPD_BITSET_EMBDIMEXCEPTION_H_ 
#include <stdexcept>

struct EmbDimException : std::out_of_range{
  explicit EmbDimException(const std::string& whatString):std::out_of_range(whatString){};
};

struct DimException : std::out_of_range{
  explicit DimException(const std::string& whatString):std::out_of_range(whatString){};
};

#endif // _CAPD_BITSET_EMBDIMEXCEPTION_H_ 
