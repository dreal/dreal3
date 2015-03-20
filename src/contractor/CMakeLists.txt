add_library(contractor
  contractor_basic.cpp
  contractor_ibex.cpp
  contractor_capd4.cpp
  )
add_dependencies(contractor CAPD4)
add_dependencies(contractor IBEX)
add_dependencies(contractor JSON11)
add_dependencies(contractor util)
