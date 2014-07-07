project(new_realpaver)

add_library(new_realpaver
  box.cpp
  constant.cpp
  function.cpp
  interval.cpp
  matrix.cpp
  unionInterval.cpp
  )
target_link_libraries(new_realpaver util)
