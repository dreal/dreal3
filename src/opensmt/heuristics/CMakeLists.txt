add_library(opensmt_heuristics heuristic.cpp  hybrid_heuristic.cpp plan_heuristic.cpp)
target_link_libraries(opensmt_heuristics gflags)
