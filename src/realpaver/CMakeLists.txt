project(realpaver)

add_library(realpaver rp_interval.c rp_box.c rp_constant.c rp_container.c
rp_expression_symbol.c rp_function.c rp_lexer.c rp_memory.c
rp_operator_sat.c rp_problem.c rp_stream.c rp_variable.c rp_clock.c
rp_constraint.c rp_expression.c rp_float.c rp_matrix.c
rp_operator_num.c rp_parser.c rp_projection.c rp_union_interval.c
rp_propagator.cpp rp_box_set.cpp rp_operator.cpp
rp_operator_factory.cpp rp_output.cpp rp_solver.cpp rp_split.cpp
rp_split_selector.cpp rp_verification.cpp)
