project(filib)

#file(GLOB_RECURSE C_FILES ${CMAKE_CURRENT_SOURCE_DIR} *.c *.h)
#set_source_files_properties(${C_FILES} PROPERTIES LANGUAGE CXX)

#if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
#  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -x c++")
#endif ()

add_library(filib
j_acos.c j_asin.c j_cos.c j_erf.c j_expm.c j_log2.c j_sqrt.c q_acot.c
q_asin.c q_atnh.c q_cosh.c q_ep1.c q_ex10.c q_glbl.c q_log2.c q_scan.c
q_sqr.c q_tanh.c j_acot.c j_asnh.c j_cosh.c j_ex10.c j_lg10.c j_sin.c
j_tan.c q_acsh.c q_asnh.c q_comp.c q_cot.c q_epm1.c q_exp.c q_lg10.c
q_pred.c q_sin.c q_sqrt.c j_acsh.c j_atan.c j_cot.c j_exp.c j_lg1p.c
j_sinh.c j_tanh.c q_acth.c q_atan.c q_cos.c q_coth.c q_erf.c q_exp2.c
q_log.c q_prnt.c q_sin1.c q_succ.c j_acth.c j_atnh.c j_coth.c j_exp2.c
j_log.c j_sqr.c q_acos.c q_ari.c q_atn1.c q_cos1.c q_cth1.c q_errm.c
q_expm.c q_log1.c q_rtrg.c q_sinh.c q_tan.c
)
