add_library(opensmt_api opensmt_c.C OpenSMTContext.C)
target_link_libraries(opensmt_api util)
add_dependencies(opensmt_api CAPD4)
add_dependencies(opensmt_api JSON11)
