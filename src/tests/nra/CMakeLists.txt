# FOREACH(infileName ${inFiles})
#     MESSAGE(STATUS "Process file: ${infileName}")

#     # Generate output file name
#     STRING(REGEX REPLACE ".in\$" "" outfileName "${infileName}")
#     SET(outfile "${CMAKE_CURRENT_BINARY_DIR}/${outfileName}")
#     MESSAGE(STATUS "Output file: ${outfile}")

#     # Generate input file name
#     SET(infile "${CMAKE_CURRENT_SOURCE_DIR}/${infileName}")

#     # Custom command to do the processing
#     ADD_CUSTOM_COMMAND(OUTPUT "${outfile}"
#         COMMAND ${processorLocation}
#         "${infile}" "${outfile}"
#         DEPENDS "${infile}" processor # depends on the 'processor'
#         COMMENT "do something")

#     # Finally remember the output file for dependencies
#     SET(outFiles ${outFiles} "${outfile}")
# ENDFOREACH(infileName)


set(DREAL_BINARY ${CMAKE_CURRENT_BINARY_DIR}/../../dReal)
file(GLOB_RECURSE NRA_INSTANCES ${DREAL_SOURCE_DIR}/tests/nra "*.smt2")

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh" ${DREAL_BINARY} ${instance})
ENDFOREACH(instance)


#add_test(NAME leantests
#         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
#         COMMAND "./test.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
#add_test(NAME leanslowtests
#         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/slow"
#         COMMAND "../test.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
