set(DREAL_BINARY ${DREAL_SOURCE_DIR}/../bin/dReal)
file(GLOB_RECURSE NRA_INSTANCES ${DREAL_SOURCE_DIR}/tests/nra "*.smt2")
list(SORT NRA_INSTANCES)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance})
  set_tests_properties("regression_nra_${instance_name}" PROPERTIES LABELS "nra_normal")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_delta_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--delta")
  set_tests_properties("regression_nra_delta_${instance_name}" PROPERTIES LABELS "nra_delta")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_delta_heuristic_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--delta --delta_heuristic")
  set_tests_properties("regression_nra_delta_heuristic_${instance_name}" PROPERTIES LABELS "nra_delta_heuristic")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_heuristic_short_sat_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--delta --delta_heuristic --short_sat")
  set_tests_properties("regression_nra_heuristic_short_sat_${instance_name}" PROPERTIES LABELS "nra_delta_heuristic_short_sat")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_short_sat_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--short_sat")
  set_tests_properties("regression_nra_short_sat_${instance_name}" PROPERTIES LABELS "nra_short_sat")
ENDFOREACH(instance)
