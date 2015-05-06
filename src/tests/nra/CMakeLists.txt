set(DREAL_BINARY ${DREAL_BINARY_DIR}/dReal)
file(GLOB_RECURSE NRA_INSTANCES ${CMAKE_CURRENT_SOURCE_DIR} "*.smt2")
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
  add_test(NAME "regression_nra_tp_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--theory_propagation")
  set_tests_properties("regression_nra_tp_${instance_name}" PROPERTIES LABELS "nra_theory_propagation")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_short_sat_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--short_sat")
  set_tests_properties("regression_nra_short_sat_${instance_name}" PROPERTIES LABELS "nra_short_sat")
ENDFOREACH(instance)
