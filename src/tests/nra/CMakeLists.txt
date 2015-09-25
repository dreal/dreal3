set(DREAL_BINARY ${DREAL_BINARY_DIR}/dReal)
file(GLOB NRA_INSTANCES "*.smt2")
list(SORT NRA_INSTANCES)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_normal_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance})
  set_tests_properties("regression_nra_normal_${instance_name}" PROPERTIES LABELS "nra_normal")
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
  add_test(NAME "regression_nra_polytope_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--polytope")
  set_tests_properties("regression_nra_polytope_${instance_name}" PROPERTIES LABELS "nra_polytope")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_short_sat_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--short_sat")
  set_tests_properties("regression_nra_short_sat_${instance_name}" PROPERTIES LABELS "nra_short_sat")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ncbt_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--ncbt")
  set_tests_properties("regression_nra_ncbt_${instance_name}" PROPERTIES LABELS "nra_ncbt")
ENDFOREACH(instance)
