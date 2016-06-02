set(DREAL_BINARY ${DREAL_BINARY_DIR}/dReal)
file(GLOB NRA_ODE_INSTANCES "*.smt2")
list(SORT NRA_ODE_INSTANCES)

FOREACH(instance ${NRA_ODE_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ode_normal_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra_ode/test.sh" ${DREAL_BINARY} ${instance})
  set_tests_properties("regression_nra_ode_normal_${instance_name}" PROPERTIES LABELS "nra_ode_normal")
ENDFOREACH(instance)

FOREACH(instance ${NRA_ODE_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ode_short_sat_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra_ode/test.sh" ${DREAL_BINARY} ${instance} "--short_sat")
  set_tests_properties("regression_nra_ode_short_sat_${instance_name}" PROPERTIES LABELS "nra_ode_short_sat")
ENDFOREACH(instance)

FOREACH(instance ${NRA_ODE_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ode_sampling_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra_ode/test.sh" ${DREAL_BINARY} ${instance} "--ode-sampling")
  set_tests_properties("regression_nra_ode_sampling_${instance_name}" PROPERTIES LABELS "nra_ode_sampling")
ENDFOREACH(instance)

FOREACH(instance ${NRA_ODE_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ode_worklist_fp_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra_ode/test.sh" ${DREAL_BINARY} ${instance} "--worklist-fp")
  set_tests_properties("regression_nra_ode_worklist_fp_${instance_name}" PROPERTIES LABELS "nra_ode_worklist_fp")
ENDFOREACH(instance)

FOREACH(instance ${NRA_ODE_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ode_cache_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra_ode/test.sh" ${DREAL_BINARY} ${instance} "--ode-cache")
  set_tests_properties("regression_nra_ode_cache_${instance_name}" PROPERTIES LABELS "nra_ode_cache")
ENDFOREACH(instance)

FOREACH(instance ${NRA_ODE_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ode_ncbt_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra_ode/test.sh" ${DREAL_BINARY} ${instance} "--ncbt")
  set_tests_properties("regression_nra_ode_ncbt_${instance_name}" PROPERTIES LABELS "nra_ode_ncbt")
ENDFOREACH(instance)

FOREACH(instance ${NRA_ODE_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_ode_delta_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra_ode/test.sh" ${DREAL_BINARY} ${instance} "--delta")
  set_tests_properties("regression_nra_ode_delta_${instance_name}" PROPERTIES LABELS "nra_ode_delta")
ENDFOREACH(instance)
