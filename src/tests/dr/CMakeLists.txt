set(DREAL_BINARY ${DREAL_BINARY_DIR}/dReal)
file(GLOB DR_INSTANCES "*.dr")
list(SORT DR_INSTANCES)

FOREACH(instance ${DR_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_dr_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/dr/test.sh"
           ${DREAL_BINARY} ${instance})
  set_tests_properties("regression_dr_${instance_name}" PROPERTIES LABELS "dr")
ENDFOREACH(instance)
