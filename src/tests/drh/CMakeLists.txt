set(DREACH_BINARY ${DREAL_SOURCE_DIR}/../bin/dReach)
SET(DRH_INSTANCES "bouncing_ball.drh")

FOREACH(instance ${DRH_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_drh_${instance_name}"
    COMMAND "${DREAL_SOURCE_DIR}/tests/drh/test.sh"
    ${DREACH_BINARY} ${CMAKE_CURRENT_LIST_DIR} ${instance})
  set_tests_properties("regression_drh_${instance_name}" PROPERTIES LABELS "drh_normal")
ENDFOREACH(instance)
