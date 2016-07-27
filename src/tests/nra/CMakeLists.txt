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

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_worklist_fp_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--worklist-fp")
  set_tests_properties("regression_nra_worklist_fp_${instance_name}" PROPERTIES LABELS "nra_worklist_fp")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_simul_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--simulation")
  set_tests_properties("regression_nra_simul_${instance_name}" PROPERTIES LABELS "nra_simul")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_multiheuristic_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--multiheuristic")
  set_tests_properties("regression_nra_multiheuristic_${instance_name}" PROPERTIES LABELS "nra_multiheuristic")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_multiprune_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--multiprune")
  set_tests_properties("regression_nra_multiprune_${instance_name}" PROPERTIES LABELS "nra_multiprune")
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
  add_test(NAME "regression_nra_slack_level_1_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--slack-level 1")
  set_tests_properties("regression_nra_slack_level_1_${instance_name}" PROPERTIES LABELS "nra_slack_level_1")
ENDFOREACH(instance)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_slack_level_2_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--slack-level 2")
  set_tests_properties("regression_nra_slack_level_2_${instance_name}" PROPERTIES LABELS "nra_slack_level_2")
ENDFOREACH(instance)

IF(USE_GLPK)
    FOREACH(instance ${NRA_INSTANCES})
        GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
        add_test(NAME "regression_nra_lp_icp_${instance_name}"
            COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
            ${DREAL_BINARY} ${instance} "--lp-icp")
        set_tests_properties("regression_nra_lp_icp_${instance_name}" PROPERTIES LABELS "nra_lp_icp")
    ENDFOREACH(instance)

    FOREACH(instance ${NRA_INSTANCES})
        GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
        add_test(NAME "regression_nra_lp_icp_prune_${instance_name}"
            COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
            ${DREAL_BINARY} ${instance} "--lp-icp-prune")
        set_tests_properties("regression_nra_lp_icp_prune_${instance_name}" PROPERTIES LABELS "nra_lp_icp_prune")
    ENDFOREACH(instance)
ENDIF(USE_GLPK)

FOREACH(instance ${NRA_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)
  add_test(NAME "regression_nra_scoring_icp_${instance_name}"
           COMMAND "${DREAL_SOURCE_DIR}/tests/nra/test.sh"
           ${DREAL_BINARY} ${instance} "--scoring-icp")
  set_tests_properties("regression_nra_scoring_icp_${instance_name}" PROPERTIES LABELS "nra_scoring_icp")
ENDFOREACH(instance)
