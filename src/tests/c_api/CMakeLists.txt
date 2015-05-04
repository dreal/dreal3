file(GLOB_RECURSE C_API_INSTANCES ${CMAKE_CURRENT_SOURCE_DIR} "*.c")
list(SORT C_API_INSTANCES)

FOREACH(instance ${C_API_INSTANCES})
  GET_FILENAME_COMPONENT(instance_name ${instance} NAME)

  add_executable(c_api_${instance_name} ${instance_name})
  target_link_libraries(c_api_${instance_name} dreal gtest ${EXTRA_LIBS} stdc++)
  add_test(c_api_${instance_name} ${CMAKE_CURRENT_BINARY_DIR}/c_api_${instance_name})
  set_tests_properties("c_api_${instance_name}" PROPERTIES LABELS "c_api")
ENDFOREACH(instance)

# add_executable(c_api_example_01 example_01.c)
# target_link_libraries(c_api_example_01 dreal gtest ${EXTRA_LIBS} stdc++)
# add_test(c_api_example_01 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_01)

# add_executable(c_api_example_02 example_02.c)
# target_link_libraries(c_api_example_02 dreal gtest ${EXTRA_LIBS} stdc++)
# add_test(c_api_example_02 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_02)

# add_executable(c_api_example_03 example_03.c)
# target_link_libraries(c_api_example_03 dreal gtest ${EXTRA_LIBS} stdc++)
# add_test(c_api_example_03 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_03)

# add_executable(c_api_example_04 example_04.c)
# target_link_libraries(c_api_example_04 dreal gtest ${EXTRA_LIBS} stdc++)
# add_test(c_api_example_04 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_04)

# add_executable(c_api_dreal.jl_01 dreal.jl.1.c)
# target_link_libraries(c_api_dreal.jl_01 dreal gtest ${EXTRA_LIBS} stdc++)
# add_test(c_api_dreal.jl_01 ${CMAKE_CURRENT_BINARY_DIR}/c_api_dreal.jl_01)
