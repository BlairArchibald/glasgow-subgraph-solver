set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

link_libraries(glasgow_subgraphs)

find_package(Boost 1.74 COMPONENTS program_options container REQUIRED)
include_directories(${Boost_INCLUDE_DIR})

add_executable(glasgow_subgraph_solver glasgow_subgraph_solver.cc)
target_link_libraries(glasgow_subgraph_solver LINK_PUBLIC ${Boost_LIBRARIES})

add_executable(glasgow_clique_solver glasgow_clique_solver.cc)
target_link_libraries(glasgow_clique_solver LINK_PUBLIC ${Boost_LIBRARIES})

add_executable(glasgow_common_subgraph_solver glasgow_common_subgraph_solver.cc)
target_link_libraries(glasgow_common_subgraph_solver LINK_PUBLIC ${Boost_LIBRARIES})

add_executable(create_random_graph create_random_graph.cc)
target_link_libraries(create_random_graph LINK_PUBLIC ${Boost_LIBRARIES})

add_executable(convert_to_lad convert_to_lad.cc)
target_link_libraries(convert_to_lad LINK_PUBLIC ${Boost_LIBRARIES})

# GBS
add_library(glasgow_bigraph_lib "glasgow_bigraph_lib.cc")
set_target_properties(glasgow_bigraph_lib PROPERTIES PUBLIC_HEADER "glasgow_bigraph_lib.hh")
# add_library(glasgow_bigraph_lib_shared SHARED "glasgow_bigraph_lib.cc")
include(GNUInstallDirs)
install(TARGETS glasgow_bigraph_lib
  PUBLIC_HEADER
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/glasgow_bigraph_lib
)
