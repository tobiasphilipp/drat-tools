cmake_minimum_required(VERSION 2.6)
project(drat-fz)

find_path(TOOLS_PATH tools/ ${PROJECT_SOURCE_DIR})

if(NOT TOOLS_PATH)
    message(FATAL_ERROR "tools not found!")
endif()

include_directories("${PROJECT_BINARY_DIR}")

add_library(verificator_caller SHARED Verificator_Caller.cpp)
add_library(fuzzer_caller SHARED Fuzzer_Caller.cpp)
add_library(destroyer SHARED Destroyer.cpp)
add_library(cnf_reader SHARED Cnf_Reader.cpp)
  
  configure_file (
  "${PROJECT_SOURCE_DIR}/main.h.in"
  "${PROJECT_BINARY_DIR}/main.h"
  )

add_executable(drat-fz main.cpp)

target_link_libraries(drat-fz verificator_caller)
target_link_libraries(drat-fz fuzzer_caller)
target_link_libraries(drat-fz destroyer)
target_link_libraries(drat-fz cnf_reader)

install(TARGETS drat-fz RUNTIME DESTINATION bin)
