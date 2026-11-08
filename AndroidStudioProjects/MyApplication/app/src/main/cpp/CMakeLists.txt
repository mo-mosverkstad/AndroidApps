cmake_minimum_required(VERSION 3.22.1)

project(editorcore LANGUAGES CXX)

# The portable core lives outside the Android source set so it can also be
# configured and tested directly on a desktop host. Its own tests are skipped
# here: Gradle only needs the library.
set(EDITOR_CORE_TESTS OFF CACHE BOOL "" FORCE)
add_subdirectory(
        ${CMAKE_CURRENT_SOURCE_DIR}/../../../../native
        ${CMAKE_CURRENT_BINARY_DIR}/editor_core
)

add_library(editorcore SHARED editor_jni.cpp)

target_link_libraries(editorcore PRIVATE editor_core log)
