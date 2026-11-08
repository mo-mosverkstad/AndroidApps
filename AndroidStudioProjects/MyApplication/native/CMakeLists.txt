cmake_minimum_required(VERSION 3.22)

project(editor_core LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# ---------------------------------------------------------------------------
# editor_core: the portable editor engine.
#
# Deliberately free of Android, JNI and platform headers so it can be built
# and tested on a desktop host. All text is UTF-16 (std::u16string) so that
# offsets line up 1:1 with java.lang.String / Compose TextRange.
# ---------------------------------------------------------------------------
add_library(editor_core STATIC
        src/piece_table.cpp
        src/document.cpp
        src/text_diff.cpp
        src/editor_model.cpp
)

target_include_directories(editor_core PUBLIC include)

set_target_properties(editor_core PROPERTIES POSITION_INDEPENDENT_CODE ON)

if (MSVC)
    target_compile_options(editor_core PRIVATE /W4 /permissive-)
else ()
    target_compile_options(editor_core PRIVATE -Wall -Wextra -Wpedantic)
endif ()

# Tests are built when this project is configured directly (desktop dev loop),
# and skipped when it is pulled in as a subdirectory by the Android build.
option(EDITOR_CORE_TESTS "Build the editor_core unit tests" ${PROJECT_IS_TOP_LEVEL})

if (EDITOR_CORE_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif ()
