add_executable(editor_core_tests
        test_framework.cpp
        test_piece_table.cpp
        test_document.cpp
        test_history.cpp
        test_text_diff.cpp
        test_editor_model.cpp
)

target_link_libraries(editor_core_tests PRIVATE editor_core)
target_include_directories(editor_core_tests PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

if (MSVC)
    target_compile_options(editor_core_tests PRIVATE /W4 /permissive- /utf-8)
else ()
    target_compile_options(editor_core_tests PRIVATE -Wall -Wextra)
endif ()

add_test(NAME editor_core_tests COMMAND editor_core_tests)
