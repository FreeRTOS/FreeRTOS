# Taken from amazon-freertos repository

#function to create the test executable
function(create_test test_name
                     test_src
                     link_list
                     dep_list
                     include_list
                     config
                     mock_dir)
    set(mocks_dir "${CMAKE_CURRENT_BINARY_DIR}/${mock_dir}")
    include (CTest)
    get_filename_component(test_src_absolute ${test_src} ABSOLUTE)
    add_custom_command(OUTPUT ${test_name}_runner.c
                  COMMAND ruby
                    ${CMOCK_DIR}/vendor/unity/auto/generate_test_runner.rb
                    ${config}
                    ${test_src_absolute}
                    ${test_name}_runner.c
                  DEPENDS ${test_src}
        )
    add_executable(${test_name} ${test_src} ${test_name}_runner.c)
    set_target_properties(${test_name} PROPERTIES
            COMPILE_FLAG "-O0 -ggdb"
            RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin/tests"
            INSTALL_RPATH_USE_LINK_PATH TRUE
            LINK_FLAGS " \
                -Wl,-rpath,${CMAKE_BINARY_DIR}/lib \
                -Wl,-rpath,${CMAKE_CURRENT_BINARY_DIR}/lib"
        )
    target_include_directories(${test_name} PUBLIC
                               ${mocks_dir}
                               ${include_list}
        )

    target_link_directories(${test_name} PUBLIC
                            ${CMAKE_CURRENT_BINARY_DIR}
        )

    # link all libraries sent through parameters
    foreach(link IN LISTS link_list)
        target_link_libraries(${test_name} ${link})
    endforeach()

    # add dependency to all the dep_list parameter
    foreach(dependency IN LISTS dep_list)
        add_dependencies(${test_name} ${dependency})
        target_link_libraries(${test_name} ${dependency})
    endforeach()
    target_link_libraries(${test_name} -lgcov unity)
    target_link_directories(${test_name}  PUBLIC
                            ${CMAKE_CURRENT_BINARY_DIR}/lib
            )
    add_test(NAME ${test_name}
             COMMAND ${CMAKE_BINARY_DIR}/bin/tests/${test_name}
             WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            )
endfunction()

# Run the C preprocessor on target files.
# Takes a CMAKE list of arguments to pass to the C compiler
function(preprocess_mock_list mock_name file_list compiler_args)
    set_property(GLOBAL PROPERTY ${mock_name}_processed TRUE)
    foreach (target_file IN LISTS file_list)
        # Has to be TARGET ALL so the file is pre-processed before CMOCK
        # is executed on the file.
        add_custom_command(OUTPUT ${target_file}.backup
            COMMAND scp ${target_file} ${target_file}.backup
            VERBATIM COMMAND ${CMAKE_C_COMPILER} -E ${compiler_args} ${target_file} > ${target_file}.out
        )
        add_custom_target(pre_${mock_name}
            COMMAND mv ${target_file}.out ${target_file}
            DEPENDS ${target_file}.backup
        )
    endforeach()

    # Clean up temporary files that were created.
    # First we test to see if the backup file still exists. If it does we revert
    # the change made to the original file.
    foreach (target_file IN LISTS file_list)
        add_custom_command(TARGET ${mock_name}
            POST_BUILD
            COMMAND test ! -e ${target_file}.backup || mv ${target_file}.backup ${target_file}
        )
    endforeach()
endfunction()

# Generates a mock library based on a module's header file
# places the generated source file in the build directory
# @param mock_name: name of the target name
# @param mock_list list of header files to mock
# @param cmock_config configuration file of the cmock framework
# @param mock_include_list include list for the target
# @param mock_define_list special definitions to control compilation
function(create_mock_list mock_name
                          mock_list
                          cmock_config
                          mock_include_list
                          mock_define_list
                          mock_dir)
    set(mocks_dir "${CMAKE_CURRENT_BINARY_DIR}/${mock_dir}")
    add_library(${mock_name} SHARED)
    foreach (mock_file IN LISTS mock_list)
        get_filename_component(mock_file_abs
                               ${mock_file}
                               ABSOLUTE
                )
        get_filename_component(mock_file_name
                               ${mock_file}
                               NAME_WLE
                )
        get_filename_component(mock_file_dir
                               ${mock_file}
                               DIRECTORY
                )
        add_custom_command (
                  OUTPUT ${mocks_dir}/mock_${mock_file_name}.c
                  COMMAND ruby
                  ${CMOCK_DIR}/lib/cmock.rb
                  -o${cmock_config} ${mock_file_abs}
                  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
                )
        target_sources(${mock_name} PUBLIC
                       ${mocks_dir}/mock_${mock_file_name}.c
        )

        target_include_directories(${mock_name} PUBLIC
                                   ${mock_file_dir}
        )
    endforeach()
    target_include_directories(${mock_name} PUBLIC
                               ${mocks_dir}
                               ${mock_include_list}
           )
    set_target_properties(${mock_name} PROPERTIES
                        LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib
                        POSITION_INDEPENDENT_CODE ON
            )
    target_compile_definitions(${mock_name} PUBLIC
            ${mock_define_list}
        )
    target_link_libraries(${mock_name} cmock unity)
endfunction()


function(create_real_library target
                             src_file
                             real_include_list
                             mock_name)
    add_library(${target} STATIC
            ${src_file}
        )
    target_include_directories(${target} PUBLIC
            ${real_include_list}
        )
    set_target_properties(${target} PROPERTIES
                COMPILE_FLAGS "-Wextra -Wpedantic \
                    -fprofile-arcs -ftest-coverage -fprofile-generate \
                    -Wno-unused-but-set-variable"
                LINK_FLAGS "-fprofile-arcs -ftest-coverage \
                    -fprofile-generate "
                ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib
            )
    if(NOT(mock_name STREQUAL ""))
        add_dependencies(${target} ${mock_name})
        target_link_libraries(${target}
                        -l${mock_name}
                        -lgcov
                )
    endif()
endfunction()
