# =============================  Queue unit tests  ===========================
project( "queue" )
set(project_name "queue")
set(utest_name "${project_name}_utest")
set(utest_source "${project_name}_utest.c")
set(utest_yml "${project_name}.yml")
# =====================  Create your mock here  (edit)  ========================

# clear the original variables
set( mock_list "" )
set( mock_include_list "" )
set( mock_define_list "" )
set( real_source_files "" )
set( real_include_directories "" )
set( test_include_directories "" )
set( utest_link_list "" )
set( utest_dep_list "" )
set(mock_dir "wrapper_mocks")


# list of files to preprocess
list(APPEND preprocessed_mock_list
    "${MODULE_ROOT_DIR}/FreeRTOS/Source/include/task.h"
    #"${MODULE_ROOT_DIR}/FreeRTOS/Source/include/portable.h"
    )

set(preprocess_commands "-I ${MODULE_ROOT_DIR}/FreeRTOS/Source/Include -I ${MODULE_ROOT_DIR}/FreeRTOS/Test/CMock/config" )


# list the files to mock here
list(APPEND mock_list
    "${MODULE_ROOT_DIR}/FreeRTOS/Source/include/task.h"
    "${MODULE_ROOT_DIR}/FreeRTOS/Source/include/list.h"
    #"${MODULE_ROOT_DIR}/FreeRTOS/Source/include/portable.h"
)

# list the directories your mocks need
list(APPEND mock_include_list
         "config"
         "${MODULE_ROOT_DIR}/FreeRTOS/Source/include"
         #"${CMAKE_CURRENT_LIST_DIR}/${mock_dir}"
    )

#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
    portUSING_MPU_WRAPPERS=0
    )

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            "${MODULE_ROOT_DIR}/FreeRTOS/Source/queue.c"
    )

# list the directories the module under test includes
list(APPEND real_include_directories
            "config"
            "${MODULE_ROOT_DIR}/FreeRTOS/Source/include"
            #"${CMAKE_CURRENT_BINARY_DIR}/${mock_dir}"
    )
# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            "config"
            "${MODULE_ROOT_DIR}/FreeRTOS/Source/include"
            "${CMAKE_CURRENT_BINARY_DIR}/${mock_dir}"
    )
# =============================  (end edit)  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")
set(pre_mock_name "pre_${mock_name}")

create_mock_list("${mock_name}"
            "${mock_list}"
            "${CMAKE_CURRENT_LIST_DIR}/${utest_yml}"
            "${mock_include_list}"
            "${mock_define_list}"
            "${mock_dir}"
    )

separate_arguments(unix_flags UNIX_COMMAND "${preprocess_commands}")

message(STATUS "Unix Flags: ${unix_flags}")

#preprocess_mock_list(${mock_name}
#            ${preprocessed_mock_list}
#            "${unix_flags}"
#        )

#add_dependencies(${mock_name} ${pre_mock_name} )


create_real_library(${real_name}
            "${real_source_files}"
            "${real_include_directories}"
            "${mock_name}"
    )

list(APPEND utest_link_list
            -l${mock_name}
            lib${real_name}.a
    )

list(APPEND utest_dep_list
            ${real_name}
    )

create_test(${utest_name}
            "${CMAKE_CURRENT_LIST_DIR}/${utest_source}"
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
            "${CMAKE_CURRENT_LIST_DIR}/${utest_yml}"
            "${mock_dir}"
    )
