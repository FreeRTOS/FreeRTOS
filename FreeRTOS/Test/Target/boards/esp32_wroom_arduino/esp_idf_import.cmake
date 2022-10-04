# This can be dropped into an external project to help locate this SDK
# It should be include()ed prior to project()

if (DEFINED ENV{IDF_PATH})
    message("Using IDF_PATH from environment ('${IDF_PATH}')")
else ()
    message(ERROR "The IDF_PATH environment variable must be set.")
endif ()

include($ENV{IDF_PATH}/tools/cmake/project.cmake)