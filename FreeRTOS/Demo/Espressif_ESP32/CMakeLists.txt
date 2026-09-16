# Top-level CMakeLists.txt for the FreeRTOS Common/Minimal demo on
# Espressif targets. Multi-target: switch SoCs via
# `idf.py set-target <target>` and sdkconfig.defaults.<target> overrides.

cmake_minimum_required(VERSION 3.22)

include($ENV{IDF_PATH}/tools/cmake/project.cmake)

set(EXTRA_COMPONENT_DIRS "${CMAKE_CURRENT_LIST_DIR}/components")

project(freertos_common_minimal_demo)
