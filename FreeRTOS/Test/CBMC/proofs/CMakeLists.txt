list(APPEND cbmc_compile_options
    -m32
)

list(APPEND cbmc_compile_definitions
    CBMC
    WINVER=0x400
    _CONSOLE
    _CRT_SECURE_NO_WARNINGS
    _DEBUG
    _WIN32_WINNT=0x0500
    __PRETTY_FUNCTION__=__FUNCTION__
    __free_rtos__
)

list(APPEND cbmc_compile_includes
    ${CMAKE_SOURCE_DIR}/demos/include
    ${CMAKE_SOURCE_DIR}/freertos_kernel/include
    ${CMAKE_SOURCE_DIR}/freertos_kernel/portable/MSVC-MingW
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/http_parser
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/jsmn
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/mbedtls/include/mbedtls
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/pkcs11
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/tinycbor
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/tracealyzer_recorder/Include
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/win_pcap
    ${CMAKE_SOURCE_DIR}/libraries/abstractions/platform/freertos/include/
    ${CMAKE_SOURCE_DIR}/libraries/abstractions/platform/include/
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/aws/defender/include
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/common/include/
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/https/include
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/https/src/private
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/serializer/src/cbor
    ${CMAKE_SOURCE_DIR}/libraries/freertos_plus/aws/ota/include
    ${CMAKE_SOURCE_DIR}/libraries/freertos_plus/standard/freertos_plus_tcp/include
    ${CMAKE_SOURCE_DIR}/libraries/freertos_plus/standard/freertos_plus_tcp/source/portable/BufferManagement
    ${CMAKE_SOURCE_DIR}/libraries/freertos_plus/standard/freertos_plus_tcp/source/portable/Compiler/MSVC
    ${CMAKE_SOURCE_DIR}/vendors/pc/boards/windows/aws_demos/application_code
    ${CMAKE_SOURCE_DIR}/vendors/pc/boards/windows/aws_demos/config_files
    ${cbmc_dir}/include
    ${cbmc_dir}/windows
)

# Remove --flag for a specific proof with list(REMOVE_ITEM cbmc_flags --flag)
list(APPEND cbmc_flags
    --32
    --bounds-check
    --pointer-check
    --div-by-zero-check
    --float-overflow-check
    --nan-check
    --nondet-static
    --pointer-overflow-check
    --signed-overflow-check
    --undefined-shift-check
    --unsigned-overflow-check
)

add_subdirectory(HTTP)
