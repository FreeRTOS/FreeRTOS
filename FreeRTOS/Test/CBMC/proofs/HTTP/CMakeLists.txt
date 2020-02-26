list(PREPEND cbmc_compile_includes
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/https/include
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/https/src/private
    ${CMAKE_SOURCE_DIR}/libraries/3rdparty/http_parser
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/common/include
    ${CMAKE_SOURCE_DIR}/libraries/abstractions/platform/include
    ${CMAKE_SOURCE_DIR}/libraries/abstractions/platform/freertos/include
    ${cbmc_dir}/proofs/HTTP
)

list(APPEND cbmc_test_labels HTTP)

add_subdirectory(IotHttpsClient_AddHeader)
add_subdirectory(IotHttpsClient_Connect)
add_subdirectory(IotHttpsClient_Disconnect)
add_subdirectory(IotHttpsClient_ReadContentLength)
add_subdirectory(IotHttpsClient_ReadHeader)
add_subdirectory(IotHttpsClient_ReadResponseStatus)
add_subdirectory(IotHttpsClient_SendSync)
