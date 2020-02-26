set(cbmc_proof_name IotHttpsClient_Disconnect)

################################################################

set(cbmc_project_source
    ${CMAKE_SOURCE_DIR}/libraries/c_sdk/standard/https/src/iot_https_client.c
)

set(cbmc_project_remove
  IotNetworkInterfaceDestroy
  _httpParserOnHeadersCompleteCallback
  _httpParserOnMessageBeginCallback
  _httpParserOnMessageCompleteCallback
)

################################################################

set(cbmc_harness_source
    ${CMAKE_CURRENT_SOURCE_DIR}/${cbmc_proof_name}_harness.c
)

set(cbmc_harness_remove
)

################################################################

set(cbmc_unwindset
    IotListDouble_RemoveAll.0:2
    strlen.0:5
)

include(${CMAKE_SOURCE_DIR}/tools/cmake/cbmc_recipes.cmake)
