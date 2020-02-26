/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS+TCP includes. */
#include "iot_https_client.h"
#include "iot_https_internal.h"

#include "../global_state_HTTP.c"

/* We prove memory safety of IotHttpsClient_Disconnect separately. */
IotHttpsReturnCode_t IotHttpsClient_Disconnect(IotHttpsConnectionHandle_t connHandle) {}


void harness() {
  IotHttpsConnectionHandle_t pConnHandle = allocate_IotConnectionHandle();
  IotHttpsConnectionInfo_t *pConnConfig = allocate_IotConnectionInfo();
  initialize_IotConnectionHandle(pConnHandle);
  if(pConnHandle) {
    __CPROVER_assume(is_valid_IotConnectionHandle(pConnHandle));
    __CPROVER_assume(is_stubbed_NetworkInterface(pConnHandle->pNetworkInterface));
  }
  if (pConnConfig) {
    __CPROVER_assume(is_valid_IotConnectionInfo(pConnConfig));
    __CPROVER_assume(is_stubbed_NetworkInterface(pConnConfig->pNetworkInterface));
  }
  IotHttpsClient_Connect(&pConnHandle, pConnConfig);
}
