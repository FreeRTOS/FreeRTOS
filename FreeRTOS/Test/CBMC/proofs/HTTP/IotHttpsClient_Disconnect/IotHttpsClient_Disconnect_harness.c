/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS+TCP includes. */
#include "iot_https_client.h"
#include "iot_https_internal.h"

#include "../global_state_HTTP.c"

void harness() {
  IotHttpsConnectionHandle_t connHandle = allocate_IotConnectionHandle();
  initialize_IotConnectionHandle(connHandle);
  if(connHandle) {
    __CPROVER_assume(is_valid_IotConnectionHandle(connHandle));
    __CPROVER_assume(is_stubbed_NetworkInterface(connHandle->pNetworkInterface));
  }
  IotHttpsClient_Disconnect(connHandle);
}
