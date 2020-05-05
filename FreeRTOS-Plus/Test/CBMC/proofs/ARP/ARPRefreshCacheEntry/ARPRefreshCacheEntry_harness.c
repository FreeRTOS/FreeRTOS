/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"

void harness()
{
  MACAddress_t xMACAddress;
  uint32_t ulIPAddress;
  vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );
  vARPRefreshCacheEntry( NULL, ulIPAddress );
}