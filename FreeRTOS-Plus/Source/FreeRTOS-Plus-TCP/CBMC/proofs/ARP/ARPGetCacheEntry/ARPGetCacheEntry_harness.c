/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"


void harness()
{
  uint32_t ulIPAddress;
  MACAddress_t xMACAddress;

  eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
}