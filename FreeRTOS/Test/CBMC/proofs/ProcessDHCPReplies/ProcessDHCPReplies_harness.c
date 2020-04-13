/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_TCP_WIN.h"

// Used to model FreeRTOS_recvfrom returning an arbitrary buffer
char read_buffer[BUFFER_SIZE];

BaseType_t prvProcessDHCPReplies( BaseType_t xExpectedMessageType );

// Stub
int32_t FreeRTOS_recvfrom(
  Socket_t xSocket, void *pvBuffer, size_t xBufferLength,
  BaseType_t xFlags, struct freertos_sockaddr *pxSourceAddress,
  socklen_t *pxSourceAddressLength )
{
  __CPROVER_assert(xFlags & FREERTOS_ZERO_COPY, "I can only do ZERO_COPY");

  // Choose buffer size
  size_t offset;
  size_t buffer_size = BUFFER_SIZE - offset;
  char *buffer = read_buffer + offset;
  __CPROVER_assume(offset <= BUFFER_SIZE);

  // Choose buffer contents
  // __CPROVER_havoc_object may not interact well with simplifier
  char temporary[BUFFER_SIZE];
  memcpy(read_buffer, temporary, BUFFER_SIZE);

  *((char **)pvBuffer) = buffer;
  return buffer_size;
}

// Stub
void FreeRTOS_ReleaseUDPPayloadBuffer( void *pvBuffer )
{
  // no-op
}

void harness() {
  // Omitting model of an unconstrained xDHCPData because xDHCPData is
  // the source of uninitialized data only on line 647 to set a
  // transaction id is an outgoing message

  BaseType_t xExpectedMessageType;
  prvProcessDHCPReplies(xExpectedMessageType);
}
