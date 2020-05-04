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

#include "cbmc.h"

void prvSkipPastRemainingOptions( const unsigned char ** const ppucPtr,
				  FreeRTOS_Socket_t ** const ppxSocket,
				  unsigned char * const pucLen );

// Given unconstrained values in harness
size_t buffer_size;
uint8_t *EthernetBuffer;

void harness()
{
  // Buffer can be any buffer of size at most BUFFER_SIZE
  size_t offset;
  uint8_t buffer[BUFFER_SIZE];
  buffer_size = BUFFER_SIZE - offset;
  EthernetBuffer = buffer + offset;

  // pucPtr can be any pointer into buffer
  size_t pucPtr_offset;
  unsigned char *pucPtr = EthernetBuffer + pucPtr_offset;

  // ucLen can be any byte
  unsigned char ucLen;

  // pxSocket can be any socket with some initialized values
  FreeRTOS_Socket_t xSocket;
  FreeRTOS_Socket_t *pxSocket = &xSocket;

  extern List_t xSegmentList;
  vListInitialise(&xSocket.u.xTCP.xTCPWindow.xWaitQueue);
  vListInitialise(&xSocket.u.xTCP.xTCPWindow.xTxSegments);
  vListInitialise(&xSocket.u.xTCP.xTCPWindow.xPriorityQueue);
  vListInitialise(&xSegmentList);
  StreamBuffer_t txStreamBuffer;
  xSocket.u.xTCP.txStream=&txStreamBuffer;

  // A singleton list
  TCPSegment_t segment_w;
  vListInitialiseItem(&segment_w.xQueueItem);
  vListInitialiseItem(&segment_w.xListItem);
  listSET_LIST_ITEM_OWNER(&segment_w.xQueueItem, (void *) &segment_w);
  vListInsertEnd(&xSocket.u.xTCP.xTCPWindow.xWaitQueue, &segment_w.xQueueItem);

  // A singleton list
  TCPSegment_t segment_t;
  vListInitialiseItem(&segment_t.xQueueItem);
  vListInitialiseItem(&segment_t.xListItem);
  listSET_LIST_ITEM_OWNER(&segment_t.xQueueItem, (void *) &segment_t);
  vListInsertEnd(&xSocket.u.xTCP.xTCPWindow.xTxSegments, &segment_t.xQueueItem);

  ////////////////////////////////////////////////////////////////
  // Specification and proof of CheckOptions inner loop

  // CBMC pointer model (obviously true)
  __CPROVER_assume(buffer_size < CBMC_MAX_OBJECT_SIZE);

  // Preconditions

  // pucPtr is a valid pointer
  __CPROVER_assume(EthernetBuffer <= pucPtr &&
  		   pucPtr < EthernetBuffer + buffer_size);
  // pucPtr + 8 is a valid pointer (xBytesRemaining > ucLen)
  __CPROVER_assume(EthernetBuffer <= pucPtr + 8 &&
  		   pucPtr + 8 <= EthernetBuffer + buffer_size);
  // ucLen >= 8 (while loop condition)
  __CPROVER_assume(ucLen >= 8);

  // Record initial values
  SAVE_OLDVAL(pucPtr, unsigned char *);
  SAVE_OLDVAL(ucLen, unsigned char);

  // Loop variables passed by reference
  prvSkipPastRemainingOptions(&pucPtr, &pxSocket, &ucLen);

  // Postconditions

  __CPROVER_assert(pucPtr == OLDVAL(pucPtr) + 8, "pucPtr advanced");
  __CPROVER_assert(ucLen == OLDVAL(ucLen) - 8, "ucLen decremented");
  __CPROVER_assert(EthernetBuffer <= pucPtr &&
		   pucPtr <= EthernetBuffer + buffer_size,
		   "pucPtr a valid pointer");
}
