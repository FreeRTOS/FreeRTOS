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

BaseType_t prvSingleStepTCPHeaderOptions( const unsigned char ** const ppucPtr,
					  const unsigned char ** const ppucLast,
					  FreeRTOS_Socket_t ** const ppxSocket,
					  TCPWindow_t ** const ppxTCPWindow);

// Given unconstrained values in harness
size_t buffer_size;
uint8_t *EthernetBuffer;

void prvSkipPastRemainingOptions( const unsigned char ** const ppucPtr,
				  FreeRTOS_Socket_t ** const ppxSocket,
				  unsigned char * const pucLen )
{
  // Preconditions

  // pucPtr is a valid pointer
  __CPROVER_assert(EthernetBuffer <= OBJ(ppucPtr) &&
		   OBJ(ppucPtr) < EthernetBuffer + buffer_size,
		   "pucPtr is a valid pointer");
  // pucPtr + 8 is a valid pointer
  __CPROVER_assert(EthernetBuffer <= OBJ(ppucPtr) + 8 &&
		   OBJ(ppucPtr) + 8 <= EthernetBuffer + buffer_size,
		   "pucPtr+8 is a valid pointer");
  // len >= 8
  __CPROVER_assert(OBJ(pucLen) >= 8, "len >= 8");

  // Record initial values
  SAVE_OLDOBJ(ppucPtr, unsigned char *);
  SAVE_OLDOBJ(pucLen, unsigned char);

  // Model loop body
  OBJ(ppucPtr) += 8;
  OBJ(pucLen) -= 8;

  // Postconditions

  __CPROVER_assume(OBJ(ppucPtr) == OLDOBJ(ppucPtr) + 8);
  __CPROVER_assume(OBJ(pucLen) == OLDOBJ(pucLen) - 8);
  __CPROVER_assume(EthernetBuffer <= OBJ(ppucPtr) &&
		   OBJ(ppucPtr) <= EthernetBuffer + buffer_size);
}

// Proof of CheckOptions outer loop
void harness()
{
  // Buffer can be any buffer of size at most BUFFER_SIZE
  size_t offset;
  uint8_t buffer[BUFFER_SIZE];
  buffer_size = BUFFER_SIZE - offset;
  EthernetBuffer = buffer + offset;

  // pucPtr and pucLast can be any pointers into buffer
  size_t pucPtr_offset;
  size_t pucLast_offset;
  unsigned char *pucPtr = EthernetBuffer + pucPtr_offset;
  unsigned char *pucLast = EthernetBuffer + pucLast_offset;

  // uxNewMSS can by any byte
  UBaseType_t uxNewMSS;

  // pxSocket can be any socket
  FreeRTOS_Socket_t xSocket;
  FreeRTOS_Socket_t *pxSocket = &xSocket;

  // pxTCPWindow can be any window (points into socket)
  TCPWindow_t *pxTCPWindow = &xSocket.u.xTCP.xTCPWindow;

  ////////////////////////////////////////////////////////////////
  // Specification and proof of CheckOptions outer loop

  // CBMC pointer model (obviously true)
  __CPROVER_assume(buffer_size < CBMC_MAX_OBJECT_SIZE);

  // Preconditions

  // pucPtr is a valid pointer
  __CPROVER_assume(EthernetBuffer <= pucPtr &&
		   pucPtr < EthernetBuffer + buffer_size);
  // pucLast is a valid pointer (or one past)
  __CPROVER_assume(EthernetBuffer <= pucLast &&
		   pucLast <= EthernetBuffer + buffer_size);
  // pucPtr is before pucLast
  __CPROVER_assume(pucPtr < pucLast);

  // Record initial values
  SAVE_OLDVAL(pucPtr, uint8_t *);
  SAVE_OLDVAL(pucLast, uint8_t *);

  // Loop variables passed by reference
  // Return value describes loop exit: break or continue
  BaseType_t rc =
    prvSingleStepTCPHeaderOptions(&pucPtr, &pucLast, &pxSocket, &pxTCPWindow);

  // Postconditions
  __CPROVER_assert(rc == pdFALSE || OLDVAL(pucPtr) < pucPtr, "pucPtr advanced");
  __CPROVER_assert(pucLast == OLDVAL(pucLast), "pucLast unchanged");
  __CPROVER_assert(pucPtr <= pucLast, "pucPtr <= pucLast");

}
