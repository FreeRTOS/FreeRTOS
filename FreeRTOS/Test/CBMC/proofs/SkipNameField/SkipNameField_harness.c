/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "IPTraceMacroDefaults.h"

#include "cbmc.h"

uint8_t *prvSkipNameField( uint8_t *pucByte, size_t xSourceLen );

void harness() {

  // Choose arbitrary buffer of size at most NETWORK_BUFFER_SIZE
  uint8_t my_buffer[NETWORK_BUFFER_SIZE];
  size_t my_buffer_offset;
  uint8_t *buffer = my_buffer + my_buffer_offset;
  size_t buffer_size = NETWORK_BUFFER_SIZE - my_buffer_offset;
  __CPROVER_assume(my_buffer_offset <= NETWORK_BUFFER_SIZE);

  // Choose arbitrary pointer into buffer
  size_t buffer_offset;
  uint8_t *pucByte = buffer + buffer_offset;
  __CPROVER_assume(buffer_offset <= NETWORK_BUFFER_SIZE);

  // Choose arbitrary value for space remaining in the buffer
  size_t xSourceLen;

  ////////////////////////////////////////////////////////////////
  // Specification and proof of prvSkipNameField

  // CBMC pointer model (this is obviously true)
  __CPROVER_assume(NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE);

  // Preconditions

  // pointer is valid pointer into buffer
  __CPROVER_assume(xSourceLen == 0 ||
		   (buffer <= pucByte && pucByte < buffer + buffer_size));

  // length is valid value for space remaining in the buffer
  __CPROVER_assume(pucByte + xSourceLen <= buffer + buffer_size);

  // CBMC loop unwinding: bound depend on xSourceLen
  __CPROVER_assume(xSourceLen <= NETWORK_BUFFER_SIZE);

  SAVE_OLDVAL(pucByte, uint8_t *);
  SAVE_OLDVAL(xSourceLen, size_t);

  // function return value is either NULL or the updated value of pucByte
  uint8_t *rc = prvSkipNameField(pucByte, xSourceLen);

  // Postconditions

  // pucByte can be advanced one position past the end of the buffer
  __CPROVER_assert((rc == 0) ||
		   (rc - OLDVAL(pucByte) >= 1 &&
		    rc - OLDVAL(pucByte) <= OLDVAL(xSourceLen) &&
		    pucByte == OLDVAL(pucByte) &&
		    buffer <= rc && rc <= buffer + buffer_size),
		   "updated pucByte");
}
