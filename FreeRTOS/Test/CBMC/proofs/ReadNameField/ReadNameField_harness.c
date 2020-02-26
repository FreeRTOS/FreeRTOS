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

uint8_t *prvReadNameField( uint8_t *pucByte, size_t xSourceLen, char *pcName, size_t xDestLen );

void harness() {

  // Choose arbitrary buffer of size at most NETWORK_BUFFER_SIZE
  uint8_t my_buffer[NETWORK_BUFFER_SIZE];
  size_t my_buffer_offset;
  uint8_t *buffer = my_buffer + my_buffer_offset;
  size_t buffer_size = NETWORK_BUFFER_SIZE - my_buffer_offset;
  __CPROVER_assume(my_buffer_offset <= NETWORK_BUFFER_SIZE);

  // Choose arbitrary name of size at most NAME_SIZE
  char my_name[NAME_SIZE];
  size_t my_name_offset;
  char *name = my_name + my_name_offset;
  size_t name_size = NAME_SIZE - my_name_offset;
  __CPROVER_assume(my_name_offset <= NAME_SIZE);

  // Choose arbitrary pointers into buffer and name
  size_t buffer_offset;
  size_t name_offset;
  uint8_t *pucByte = buffer + buffer_offset;
  char *pcName = name + name_offset;
  __CPROVER_assume(buffer_offset <= NETWORK_BUFFER_SIZE);
  __CPROVER_assume(name_offset <= NAME_SIZE);

  // Choose arbitrary values for space remaining in the buffers
  size_t xSourceLen;
  size_t xDestLen;

  ////////////////////////////////////////////////////////////////
  // Specification and proof of prvReadNameField

  // CBMC pointer model (this is obviously true)
  __CPROVER_assume(NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE);
  __CPROVER_assume(NAME_SIZE < CBMC_MAX_OBJECT_SIZE);

  // Preconditions

  // pointers are valid pointers into buffers
  __CPROVER_assume(xSourceLen == 0 ||
		   (buffer <= pucByte && pucByte < buffer + buffer_size));
  __CPROVER_assume(name <= pcName && pcName < name + name_size);

  // lengths are valid values for space remaining in the buffers
  __CPROVER_assume(pucByte + xSourceLen <= buffer + buffer_size);
  __CPROVER_assume(pcName + xDestLen <= name + name_size);

  // CBMC loop unwinding: bounds depend on xSourceLen and xDestLen
  __CPROVER_assume(xSourceLen <= NETWORK_BUFFER_SIZE);
  __CPROVER_assume(xDestLen <= NAME_SIZE);

  // Buffer overflow via integer overflow in comparison xNameLen < xDestLen - 1
  // In actual code, xDestLen == 254
  __CPROVER_assume(xDestLen > 0);

  // Save values before function call
  SAVE_OLDVAL(pucByte, uint8_t *);
  SAVE_OLDVAL(pcName, char *);
  SAVE_OLDVAL(xSourceLen, size_t);
  SAVE_OLDVAL(xDestLen, size_t);

  // function return value is either NULL or the updated value of pucByte
  uint8_t *rc = prvReadNameField(pucByte, xSourceLen, pcName, xDestLen);

  // Postconditions

  // pucByte can be advanced one position past the end of the buffer
  __CPROVER_assert((rc == 0) ||
		   (rc - OLDVAL(pucByte) >= 1 &&
		    rc - OLDVAL(pucByte) <= OLDVAL(xSourceLen) &&
		    rc - OLDVAL(pucByte) <= OLDVAL(xDestLen)+2 &&
		    pucByte == OLDVAL(pucByte) &&
		    pcName == OLDVAL(pcName) &&
		    buffer <= rc && rc <= buffer + buffer_size),
		   "updated pucByte");
}
