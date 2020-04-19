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

uint32_t prvParseDNSReply(uint8_t *pucUDPPayloadBuffer,
			  size_t xBufferLength,
			  TickType_t xIdentifier);

// Used in specification and abstraction of prvReadNameField, prvSkipNameField
// Given unconstrained values in harness
uint8_t *buffer;
size_t buffer_size;

// Abstraction of prvReadNameField
uint8_t *prvReadNameField(uint8_t *pucByte,
			  size_t xSourceLen,
			  char *pcName,
			  size_t xDestLen){

  // Preconditions

  // pointers are valid pointers into buffers
  __CPROVER_assert(xSourceLen == 0 ||
		   (buffer <= pucByte && pucByte < buffer + buffer_size),
		   "pucByte valid pointer");
  //  __CPROVER_assume(name <= pcName && pcName < name + name_size);
  (void) *(pcName); // can only test for valid pointer

  // lengths are valid values for space remaining in the buffers
  __CPROVER_assert(pucByte + xSourceLen <= buffer + buffer_size,
		   "xSourceLen valid length");
  //  __CPROVER_assume(pcName + xDestLen <= name + name_size);
  (void) *(pcName + (xDestLen-1)); // can only test for valid pointer

  // CBMC loop unwinding: bounds depend on xSourceLen and xDestLen
  __CPROVER_assert(xSourceLen <= NETWORK_BUFFER_SIZE,
		   "xSourceLen loop unwinding");
  //  __CPROVER_assume(xDestLen <= NAME_SIZE);

  // Buffer overflow from integer overflow in expression len < xDestLen-1
  // xDestLen == 254 in code
  __CPROVER_assert(xDestLen > 0, "xDestLen nonzero");

  SAVE_OLDVAL(pucByte, uint8_t *);
  SAVE_OLDVAL(pcName, char *);
  SAVE_OLDVAL(xSourceLen, size_t);
  SAVE_OLDVAL(xDestLen, size_t);

  // Function body
  char bit;
  size_t offset;
  uint8_t *rc = bit ? pucByte + offset : 0;
  __CPROVER_assume(offset <= NETWORK_BUFFER_SIZE);

  // Postconditions
  __CPROVER_assume((rc == 0) ||
		   (rc - OLDVAL(pucByte) >= 1 &&
		    rc - OLDVAL(pucByte) <= OLDVAL(xSourceLen) &&
		    rc - OLDVAL(pucByte) <= OLDVAL(xDestLen)+2 &&
		    pucByte == OLDVAL(pucByte) &&
		    pcName == OLDVAL(pcName) &&
		    buffer <= rc && rc <= buffer + buffer_size));

  return rc;
}

// Abstraction of prvSkipNameField
uint8_t *prvSkipNameField( uint8_t *pucByte, size_t xSourceLen ){

  // Preconditions

  // pointer is valid pointer into buffer
  __CPROVER_assert(xSourceLen == 0 ||
		   (buffer <= pucByte && pucByte < buffer + buffer_size),
		   "pucByte valid pointer");

  // length is valid value for space remaining in the buffer
  __CPROVER_assert(pucByte + xSourceLen <= buffer + buffer_size,
		   "xSourceLen valid length");

  // CBMC loop unwinding: bound depend on xSourceLen
  __CPROVER_assert(xSourceLen <= NETWORK_BUFFER_SIZE,
		   "xSourceLen loop unwinding");

  SAVE_OLDVAL(pucByte, uint8_t *);
  SAVE_OLDVAL(xSourceLen, size_t);

  // Function body
  char bit;
  size_t offset;
  uint8_t *rc = bit ? pucByte + offset : 0;
  __CPROVER_assume(offset <= NETWORK_BUFFER_SIZE);

  // Postconditions
  __CPROVER_assume((rc == 0) ||
		   (rc - OLDVAL(pucByte) >= 1 &&
		    rc - OLDVAL(pucByte) <= OLDVAL(xSourceLen) &&
		    pucByte == OLDVAL(pucByte) &&
		    buffer <= rc && rc <= buffer + buffer_size));

  return rc;

}

void harness() {

  // Choose arbitrary buffer of size at most NETWORK_BUFFER_SIZE
  uint8_t my_buffer[NETWORK_BUFFER_SIZE];
  size_t my_buffer_offset;
  buffer = my_buffer + my_buffer_offset;
  buffer_size = NETWORK_BUFFER_SIZE - my_buffer_offset;
  __CPROVER_assume(my_buffer_offset <= NETWORK_BUFFER_SIZE);

  __CPROVER_havoc_object(my_buffer);

  // Choose arbitrary pointer into the buffer
  size_t buffer_offset;
  uint8_t *pucUDPPayloadBuffer = buffer + buffer_offset;

  // Choose arbitrary value for space remaining in the buffer
  size_t xBufferLength;

  // Choose arbitrary identifier
  TickType_t xIdentifier;

  ////////////////////////////////////////////////////////////////
  // Specification and proof of prvReadNameField

  // CBMC pointer model (this is obviously true)
  __CPROVER_assume(NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE);

  // Preconditions

  // pointer is valid pointer into buffer
  __CPROVER_assume(buffer <= pucUDPPayloadBuffer &&
		   pucUDPPayloadBuffer < buffer + buffer_size);

  // length is valid value for space remaining in the buffer
  __CPROVER_assume(pucUDPPayloadBuffer + xBufferLength
		   <= buffer + buffer_size);

  // CBMC loop unwinding: bounds depend on xBufferLength
  __CPROVER_assume(xBufferLength <= NETWORK_BUFFER_SIZE);

  prvParseDNSReply(pucUDPPayloadBuffer, xBufferLength, xIdentifier);

}
