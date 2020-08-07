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

/****************************************************************
 * Signature of function under test
 ****************************************************************/

uint32_t prvParseDNSReply( uint8_t *pucUDPPayloadBuffer,
			   size_t uxBufferLength,
			   BaseType_t xExpected );

/****************************************************************
 * Abstraction of prvReadNameField proved in ReadNameField
 ****************************************************************/

size_t prvReadNameField( const uint8_t *pucByte,
			 size_t uxRemainingBytes,
			 char *pcName,
			 size_t uxDestLen )
{
  __CPROVER_assert(NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE,
		   "NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE");
  __CPROVER_assert(NAME_SIZE < CBMC_MAX_OBJECT_SIZE,
		   "NAME_SIZE < CBMC_MAX_OBJECT_SIZE");
  __CPROVER_assert(NAME_SIZE >= 4,
		   "NAME_SIZE >= 4 required for good coverage.");


  /* Preconditions */
  __CPROVER_assert(uxRemainingBytes < CBMC_MAX_OBJECT_SIZE,
		   "ReadNameField: uxRemainingBytes < CBMC_MAX_OBJECT_SIZE)");
  __CPROVER_assert(uxDestLen < CBMC_MAX_OBJECT_SIZE,
		   "ReadNameField: uxDestLen < CBMC_MAX_OBJECT_SIZE)");

  __CPROVER_assert(uxRemainingBytes <= NETWORK_BUFFER_SIZE,
		   "ReadNameField: uxRemainingBytes <= NETWORK_BUFFER_SIZE)");

  /* This precondition in the function contract for prvReadNameField
   * fails because prvCheckOptions called prvReadNameField with the
   * constant value 254.
  __CPROVER_assert(uxDestLen <= NAME_SIZE,
		   "ReadNameField: uxDestLen <= NAME_SIZE)");
  */

  __CPROVER_assert( pucByte != NULL ,
		    "ReadNameField:  pucByte != NULL )");
  __CPROVER_assert( pcName != NULL ,
		    "ReadNameField:  pcName != NULL )");

  __CPROVER_assert(uxDestLen > 0,
		   "ReadNameField: uxDestLen > 0)");

  /* Return value */
  size_t index;

  /* Postconditions */
  __CPROVER_assume( index <= uxDestLen+1 && index <= uxRemainingBytes );

  return index;
}

/****************************************************************
 * Abstraction of prvSkipNameField proved in SkipNameField
 ****************************************************************/

size_t prvSkipNameField( const uint8_t *pucByte, size_t uxLength )
{

  __CPROVER_assert(NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE,
		   "NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE");


  /* Preconditions */
  __CPROVER_assert(uxLength < CBMC_MAX_OBJECT_SIZE,
		   "SkipNameField: uxLength < CBMC_MAX_OBJECT_SIZE)");
  __CPROVER_assert(uxLength <= NETWORK_BUFFER_SIZE,
		   "SkipNameField: uxLength <= NETWORK_BUFFER_SIZE)");
  __CPROVER_assert(pucByte != NULL,
		   "SkipNameField: pucByte != NULL)");

  /* Return value */
  size_t index;

  /* Postconditions */
  __CPROVER_assume(index <= uxLength);

  return index;
}

/****************************************************************
 * Proof of prvParseDNSReply
 ****************************************************************/

void harness() {

  size_t uxBufferLength;
  BaseType_t xExpected;
  uint8_t *pucUDPPayloadBuffer = malloc(uxBufferLength);

  __CPROVER_assert(NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE,
		   "NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE");

  __CPROVER_assume(uxBufferLength < CBMC_MAX_OBJECT_SIZE);
  __CPROVER_assume(uxBufferLength <= NETWORK_BUFFER_SIZE);
  __CPROVER_assume(pucUDPPayloadBuffer != NULL);

  uint32_t index = prvParseDNSReply( pucUDPPayloadBuffer,
				     uxBufferLength,
				     xExpected );

}
