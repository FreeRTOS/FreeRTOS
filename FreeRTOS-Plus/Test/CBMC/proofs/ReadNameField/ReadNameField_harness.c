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

size_t prvReadNameField( const uint8_t *pucByte,
			 size_t uxRemainingBytes,
			 char *pcName,
			 size_t uxDestLen );

/****************************************************************
 * The function under test is not defined in all configurations
 ****************************************************************/

#if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )  

/* prvReadNameField is defined in this configuration */

#else

/* prvReadNameField is not defined in this configuration, stub it. */

size_t prvReadNameField( const uint8_t *pucByte,
			 size_t uxRemainingBytes,
			 char *pcName,
			 size_t uxDestLen )
{
  return 0;
}

#endif


/****************************************************************
 * Proof of prvReadNameField function contract
 ****************************************************************/

void harness() {

  __CPROVER_assert(NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE,
		   "NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE");
  __CPROVER_assert(NAME_SIZE < CBMC_MAX_OBJECT_SIZE,
		   "NAME_SIZE < CBMC_MAX_OBJECT_SIZE");

  __CPROVER_assert(NAME_SIZE >= 4,
		   "NAME_SIZE >= 4 required for good coverage.");


  size_t uxRemainingBytes;
  size_t uxDestLen;

  uint8_t *pucByte = malloc(uxRemainingBytes);
  char *pcName = malloc(uxDestLen);

  /* Preconditions */

  __CPROVER_assume(uxRemainingBytes < CBMC_MAX_OBJECT_SIZE);
  __CPROVER_assume(uxDestLen < CBMC_MAX_OBJECT_SIZE);

  __CPROVER_assume(uxRemainingBytes <= NETWORK_BUFFER_SIZE);
  __CPROVER_assume(uxDestLen <= NAME_SIZE);

  __CPROVER_assume( pucByte != NULL );
  __CPROVER_assume( pcName != NULL );

  /* Avoid overflow on uxSourceLen - 1U with uxSourceLen == uxRemainingBytes */
  //__CPROVER_assume(uxRemainingBytes > 0);

  /* Avoid overflow on uxDestLen - 1U */
  __CPROVER_assume(uxDestLen > 0);

  size_t index = prvReadNameField( pucByte,
				   uxRemainingBytes,
				   pcName,
				   uxDestLen );

  /* Postconditions */

  __CPROVER_assert( index <= uxDestLen+1 && index <= uxRemainingBytes,
		    "prvReadNamefield: index <= uxDestLen+1");
}
