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
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"

#include "cbmc.h"

/****************************************************************
 * Signature of the function under test
 ****************************************************************/

size_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                      size_t uxTotalLength,
                                      FreeRTOS_Socket_t * const pxSocket,
                                      BaseType_t xHasSYNFlag );

/****************************************************************
 * Declare the buffer size external to the harness so it can be
 * accessed by the preconditions of prvReadSackOption, and give the
 * buffer size an unconstrained value in the harness itself.
 ****************************************************************/

size_t buffer_size;

/****************************************************************
 * Function contract proved correct by CheckOptionsInner
 ****************************************************************/

void prvReadSackOption( const uint8_t * const pucPtr,
                        size_t uxIndex,
                        FreeRTOS_Socket_t * const pxSocket )
{
    /* Preconditions */
    __CPROVER_assert( buffer_size < CBMC_MAX_OBJECT_SIZE,
                      "prvReadSackOption: buffer_size < CBMC_MAX_OBJECT_SIZE" );
    __CPROVER_assert( uxIndex <= buffer_size,
                      "prvReadSackOption: uxIndex <= buffer_size" );
    __CPROVER_assert( uxIndex + 8 <= buffer_size,
                      "prvReadSackOption: uxIndex + 8 <= buffer_size" );
    __CPROVER_assert( pucPtr != NULL,
                      "prvReadSackOption: pucPtr != NULL" );
    __CPROVER_assert( pxSocket != NULL,
                      "prvReadSackOption: pxSocket != NULL" );

    /* No postconditions required */
}

/****************************************************************
 * Proof of prvSingleStepTCPHeaderOptions function contract
 ****************************************************************/

void harness()
{
    /* Give buffer_size an unconstrained value */
    size_t buf_size;

    buffer_size = buf_size;

    uint8_t * pucPtr = malloc( buffer_size );
    size_t uxTotalLength;
    FreeRTOS_Socket_t * pxSocket = malloc( sizeof( FreeRTOS_Socket_t ) );
    BaseType_t xHasSYNFlag;

    /****************************************************************
     * Specification and proof of CheckOptions outer loop
     ****************************************************************/

    /* CBMC model of pointers limits the size of the buffer */
    __CPROVER_assume( buffer_size < CBMC_MAX_OBJECT_SIZE );

    /* Preconditions */
    __CPROVER_assume( 8 <= buffer_size ); /* ulFirst and ulLast */
    __CPROVER_assume( pucPtr != NULL );
    __CPROVER_assume( uxTotalLength <= buffer_size );
    __CPROVER_assume( pxSocket != NULL );

    size_t index = prvSingleStepTCPHeaderOptions( pucPtr,
                                                  uxTotalLength,
                                                  pxSocket,
                                                  xHasSYNFlag );

    /* Postconditions */
    __CPROVER_assert( index == 1 || index <= uxTotalLength,
                      "prvSingleStepTCPHeaderOptions: index <= uxTotalLength" );
}
