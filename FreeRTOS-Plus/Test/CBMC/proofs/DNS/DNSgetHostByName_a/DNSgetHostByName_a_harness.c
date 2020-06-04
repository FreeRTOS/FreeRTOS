/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "cbmc.h"

/****************************************************************
 * We abstract:
 *
 *   All kernel task scheduling functions since we are doing
 *   sequential verification and the sequential verification of these
 *   sequential primitives is done elsewhere.
 *
 *   Many methods in the FreeRTOS TCP API in stubs/freertos_api.c
 *
 *   prvParseDNSReply proved memory safe elsewhere
 *
 *   prvCreateDNSMessage
 *
 * This proof assumes the length of pcHostName is bounded by
 * MAX_HOSTNAME_LEN.  We have to bound this length because we have to
 * bound the iterations of strcmp.
 ****************************************************************/

/****************************************************************
 * Abstract prvParseDNSReply proved memory safe in ParseDNSReply.
 *
 * We stub out his function to fill the payload buffer with
 * unconstrained data and return an unconstrained size.
 *
 * The function under test uses only the return value of this
 * function.
 ****************************************************************/

uint32_t prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                           size_t xBufferLength,
                           BaseType_t xExpected )
{
    __CPROVER_assert(pucUDPPayloadBuffer != NULL,
		     "Precondition: pucUDPPayloadBuffer != NULL");

    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    return nondet_uint32();
}

/****************************************************************
 * Abstract prvCreateDNSMessage
 *
 * This function writes a header, a hostname, and a constant amount of
 * data into the payload buffer, and returns the amount of data
 * written.  This abstraction just fills the entire buffer with
 * unconstrained data and returns and unconstrained length.
 ****************************************************************/

size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                            const char * pcHostName,
                            TickType_t uxIdentifier )
{
    __CPROVER_assert(pucUDPPayloadBuffer != NULL,
		     "Precondition: pucUDPPayloadBuffer != NULL");
    __CPROVER_assert(pcHostName != NULL,
		     "Precondition: pcHostName != NULL");

    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    return nondet_sizet();
}

/****************************************************************
 * A stub for a function callback.
 ****************************************************************/

void func(const char * pcHostName, void * pvSearchID, uint32_t ulIPAddress)
{
}

/****************************************************************
 * The proof for FreeRTOS_gethostbyname_a.
 ****************************************************************/

void harness() {
    size_t len;

    __CPROVER_assume( len <= MAX_HOSTNAME_LEN );
    char * pcHostName = safeMalloc( len );

    __CPROVER_assume( len > 0 ); /* prvProcessDNSCache strcmp */
    __CPROVER_assume( pcHostName != NULL );
    pcHostName[ len - 1 ] = NULL;

    FOnDNSEvent pCallback = func;
    TickType_t xTimeout;
    void *pvSearchID;

    FreeRTOS_gethostbyname_a(pcHostName, pCallback, pvSearchID, xTimeout);
}
