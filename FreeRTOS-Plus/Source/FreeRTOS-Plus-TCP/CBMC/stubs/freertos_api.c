/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "NetworkBufferManagement.h"

#include "cbmc.h"

/****************************************************************
 * This is a collection of abstractions of methods in the FreeRTOS TCP
 * API.  The abstractions simply perform minimal validation of
 * function arguments, and return unconstrained values of the
 * appropriate type.
 ****************************************************************/

/****************************************************************
 * Abstract FreeRTOS_socket.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/socket.html
 *
 * We stub out this function to do nothing but allocate space for a
 * socket containing unconstrained data or return an error.
 ****************************************************************/

Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol )
{
    return nondet_bool() ?
           FREERTOS_INVALID_SOCKET : malloc( sizeof( Socket_t ) );
}

/****************************************************************
 * Abstract FreeRTOS_setsockopt.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/setsockopt.html
 ****************************************************************/

BaseType_t FreeRTOS_setsockopt( Socket_t xSocket,
                                int32_t lLevel,
                                int32_t lOptionName,
                                const void * pvOptionValue,
                                size_t uxOptionLength )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    __CPROVER_assert( pvOptionValue != NULL,
                      "FreeRTOS precondition: pvOptionValue != NULL" );
    return nondet_BaseType();
}

/****************************************************************
 * Abstract FreeRTOS_closesocket.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/close.html
 ****************************************************************/

BaseType_t FreeRTOS_closesocket( Socket_t xSocket )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    return nondet_BaseType();
}

/****************************************************************
 * Abstract FreeRTOS_bind.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/bind.html
 ****************************************************************/

BaseType_t FreeRTOS_bind( Socket_t xSocket,
                          struct freertos_sockaddr * pxAddress,
                          socklen_t xAddressLength )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    __CPROVER_assert( pxAddress != NULL,
                      "FreeRTOS precondition: pxAddress != NULL" );
    return nondet_BaseType();
}

/****************************************************************
 * Abstract FreeRTOS_inet_addr.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/inet_addr.html
 ****************************************************************/

uint32_t FreeRTOS_inet_addr( const char * pcIPAddress )
{
    __CPROVER_assert( pcIPAddress != NULL,
                      "FreeRTOS precondition: pcIPAddress != NULL" );
    return nondet_uint32();
}

/****************************************************************
 * Abstract FreeRTOS_recvfrom.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/recvfrom.html
 *
 * We stub out this function to do nothing but allocate a buffer of
 * unconstrained size containing unconstrained data and return the
 * size (or return the size 0 if the allocation fails).
 ****************************************************************/

int32_t FreeRTOS_recvfrom( Socket_t xSocket,
                           void * pvBuffer,
                           size_t uxBufferLength,
                           BaseType_t xFlags,
                           struct freertos_sockaddr * pxSourceAddress,
                           socklen_t * pxSourceAddressLength )

{
    /****************************************************************
     * "If the zero copy calling semantics are used (the ulFlasg
     * parameter does not have the FREERTOS_ZERO_COPY bit set) then
     * pvBuffer does not point to a buffer and xBufferLength is not
     * used."  This is from the documentation.
     ****************************************************************/
    __CPROVER_assert( xFlags & FREERTOS_ZERO_COPY, "I can only do ZERO_COPY" );

    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );

    /****************************************************************
     * TODO: We need to check this out.
     *
     * The code calls recvfrom with these parameters NULL, it is not
     * clear from the documentation that this is allowed.
     ****************************************************************/
    #if 0
        __CPROVER_assert( pxSourceAddress != NULL,
                          "FreeRTOS precondition: pxSourceAddress != NULL" );
        __CPROVER_assert( pxSourceAddressLength != NULL,
                          "FreeRTOS precondition: pxSourceAddress != NULL" );
    #endif

    size_t payload_size;
    __CPROVER_assume( payload_size + sizeof( UDPPacket_t )
		      < CBMC_MAX_OBJECT_SIZE );

    /****************************************************************
     * TODO: We need to make this lower bound explicit in the Makefile.json
     *
     * DNSMessage_t is a typedef in FreeRTOS_DNS.c
     * sizeof(DNSMessage_t) = 6 * sizeof(uint16_t)
     ****************************************************************/
    __CPROVER_assume( payload_size >= 6 * sizeof( uint16_t ) );

    #ifdef CBMC_FREERTOS_RECVFROM_BUFFER_BOUND
        __CPROVER_assume( payload_size <= CBMC_FREERTOS_RECVFROM_BUFFER_BOUND );
    #endif

    uint32_t buffer_size = payload_size + sizeof( UDPPacket_t );
    uint8_t *buffer = safeMalloc( buffer_size );
	
    if ( buffer == NULL ) {
      buffer_size = 0;
    }
    else
    {
      buffer = buffer + sizeof( UDPPacket_t );
      buffer_size = buffer_size - sizeof( UDPPacket_t );
    }
    
    *( ( uint8_t ** ) pvBuffer ) = buffer;
    return buffer_size;
}

/****************************************************************
 * Abstract FreeRTOS_recvfrom.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/sendto.html
 ****************************************************************/

int32_t FreeRTOS_sendto( Socket_t xSocket,
                         const void * pvBuffer,
                         size_t uxTotalDataLength,
                         BaseType_t xFlags,
                         const struct freertos_sockaddr * pxDestinationAddress,
                         socklen_t xDestinationAddressLength )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );
    __CPROVER_assert( pxDestinationAddress != NULL,
                      "FreeRTOS precondition: pxDestinationAddress != NULL" );
    return nondet_int32();
}

/****************************************************************
 * Abstract FreeRTOS_GetUDPPayloadBuffer
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/API/FreeRTOS_GetUDPPayloadBuffer.html
 *
 * We stub out this function to do nothing but allocate a buffer of
 * unconstrained size containing unconstrained data and return a
 * pointer to the buffer (or NULL).
 ****************************************************************/

void * FreeRTOS_GetUDPPayloadBuffer( size_t xRequestedSizeBytes,
                                     TickType_t xBlockTimeTicks )
{
    size_t size;

    __CPROVER_assume( size < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( size >= sizeof( UDPPacket_t ) );

    uint8_t *buffer = safeMalloc( size );
    return buffer == NULL ? buffer : buffer + sizeof( UDPPacket_t );
}

/****************************************************************
 * Abstract FreeRTOS_GetUDPPayloadBuffer
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/FreeRTOS_ReleaseUDPPayloadBuffer.html
 ****************************************************************/

void FreeRTOS_ReleaseUDPPayloadBuffer( void * pvBuffer )
{
    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );
    __CPROVER_assert( __CPROVER_POINTER_OFFSET( pvBuffer )
		      == sizeof( UDPPacket_t ),
                      "FreeRTOS precondition: pvBuffer offset" );

    free( pvBuffer - sizeof( UDPPacket_t ) );
}

/****************************************************************
 * Abstract pxGetNetworkBufferWithDescriptor.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/pxGetNetworkBufferWithDescriptor.html
 *
 * The real allocator take buffers off a list.
 ****************************************************************/

uint32_t GetNetworkBuffer_failure_count;

NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    __CPROVER_assert(
        xRequestedSizeBytes + ipBUFFER_PADDING < CBMC_MAX_OBJECT_SIZE,
        "pxGetNetworkBufferWithDescriptor: request too big" );

    /*
      * The semantics of this function is to wait until a buffer with
      * at least the requested number of bytes becomes available.  If a
      * timeout occurs before the buffer is available, then return a
      * NULL pointer.
      */

    NetworkBufferDescriptor_t * desc = safeMalloc( sizeof( *desc ) );

    #ifdef CBMC_GETNETWORKBUFFER_FAILURE_BOUND
        /*
          * This interprets the failure bound as being one greater than the
          * actual number of times GetNetworkBuffer should be allowed to
          * fail.
          *
          * This makes it possible to use the same bound for loop unrolling
          * which must be one greater than the actual number of times the
          * loop should be unwound.
          *
          * NOTE: Using this bound with --nondet-static requires setting
          * (or assuming) GetNetworkBuffer_failure_count to a value (like 0)
          * in the proof harness that won't induce an integer overflow.
          */
        GetNetworkBuffer_failure_count++;
        __CPROVER_assume(
	    IMPLIES(
	        GetNetworkBuffer_failure_count >= CBMC_GETNETWORKBUFFER_FAILURE_BOUND,
		desc != NULL ) );
    #endif

    if( desc != NULL )
    {
        /*
          * We may want to experiment with allocating space other than
          * (more than) the exact amount of space requested.
          */

        size_t size = xRequestedSizeBytes;
        __CPROVER_assume( size < CBMC_MAX_OBJECT_SIZE );

        desc->pucEthernetBuffer = safeMalloc( size );
        desc->xDataLength = desc->pucEthernetBuffer == NULL ? 0 : size;

        #ifdef CBMC_REQUIRE_NETWORKBUFFER_ETHERNETBUFFER_NONNULL
            /* This may be implied by the semantics of the function. */
            __CPROVER_assume( desc->pucEthernetBuffer != NULL );
        #endif

	/* Allow method to fail again next time */
	GetNetworkBuffer_failure_count = 0;
    }

    return desc;
}

/****************************************************************
 * Abstract pxGetNetworkBufferWithDescriptor.
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/vReleaseNetworkBufferAndDescriptor.html
 ****************************************************************/

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL,
                      "Precondition: pxNetworkBuffer != NULL" );

    if( pxNetworkBuffer->pucEthernetBuffer != NULL )
    {
        free( pxNetworkBuffer->pucEthernetBuffer );
    }

    free( pxNetworkBuffer );
}

/****************************************************************
 * Abstract FreeRTOS_GetAddressConfiguration
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/FreeRTOS_GetAddressConfiguration.html
 ****************************************************************/

void FreeRTOS_GetAddressConfiguration( uint32_t * pulIPAddress,
                                       uint32_t * pulNetMask,
                                       uint32_t * pulGatewayAddress,
                                       uint32_t * pulDNSServerAddress )
{
    if( pulIPAddress != NULL )
    {
        *pulIPAddress = nondet_unint32();
    }

    if( pulNetMask != NULL )
    {
        *pulNetMask = nondet_unint32();
    }

    if( pulGatewayAddress != NULL )
    {
        *pulGatewayAddress = nondet_unint32();
    }

    if( pulDNSServerAddress != NULL )
    {
        *pulDNSServerAddress = nondet_unint32();
    }
}

/****************************************************************/

/****************************************************************
 * This is a collection of methods that are defined by the user
 * application but are invoked by the FreeRTOS API.
 ****************************************************************/

/****************************************************************
 * Abstract FreeRTOS_GetAddressConfiguration
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/vApplicationIPNetworkEventHook.html
 ****************************************************************/

void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
}

/****************************************************************
 * Abstract pcApplicationHostnameHook
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html
 ****************************************************************/

const char * pcApplicationHostnameHook( void )
{
    return "hostname";
}

/****************************************************************/
