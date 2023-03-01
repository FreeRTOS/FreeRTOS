/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* TCP/IP stack includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/*-----------------------------------------------------------*/

#if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )

    /* In case multiple interfaces are used, define them statically. */

    /* there is only 1 physical interface. */
    static NetworkInterface_t xInterfaces[ 1 ];

    /* It will have several end-points. */
    static NetworkEndPoint_t xEndPoints[ 4 ];

#endif /* if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 ) */

/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) || ( ipconfigDHCP_REGISTER_HOSTNAME == 1 )

    const char * pcApplicationHostnameHook( void )
    {
        /* Assign the name "FreeRTOS" to this network node.  This function will
         * be called during the DHCP: the machine will be registered with an IP
         * address plus this name. */
        return "FreeRTOSWinSim";
    }

#endif

/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 )

    BaseType_t xApplicationDNSQueryHook( const char * pcName )
    {
        BaseType_t xReturn;

        /* Determine if a name lookup is for this node.  Two names are given
         * to this node: that returned by pcApplicationHostnameHook() and that set
         * by mainDEVICE_NICK_NAME. */
        if( _stricmp( pcName, pcApplicationHostnameHook() ) == 0 )
        {
            xReturn = pdPASS;
        }
        else if( _stricmp( pcName, mainDEVICE_NICK_NAME ) == 0 )
        {
            xReturn = pdPASS;
        }
        else
        {
            xReturn = pdFAIL;
        }

        return xReturn;
    }

#endif /* if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) */

/*
 * Set *pulNumber to a random number, and return pdTRUE. When the random number
 * generator is broken, it shall return pdFALSE.
 */
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *pulNumber = ( uint32_t ) uxRand();
    return pdTRUE;
}

/*-----------------------------------------------------------*/

/*
 * Callback that provides the inputs necessary to generate a randomized TCP
 * Initial Sequence Number per RFC 6528.  THIS IS ONLY A DUMMY IMPLEMENTATION
 * THAT RETURNS A PSEUDO RANDOM NUMBER SO IS NOT INTENDED FOR USE IN PRODUCTION
 * SYSTEMS.
 */
uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                             uint16_t usSourcePort,
                                             uint32_t ulDestinationAddress,
                                             uint16_t usDestinationPort )
{
    ( void ) ulSourceAddress;
    ( void ) usSourcePort;
    ( void ) ulDestinationAddress;
    ( void ) usDestinationPort;

    return ( uint32_t ) uxRand();
}

/* Called by FreeRTOS+TCP when the network connects or disconnects.  Disconnect
 * events are only received if implemented in the MAC driver. */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
    uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
    char cBuffer[ 16 ];
    static BaseType_t xTasksAlreadyCreated = pdFALSE;

    /* If the network has just come up...*/
    if( eNetworkEvent == eNetworkUp )
    {
        /* Print out the network configuration, which may have come from a DHCP
         * server. */
    #if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )
        FreeRTOS_GetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, pxNetworkEndPoints );
    #else
        FreeRTOS_GetAddressConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress );
    #endif /* if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 ) */

        FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
        FreeRTOS_printf( ( "\r\n\r\nIP Address: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulNetMask, cBuffer );
        FreeRTOS_printf( ( "Subnet Mask: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulGatewayAddress, cBuffer );
        FreeRTOS_printf( ( "Gateway Address: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulDNSServerAddress, cBuffer );
        FreeRTOS_printf( ( "DNS Server Address: %s\r\n\r\n\r\n", cBuffer ) );
    }
}

/*-----------------------------------------------------------*/

void vPlatformInitIpStack( void )
{
    UBaseType_t uxRandomNumber;
    BaseType_t xResult;
    uint8_t ucIPAddress[ 4 ];
    uint8_t ucNetMask[ 4 ] = { 255, 255, 0, 0 };
    uint8_t ucNullAddress[ 4 ] = { 0, 0, 0, 0 };
    uint8_t ucMACAddress[ 6 ];

    /* Generate a random number */
    uxRandomNumber = uxRand();

    /* Generate a random MAC address in the reserved range */
    ucMACAddress[ 0 ] = 0x00;
    ucMACAddress[ 1 ] = 0x11;
    ucMACAddress[ 2 ] = ( uxRandomNumber & 0xFF );
    ucMACAddress[ 3 ] = ( ( uxRandomNumber >> 8 ) & 0xFF );
    ucMACAddress[ 4 ] = ( ( uxRandomNumber >> 16 ) & 0xFF );
    ucMACAddress[ 5 ] = ( ( uxRandomNumber >> 24 ) & 0xFF );

    /* Assign a link-local address in the 169.254.0.0/16 range */
    ucIPAddress[ 0 ] = 169U;
    ucIPAddress[ 1 ] = 254U;
    ucIPAddress[ 2 ] = ( ( uxRandomNumber >> 16 ) & 0xFF );
    ucIPAddress[ 3 ] = ( ( uxRandomNumber >> 24 ) & 0xFF );

    /* Initialise the network interface.*/
    FreeRTOS_debug_printf( ( "FreeRTOS_IPInit\r\n" ) );

#if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )
    /* Initialise the interface descriptor for WinPCap. */
    pxWinPcap_FillInterfaceDescriptor( 0, &( xInterfaces[ 0 ] ) );

    /* === End-point 0 === */
    FreeRTOS_FillEndPoint( &( xInterfaces[ 0 ] ), &( xEndPoints[ 0 ] ), ucIPAddress, ucNetMask, ucNullAddress, ucNullAddress, ucMACAddress );
    #if ( ipconfigUSE_DHCP != 0 )
    {
        /* End-point 0 wants to use DHCPv4. */
        xEndPoints[ 0 ].bits.bWantDHCP = pdTRUE;
    }
    #endif /* ( ipconfigUSE_DHCP != 0 ) */
    memcpy( ipLOCAL_MAC_ADDRESS, ucMACAddress, sizeof( ucMACAddress ) );
    xResult = FreeRTOS_IPStart();
#else
    /* Using the old /single /IPv4 library, or using backward compatible mode of the new /multi library. */
    xResult = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucNullAddress, ucNullAddress, ucMACAddress );
#endif /* if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 ) */

    configASSERT( xResult == pdTRUE );
}

/*-----------------------------------------------------------*/

BaseType_t xPlatformIsNetworkUp( void )
{
    return FreeRTOS_IsNetworkUp();
}

/*-----------------------------------------------------------*/

#if ( ( ipconfigUSE_TCP == 1 ) && ( ipconfigUSE_DHCP_HOOK != 0 ) )

eDHCPCallbackAnswer_t xApplicationDHCPHook( eDHCPCallbackPhase_t eDHCPPhase,
                                            uint32_t ulIPAddress )
{
    /* Provide a stub for this function. */
    return eDHCPContinue;
}

#endif
/*-----------------------------------------------------------*/