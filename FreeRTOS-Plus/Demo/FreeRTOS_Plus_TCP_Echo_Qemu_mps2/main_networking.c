/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/*
 * This project is a cut down version of the project described on the following
 * link.  Only the TCP echo clients is included in the build:
 * https://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdio.h>
#include <time.h>
#include <unistd.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"

/* Demo application includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "TCPEchoClient_SingleTasks.h"
#include "CMSIS/CMSDK_CM3.h"

/* Echo client task parameters  */
#define mainECHO_CLIENT_TASK_STACK_SIZE     ( configMINIMAL_STACK_SIZE * 2 )                /* Not used in the linux port. */
#define mainECHO_CLIENT_TASK_PRIORITY       ( tskIDLE_PRIORITY + 1 )

/* Define a name that will be used for LLMNR and NBNS searches. */
#define mainHOST_NAME                       "RTOSDemo"
#define mainDEVICE_NICK_NAME                "qemu_demo"

/* Set the following constants to 1 or 0 to define which tasks to include and
 * exclude:
 *
 * mainCREATE_TCP_ECHO_TASKS_SINGLE:  When set to 1 a set of tasks are created that
 * send TCP echo requests to the standard echo port (port 7), then wait for and
 * verify the echo reply, from within the same task (Tx and Rx are performed in the
 * same RTOS task).  The IP address of the echo server must be configured using the
 * configECHO_SERVER_ADDR0 to configECHO_SERVER_ADDR3 constants in
 * FreeRTOSConfig.h.
 *
 */
#define mainCREATE_TCP_ECHO_TASKS_SINGLE    1

/*-----------------------------------------------------------*/

/*
 * Just seeds the simple pseudo random number generator.
 */
static void prvSRand( UBaseType_t ulSeed );

/*
 * Miscellaneous initialisation including preparing the logging and seeding the
 * random number generator.
 */
static void prvMiscInitialisation( void );

/* The default IP and MAC address used by the demo.  The address configuration
 * defined here will be used if ipconfigUSE_DHCP is 0, or if ipconfigUSE_DHCP is
 * 1 but a DHCP server could not be contacted.  See the online documentation for
 * more information. */
static const uint8_t ucIPAddress[ 4 ] =
{
    configIP_ADDR0,
    configIP_ADDR1,
    configIP_ADDR2,
    configIP_ADDR3
};
static const uint8_t ucNetMask[ 4 ] =
{
    configNET_MASK0,
    configNET_MASK1,
    configNET_MASK2,
    configNET_MASK3
};
static const uint8_t ucGatewayAddress[ 4 ] =
{
    configGATEWAY_ADDR0,
    configGATEWAY_ADDR1,
    configGATEWAY_ADDR2,
    configGATEWAY_ADDR3
};
static const uint8_t ucDNSServerAddress[ 4 ] =
{
    configDNS_SERVER_ADDR0,
    configDNS_SERVER_ADDR1,
    configDNS_SERVER_ADDR2,
    configDNS_SERVER_ADDR3
};
const uint8_t ucMACAddress[ 6 ] =
{
    configMAC_ADDR0,
    configMAC_ADDR1,
    configMAC_ADDR2,
    configMAC_ADDR3,
    configMAC_ADDR4,
    configMAC_ADDR5
};

/* Use by the pseudo random number generator. */
static UBaseType_t ulNextRand;

#if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )

/* In case multiple interfaces are used, define them statically. */

/* There is only 1 physical interface. */
    static NetworkInterface_t xInterfaces[ 1 ];

/* It will have several end-points. */
    static NetworkEndPoint_t xEndPoints[ 4 ];

#endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */

/*-----------------------------------------------------------*/

void main_tcp_echo_client_tasks( void )
{
    BaseType_t xReturn;
    const uint32_t ulLongTime_ms = pdMS_TO_TICKS( 1000UL );

    /*
     * Instructions for using this project are provided on:
     * https://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
     */

    /* Miscellaneous initialisation including preparing the logging and seeding
     * the random number generator. */
    prvMiscInitialisation();

    /* Initialise the network interface.
     *
     ***NOTE*** Tasks that use the network are created in the network event hook
     * when the network is connected and ready for use (see the definition of
     * vApplicationIPNetworkEventHook() below).  The address values passed in here
     * are used if ipconfigUSE_DHCP is set to 0, or if ipconfigUSE_DHCP is set to 1
     * but a DHCP server cannot be contacted. */

    /* Initialise the network interface.*/
    FreeRTOS_debug_printf( ( "FreeRTOS_IPInit\r\n" ) );

    /* Set Ethernet interrupt priority to configMAC_INTERRUPT_PRIORITY. */
    NVIC_SetPriority( ETHERNET_IRQn, configMAC_INTERRUPT_PRIORITY );

    #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
        /* Initialise the interface descriptor for WinPCap. */
        extern NetworkInterface_t * pxMPS2_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                                    NetworkInterface_t * pxInterface );
        pxMPS2_FillInterfaceDescriptor( 0, &( xInterfaces[ 0 ] ) );

        /* === End-point 0 === */
        FreeRTOS_FillEndPoint( &( xInterfaces[ 0 ] ), &( xEndPoints[ 0 ] ), ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );
    #if ( ipconfigUSE_DHCP != 0 )
        {
            /* End-point 0 wants to use DHCPv4. */
            xEndPoints[ 0 ].bits.bWantDHCP = pdTRUE;
        }
        #endif /* ( ipconfigUSE_DHCP != 0 ) */

        xReturn = FreeRTOS_IPInit_Multi();
    #else /* if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */
        /* Using the old /single /IPv4 library, or using backward compatible mode of the new /multi library. */
        xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );
    #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */

    configASSERT( xReturn == pdTRUE );

    /* Start the RTOS scheduler. */
    FreeRTOS_debug_printf( ( "vTaskStartScheduler\n" ) );
    vTaskStartScheduler();
    FreeRTOS_debug_printf( ( "Should not reach this point after scheduler\n" ) );

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks to be created.  See the memory management section on the
     * FreeRTOS web site for more details (this is standard text that is not not
     * really applicable to the Linux simulator port). */
    for( ; ; )
    {
        usleep( ulLongTime_ms * 1000 );
    }
}
/*-----------------------------------------------------------*/

BaseType_t xTasksAlreadyCreated = pdFALSE;

/* Called by FreeRTOS+TCP when the network connects or disconnects.  Disconnect
 * events are only received if implemented in the MAC driver. */
#if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
    void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                               struct xNetworkEndPoint * pxEndPoint )
#else
    void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
#endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */
{
    uint32_t ulIPAddress;
    uint32_t ulNetMask;
    uint32_t ulGatewayAddress;
    uint32_t ulDNSServerAddress;
    char cBuffer[ 16 ];

    #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
        ( void ) pxEndPoint;
    #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */

    /* If the network has just come up...*/
    if( eNetworkEvent == eNetworkUp )
    {
        /* Create the tasks that use the IP stack if they have not already been
         * created. */
        if( xTasksAlreadyCreated == pdFALSE )
        {
            /* See the comments above the definitions of these pre-processor
             * macros at the top of this file for a description of the individual
             * demo tasks. */

            #if ( mainCREATE_TCP_ECHO_TASKS_SINGLE == 1 )
            {
                vStartTCPEchoClientTasks_SingleTasks( mainECHO_CLIENT_TASK_STACK_SIZE,
                                                      mainECHO_CLIENT_TASK_PRIORITY );
            }
            #endif /* mainCREATE_TCP_ECHO_TASKS_SINGLE */

            xTasksAlreadyCreated = pdTRUE;
        }

        /* Print out the network configuration, which may have come from a DHCP
         * server. */
        #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
            FreeRTOS_GetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, pxNetworkEndPoints );
        #else
            FreeRTOS_GetAddressConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress );
        #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */
        FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
        FreeRTOS_printf( ( "\r\n\r\nIP Address: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulNetMask, cBuffer );
        FreeRTOS_printf( ( "Subnet Mask: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulGatewayAddress, cBuffer );
        FreeRTOS_printf( ( "Gateway Address: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulDNSServerAddress, cBuffer );
        FreeRTOS_printf( ( "DNS Server Address: %s\r\n\r\n\r\n", cBuffer ) );
    }
    else
    {
        FreeRTOS_printf( ( "Application idle hook network down\n" ) );
    }
}
/*-----------------------------------------------------------*/

UBaseType_t uxRand( void )
{
    const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

    /* Utility function to generate a pseudo random number. */

    ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
    return( ( int ) ( ulNextRand >> 16UL ) & 0x7fffUL );
}
/*-----------------------------------------------------------*/

static void prvSRand( UBaseType_t ulSeed )
{
    /* Utility function to seed the pseudo random number generator. */
    ulNextRand = ulSeed;
}
/*-----------------------------------------------------------*/

static void prvMiscInitialisation( void )
{
    time_t xTimeNow;
    uint32_t ulRandomNumbers[ 4 ];

    /* Seed the random number generator. */
    time( &xTimeNow );
    FreeRTOS_debug_printf( ( "Seed for randomiser: %lu\n", xTimeNow ) );
    prvSRand( ( uint32_t ) xTimeNow );

    ( void ) xApplicationGetRandomNumber( &ulRandomNumbers[ 0 ] );
    ( void ) xApplicationGetRandomNumber( &ulRandomNumbers[ 1 ] );
    ( void ) xApplicationGetRandomNumber( &ulRandomNumbers[ 2 ] );
    ( void ) xApplicationGetRandomNumber( &ulRandomNumbers[ 3 ] );
    FreeRTOS_debug_printf( ( "Random numbers: %08X %08X %08X %08X\n",
                             ulRandomNumbers[ 0 ],
                             ulRandomNumbers[ 1 ],
                             ulRandomNumbers[ 2 ],
                             ulRandomNumbers[ 3 ] ) );
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) || ( ipconfigDHCP_REGISTER_HOSTNAME == 1 )

    const char * pcApplicationHostnameHook( void )
    {
        /* Assign the name "FreeRTOS" to this network node.  This function will
         * be called during the DHCP: the machine will be registered with an IP
         * address plus this name. */
        return mainHOST_NAME;
    }

#endif
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 )

    #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
        BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                                   const char * pcName )
    #else
        BaseType_t xApplicationDNSQueryHook( const char * pcName )
    #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */
    {
        BaseType_t xReturn;

        #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
            ( void ) pxEndPoint;
        #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */

        /* Determine if a name lookup is for this node.  Two names are given
         * to this node: that returned by pcApplicationHostnameHook() and that set
         * by mainDEVICE_NICK_NAME. */
        if( strcasecmp( pcName, pcApplicationHostnameHook() ) == 0 )
        {
            xReturn = pdPASS;
        }
        else if( strcasecmp( pcName, mainDEVICE_NICK_NAME ) == 0 )
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
 * Callback that provides the inputs necessary to generate a randomized TCP
 * Initial Sequence Number per RFC 6528.  THIS IS ONLY A DUMMY IMPLEMENTATION
 * THAT RETURNS A PSEUDO RANDOM NUMBER SO IS NOT INTENDED FOR USE IN PRODUCTION
 * SYSTEMS.
 */
extern uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                                    uint16_t usSourcePort,
                                                    uint32_t ulDestinationAddress,
                                                    uint16_t usDestinationPort )
{
    ( void ) ulSourceAddress;
    ( void ) usSourcePort;
    ( void ) ulDestinationAddress;
    ( void ) usDestinationPort;

    return uxRand();
}

/*
 * Supply a random number to FreeRTOS+TCP stack.
 * THIS IS ONLY A DUMMY IMPLEMENTATION THAT RETURNS A PSEUDO RANDOM NUMBER
 * SO IS NOT INTENDED FOR USE IN PRODUCTION SYSTEMS.
 */
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *( pulNumber ) = uxRand();
    return pdTRUE;
}
