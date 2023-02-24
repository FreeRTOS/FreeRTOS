/*
 * FreeRTOS+TCP V2.3.2
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/*
 * This project is a cut down version of the project described on the following
 * link.  Only the simple UDP client and server and the TCP echo clients are
 * included in the build:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdio.h>
#include <time.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "semphr.h"

/* Demo application includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Routing.h"

#if ( ipconfigMULTI_INTERFACE == 1 )
    #include "FreeRTOS_ND.h"
#endif

#include "logging.h"

#include "plus_tcp_demo_cli.h"

#ifndef ARRAY_SIZE
    #define ARRAY_SIZE( x )    ( int ) ( sizeof( x ) / sizeof( x )[ 0 ] )
#endif

/* Simple UDP client and server task parameters. */
#define mainSIMPLE_UDP_CLIENT_SERVER_TASK_PRIORITY    ( tskIDLE_PRIORITY )
#define mainSIMPLE_UDP_CLIENT_SERVER_PORT             ( 5005UL )

/* Echo client task parameters - used for both TCP and UDP echo clients. */
#define mainECHO_CLIENT_TASK_STACK_SIZE               ( configMINIMAL_STACK_SIZE * 2 )      /* Not used in the Windows port. */
#define mainECHO_CLIENT_TASK_PRIORITY                 ( tskIDLE_PRIORITY + 1 )

/* Echo server task parameters. */
#define mainECHO_SERVER_TASK_STACK_SIZE               ( configMINIMAL_STACK_SIZE * 2 )      /* Not used in the Windows port. */
#define mainECHO_SERVER_TASK_PRIORITY                 ( tskIDLE_PRIORITY + 1 )

/* Define a name that will be used for LLMNR and NBNS searches. */
#define mainHOST_NAME                                 "RTOSDemo"
#define mainDEVICE_NICK_NAME                          "windows_demo"

/* Set the following constants to 1 or 0 to define which tasks to include and
 * exclude:
 *
 * mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS:  When set to 1 two UDP client tasks
 * and two UDP server tasks are created.  The clients talk to the servers.  One set
 * of tasks use the standard sockets interface, and the other the zero copy sockets
 * interface.  These tasks are self checking and will trigger a configASSERT() if
 * they detect a difference in the data that is received from that which was sent.
 * As these tasks use UDP, and can therefore loose packets, they will cause
 * configASSERT() to be called when they are run in a less than perfect networking
 * environment.
 *
 * mainCREATE_TCP_ECHO_TASKS_SINGLE:  When set to 1 a set of tasks are created that
 * send TCP echo requests to the standard echo port (port 7), then wait for and
 * verify the echo reply, from within the same task (Tx and Rx are performed in the
 * same RTOS task).  The IP address of the echo server must be configured using the
 * configECHO_SERVER_ADDR0 to configECHO_SERVER_ADDR3 constants in
 * FreeRTOSConfig.h.
 *
 * mainCREATE_TCP_ECHO_SERVER_TASK:  When set to 1 a task is created that accepts
 * connections on the standard echo port (port 7), then echos back any data
 * received on that connection.
 */
#define mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS     0
#define mainCREATE_TCP_ECHO_TASKS_SINGLE              0
#define mainCREATE_TCP_ECHO_SERVER_TASK               0
/*-----------------------------------------------------------*/

/* Define a task that is used to start and monitor several tests. */
static void prvServerWorkTask( void * pvArgument );

/* Let this task run at a low priority. */
#define mainTCP_SERVER_TASK_PRIORITY    ( tskIDLE_PRIORITY + 1 )

/* Give it an appropriate stack size. */
#define mainTCP_SERVER_STACK_SIZE       2048

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
static const uint8_t ucIPAddress[ 4 ] = { configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 };
static const uint8_t ucNetMask[ 4 ] = { configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 };
static const uint8_t ucGatewayAddress[ 4 ] = { configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3 };
static const uint8_t ucDNSServerAddress[ 4 ] = { configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3 };

/* Set the following constant to pdTRUE to log using the method indicated by the
 * name of the constant, or pdFALSE to not log using the method indicated by the
 * name of the constant.  Options include to standard out (xLogToStdout), to a disk
 * file (xLogToFile), and to a UDP port (xLogToUDP).  If xLogToUDP is set to pdTRUE
 * then UDP messages are sent to the IP address configured as the echo server
 * address (see the configECHO_SERVER_ADDR0 definitions in FreeRTOSConfig.h) and
 * the port number set by configPRINT_PORT in FreeRTOSConfig.h. */
const BaseType_t xLogToStdout = pdTRUE, xLogToFile = pdFALSE, xLogToUDP = pdFALSE;

/* Default MAC address configuration.  The demo creates a virtual network
 * connection that uses this MAC address by accessing the raw Ethernet data
 * to and from a real network connection on the host PC.  See the
 * configNETWORK_INTERFACE_TO_USE definition for information on how to configure
 * the real network connection to use. */
const uint8_t ucMACAddress[ 6 ] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };

/* Use by the pseudo random number generator. */
static UBaseType_t ulNextRand;

/*-----------------------------------------------------------*/

#if ( ipconfigMULTI_INTERFACE == 1 ) && ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )
    /* In case multiple interfaces are used, define them statically. */

/* With WinPCap there is only 1 physical interface. */
    static NetworkInterface_t xInterfaces[ 1 ];

/* It will have several end-points. */
    static NetworkEndPoint_t xEndPoints[ 3 ];

/* A function from NetInterface.c to initialise the interface descriptor
 * of type 'NetworkInterface_t'. */
    NetworkInterface_t * xWinPcap_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                           NetworkInterface_t * pxInterface );
#endif /* ipconfigMULTI_INTERFACE */

int main( void )
{
    const uint32_t ulLongTime_ms = pdMS_TO_TICKS( 1000UL );

    /*
     * Instructions for using this project are provided on:
     * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
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
     * but a DHCP server cannot be	contacted. */

    #if ( ipconfigMULTI_INTERFACE == 0 ) || ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 )
        /* Using the old /single /IPv4 library, or using backward compatible mode of the new /multi library. */
        FreeRTOS_debug_printf( ( "FreeRTOS_IPInit\r\n" ) );
        FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );
    #else
        /* Initialise the interface descriptor for WinPCap. */
        xWinPcap_FillInterfaceDescriptor( 0, &( xInterfaces[ 0 ] ) );

        FreeRTOS_FillEndPoint( &( xInterfaces[ 0 ] ), &( xEndPoints[ 0 ] ), ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );
        #if ( ipconfigUSE_DHCP != 0 )
            {
                /* End-point 0 wants to use DHCPv4. */
                xEndPoints[ 0 ].bits.bWantDHCP = pdTRUE;
            }
        #endif /* ( ipconfigUSE_DHCP != 0 ) */

        {
            /* For testing Raspberry PI. */
            const uint8_t ucIPAddress2[ 4 ] = { 10, 0, 1, 6 };
            const uint8_t ucNetMask2[ 4 ] = { 255, 0, 0, 0 };
            const uint8_t ucGatewayAddress2[ 4 ] = { 0, 0, 0, 0 };
            const uint8_t ucDNSServerAddress2[ 4 ] = { 0, 0, 0, 0 };
            FreeRTOS_FillEndPoint( &( xInterfaces[ 0 ] ), &( xEndPoints[ 1 ] ), ucIPAddress2, ucNetMask2, ucGatewayAddress2, ucDNSServerAddress2, ucMACAddress );
        }

        #if ( ipconfigUSE_DHCP != 0 )
            {
                /* End-point 1 does not want to use DHCPv4. */
                xEndPoints[ 1 ].bits.bWantDHCP = pdFALSE;
            }
        #endif /* ( ipconfigUSE_DHCP != 0 ) */

        /*
         * End-point-1  // public
         *     Network: 2001:470:ec54::/64
         *     IPv6   : 2001:470:ec54::4514:89d5:4589:8b79/128
         *     Gateway: fe80::9355:69c7:585a:afe7  // obtained from Router Advertisement
         */
        #if ( ipconfigUSE_IPv6 != 0 )
            {
                IPv6_Address_t xIPAddress;
                IPv6_Address_t xPrefix;
                IPv6_Address_t xGateWay;
                IPv6_Address_t xDNSServer;

                FreeRTOS_inet_pton6( "2001:470:ec54::", xPrefix.ucBytes );
                FreeRTOS_inet_pton6( "2001:4860:4860::8888", xDNSServer.ucBytes );

                FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, 64, pdTRUE );
                FreeRTOS_inet_pton6( "fe80::9355:69c7:585a:afe7", xGateWay.ucBytes );

                FreeRTOS_FillEndPoint_IPv6( &( xInterfaces[ 0 ] ),
                                            &( xEndPoints[ 2 ] ),
                                            &( xIPAddress ),
                                            &( xPrefix ),
                                            64uL,            /* Prefix length. */
                                            &( xGateWay ),
                                            &( xDNSServer ), /* pxDNSServerAddress: Not used yet. */
                                            ucMACAddress );
                #if ( ipconfigUSE_RA != 0 )
                    {
                        /* End-point 1 wants to use Router Advertisement / SLAAC. */
                        xEndPoints[ 2 ].bits.bWantRA = pdTRUE;
                    }
                #endif /* #if( ipconfigUSE_RA != 0 ) */
                #if ( ipconfigUSE_DHCPv6 != 0 )
                    {
                        /* End-point 1 wants to use DHCPv6. */
                        xEndPoints[ 2 ].bits.bWantDHCP = pdTRUE;
                    }
                #endif /* ( ipconfigUSE_DHCPv6 != 0 ) */
            }
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        FreeRTOS_IPStart();
    #endif /* if ( ipconfigMULTI_INTERFACE == 0 ) || ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 ) */
    xTaskCreate( prvServerWorkTask, "SvrWork", mainTCP_SERVER_STACK_SIZE, NULL, mainTCP_SERVER_TASK_PRIORITY, NULL );

    /* Start the RTOS scheduler. */
    FreeRTOS_debug_printf( ( "vTaskStartScheduler\r\n" ) );
    vTaskStartScheduler();

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks	to be created.  See the memory management section on the
     * FreeRTOS web site for more details (this is standard text that is not not
     * really applicable to the Win32 simulator port). */
    for( ; ; )
    {
        Sleep( ulLongTime_ms );
    }
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    const uint32_t ulMSToSleep = 1;

    /* This is just a trivial example of an idle hook.  It is called on each
     * cycle of the idle task if configUSE_IDLE_HOOK is set to 1 in
     * FreeRTOSConfig.h.  It must *NOT* attempt to block.  In this case the
     * idle task just sleeps to lower the CPU usage. */
    Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vAssertCalled( const char * pcFile,
                    uint32_t ulLine )
{
    const uint32_t ulLongSleep = 1000UL;
    volatile uint32_t ulBlockVariable = 0UL;
    volatile char * pcFileName = ( volatile char * ) pcFile;
    volatile uint32_t ulLineNumber = ulLine;

    ( void ) pcFileName;
    ( void ) ulLineNumber;

    FreeRTOS_debug_printf( ( "vAssertCalled( %s, %ld\r\n", pcFile, ulLine ) );

    /* Setting ulBlockVariable to a non-zero value in the debugger will allow
     * this function to be exited. */
    taskDISABLE_INTERRUPTS();
    {
        while( ulBlockVariable == 0UL )
        {
            Sleep( ulLongSleep );
        }
    }
    taskENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+TCP when the network connects or disconnects.  Disconnect
 * events are only received if implemented in the MAC driver. */
/* *INDENT-OFF* */
#if ( ipconfigMULTI_INTERFACE != 0 ) || ( ipconfigCOMPATIBLE_WITH_SINGLE != 0 )
    /* The multi version: each end-point comes up individually. */
    void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent,
                                         NetworkEndPoint_t * pxEndPoint )
#else
    /* The single version, the interface comes up as a whole. */
    void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
#endif
/* *INDENT-ON* */
{
    char cBuffer[ 16 ];
    static BaseType_t xTasksAlreadyCreated = pdFALSE;

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
            #if ( mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS == 1 )
                {
                    vStartSimpleUDPClientServerTasks( configMINIMAL_STACK_SIZE, mainSIMPLE_UDP_CLIENT_SERVER_PORT, mainSIMPLE_UDP_CLIENT_SERVER_TASK_PRIORITY );
                }
            #endif /* mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS */

            #if ( mainCREATE_TCP_ECHO_TASKS_SINGLE == 1 )
                {
                    vStartTCPEchoClientTasks_SingleTasks( mainECHO_CLIENT_TASK_STACK_SIZE, mainECHO_CLIENT_TASK_PRIORITY );
                }
            #endif /* mainCREATE_TCP_ECHO_TASKS_SINGLE */

            #if ( mainCREATE_TCP_ECHO_SERVER_TASK == 1 )
                {
                    vStartSimpleTCPServerTasks( mainECHO_SERVER_TASK_STACK_SIZE, mainECHO_SERVER_TASK_PRIORITY );
                }
            #endif

            xTasksAlreadyCreated = pdTRUE;
        }

        #if ( ipconfigMULTI_INTERFACE == 0 )
            {
                uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;

                /* Print out the network configuration, which may have come from a DHCP
                 * server. */
                FreeRTOS_GetAddressConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress );
                FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
                FreeRTOS_printf( ( "\r\n\r\nIP Address: %s\r\n", cBuffer ) );

                FreeRTOS_inet_ntoa( ulNetMask, cBuffer );
                FreeRTOS_printf( ( "Subnet Mask: %s\r\n", cBuffer ) );

                FreeRTOS_inet_ntoa( ulGatewayAddress, cBuffer );
                FreeRTOS_printf( ( "Gateway Address: %s\r\n", cBuffer ) );

                FreeRTOS_inet_ntoa( ulDNSServerAddress, cBuffer );
                FreeRTOS_printf( ( "DNS Server Address: %s\r\n\r\n\r\n", cBuffer ) );
            }
        #else /* if ( ipconfigMULTI_INTERFACE == 0 ) */
            {
                /* Print out the network configuration, which may have come from a DHCP
                 * server. */
                showEndPoint( pxEndPoint );
            }
        #endif /* ipconfigMULTI_INTERFACE */
    }
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
    /* Called if a call to pvPortMalloc() fails because there is insufficient
     * free memory available in the FreeRTOS heap.  pvPortMalloc() is called
     * internally by FreeRTOS API functions that create tasks, queues, software
     * timers, and semaphores.  The size of the FreeRTOS heap is set by the
     * configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
    vAssertCalled( __FILE__, __LINE__ );
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
    uint32_t ulLoggingIPAddress;

    ulLoggingIPAddress = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0, configECHO_SERVER_ADDR1, configECHO_SERVER_ADDR2, configECHO_SERVER_ADDR3 );
    vLoggingInit( xLogToStdout, xLogToFile, xLogToUDP, ulLoggingIPAddress, configPRINT_PORT );

    /* Seed the random number generator. */
    time( &xTimeNow );
    FreeRTOS_debug_printf( ( "Seed for randomiser: %lu\r\n", xTimeNow ) );
    prvSRand( ( uint32_t ) xTimeNow );
    FreeRTOS_debug_printf( ( "Random numbers: %08X %08X %08X %08X\r\n", ipconfigRAND32(), ipconfigRAND32(), ipconfigRAND32(), ipconfigRAND32() ) );
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
/*-----------------------------------------------------------*/

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
/*-----------------------------------------------------------*/

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
/*-----------------------------------------------------------*/

const char * pcCommandList[] =
{
    "http4 google.de /index.html",
    "http6 google.nl /index.html",
    "ping4 10.0.1.10",
    "ping4 192.168.2.1",
    "dnsq4 amazon.com",
    "ping6 google.de",
    "ntp6a 2.europe.pool.ntp.org",
};

static void prvServerWorkTask( void * pvArgument )
{
    BaseType_t xCommandIndex = 0;

    ( void ) pvArgument;
    FreeRTOS_printf( ( "prvServerWorkTask started\n" ) );

    do
    {
        vTaskDelay( pdMS_TO_TICKS( 100U ) );
    }
    while( FreeRTOS_IsNetworkUp() == pdFALSE );

    for( ; ; )
    {
        char pcCommand[ 129 ];
        TickType_t uxTickCount = pdMS_TO_TICKS( 2000U );

        while( uxTickCount > 0U )
        {
            xHandleTesting();
            vTaskDelay( 1U );
            uxTickCount--;
        }

        if( xCommandIndex < ARRAY_SIZE( pcCommandList ) )
        {
            snprintf( pcCommand, sizeof( pcCommand ), "%s", pcCommandList[ xCommandIndex ] );
            FreeRTOS_printf( ( "\n" ) );
            FreeRTOS_printf( ( "/*==================== %s (%d/%d) ====================*/\n",
                               pcCommand, xCommandIndex + 1, ARRAY_SIZE( pcCommandList ) ) );
            FreeRTOS_printf( ( "\n" ) );
            xHandleTestingCommand( pcCommand, sizeof( pcCommand ) );
            xCommandIndex++;
        }
    }
}

#if ( ipconfigUSE_NTP_DEMO != 0 )

/* Some functions to get NTP demo working. */

    extern BaseType_t xNTPHasTime;
    extern uint32_t ulNTPTime;

    struct
    {
        uint32_t ntpTime;
    }
    time_guard;

    int set_time( time_t * pxTime )
    {
        ( void ) pxTime;
        time_guard.ntpTime = ulNTPTime - xTaskGetTickCount() / configTICK_RATE_HZ;
        return 0;
    }
/*-----------------------------------------------------------*/

    time_t get_time( time_t * puxTime )
    {
        time_t xTime = 0U;

        if( xNTPHasTime != pdFALSE )
        {
            TickType_t passed = xTaskGetTickCount() / configTICK_RATE_HZ;
            xTime = ( time_t ) time_guard.ntpTime + ( time_t ) passed;
        }

        if( puxTime != NULL )
        {
            *( puxTime ) = xTime;
        }

        return xTime;
    }
/*-----------------------------------------------------------*/

    struct tm * gmtime_r( const time_t * pxTime,
                          struct tm * tmStruct )
    {
        struct tm tm;

        memcpy( &( tm ), gmtime( pxTime ), sizeof( tm ) );

        if( tmStruct != NULL )
        {
            memcpy( tmStruct, &( tm ), sizeof tm );
        }

        return &( tm );
    }
/*-----------------------------------------------------------*/

#endif /* ( ipconfigUSE_NTP_DEMO != 0 ) */

BaseType_t xApplicationMemoryPermissions( uint32_t aAddress )
{
    return 0x03;
}
/*-----------------------------------------------------------*/

void vOutputChar( const char cChar,
                  const TickType_t xTicksToWait )
{
}
/*-----------------------------------------------------------*/
