/*
 * FreeRTOS V202112.00
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

/*
 * This project is a cut down version of the project described on the following
 * link.  Only the simple UDP client and server and the TCP echo clients are
 * included in the build:
 * https://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <pthread.h>
#include <signal.h>
#include <string.h>

/* Socket includes */
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"


#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/msg.h>

/* Demo application includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Stream_Buffer.h"
/*#include "SimpleUDPClientAndServer.h" */
#include "SimpleTCPEchoServer.h"
/*#include "TCPEchoClient_SingleTasks.h" */
/*#include "logging.h" */
#include "TCPEchoClient_SingleTasks.h"
#include "PacketDrillHandlerTask.h"

/* Simple UDP client and server task parameters. */
#define mainSIMPLE_UDP_CLIENT_SERVER_TASK_PRIORITY    ( tskIDLE_PRIORITY )
#define mainSIMPLE_UDP_CLIENT_SERVER_PORT             ( 5005UL )

/* Echo client task parameters - used for both TCP and UDP echo clients. */
#define mainECHO_CLIENT_TASK_STACK_SIZE               ( configMINIMAL_STACK_SIZE * 2 )      /* Not used in the linux port. */
#define mainECHO_CLIENT_TASK_PRIORITY                 ( tskIDLE_PRIORITY + 1 )

/* Echo server task parameters. */
#define mainECHO_SERVER_TASK_STACK_SIZE               ( configMINIMAL_STACK_SIZE * 2 )      /* Not used in the linux port. */
#define mainECHO_SERVER_TASK_PRIORITY                 ( tskIDLE_PRIORITY + 1 )

/* PacketDrill handler task parameters*/
#define mainPACKETDRILL_HANDLER_PRIORITY                 ( tskIDLE_PRIORITY + 3 )

/* Define a name that will be used for LLMNR and NBNS searches. */
#define mainHOST_NAME                                 "RTOSDemo"
#define mainDEVICE_NICK_NAME                          "linux_demo"

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
#define mainCREATE_TCP_ECHO_TASKS_SINGLE              0
#define mainCREATE_TCP_ECHO_SERVER                    0
#define mainCREATE_PACKETDRILL_BRIDGE_THREAD          1
/*-----------------------------------------------------------*/

#define xSEND_BUFFER_SIZE    32768
#define xRECV_BUFFER_SIZE    32768

/*
 * Just seeds the simple pseudo random number generator.
 */
static void prvSRand( UBaseType_t ulSeed );

static int prvCreateThreadSafeBuffers( void );

/*
 * Miscellaneous initialisation including preparing the logging and seeding the
 * random number generator.
 */
static void prvMiscInitialisation( void );

static void *packetDrillBridgeThread (void *pvParameters);
size_t IntToString1(char *s, int x);

struct event * pvSendEvent = NULL;

static pthread_t packetDrillBridgeThreadHandle;

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

void main_tcp_echo_client_tasks( void )
{
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
     * but a DHCP server cannot be	contacted. */
    FreeRTOS_debug_printf( ( "FreeRTOS_IPInit\n" ) );
    FreeRTOS_IPInit( ucIPAddress,
                     ucNetMask,
                     ucGatewayAddress,
                     ucDNSServerAddress,
                     ucMACAddress );

    /* Start the RTOS scheduler. */
    FreeRTOS_debug_printf( ( "vTaskStartScheduler\n" ) );
    vTaskStartScheduler();
    FreeRTOS_debug_printf( ( "Should not reach this point after scheduler\n" ) );

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks	to be created.  See the memory management section on the
     * FreeRTOS web site for more details (this is standard text that is not not
     * really applicable to the Linux simulator port). */
    for( ; ; )
    {
        usleep( ulLongTime_ms * 1000 );
    }
}
/*-----------------------------------------------------------*/

#define mbaTASK_MESSAGE_BUFFER_SIZE       ( 60 )
StreamBuffer_t * xSendBuffer = NULL;
StreamBuffer_t * xRecvBuffer = NULL;


/* ====================== Static Function definitions ======================= */

/*!
 * @brief create thread safe buffers to send/receive packets between threads
 * @returns
 */
static int prvCreateThreadSafeBuffers( void )
{
    int ret = pdFAIL;

    /* The buffer used to pass data to be transmitted from a FreeRTOS task to
     * the linux thread that sends via the pcap library. */
    do
    {
        if( xSendBuffer == NULL )
        {
            xSendBuffer = ( StreamBuffer_t * ) malloc( sizeof( *xSendBuffer ) - sizeof( xSendBuffer->ucArray ) + xSEND_BUFFER_SIZE + 1 );

            if( xSendBuffer == NULL )
            {
                break;
            }

            configASSERT( xSendBuffer );
            memset( xSendBuffer, '\0', sizeof( *xSendBuffer ) - sizeof( xSendBuffer->ucArray ) );
            xSendBuffer->LENGTH = xSEND_BUFFER_SIZE + 1;
        }

        /* The buffer used to pass received data from the pthread that receives
         * via the pcap library to the FreeRTOS task. */
        if( xRecvBuffer == NULL )
        {
            xRecvBuffer = ( StreamBuffer_t * ) malloc( sizeof( *xRecvBuffer ) - sizeof( xRecvBuffer->ucArray ) + xRECV_BUFFER_SIZE + 1 );

            if( xRecvBuffer == NULL )
            {
                break;
            }

            configASSERT( xRecvBuffer );
            memset( xRecvBuffer, '\0', sizeof( *xRecvBuffer ) - sizeof( xRecvBuffer->ucArray ) );
            xRecvBuffer->LENGTH = xRECV_BUFFER_SIZE + 1;
        }

        ret = pdPASS;
    } while( 0 );

    if (pvSendEvent == NULL) {
        pvSendEvent = event_create();
    }


    return ret;
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
        /* Create the tasks that use the IP stack if they have not already been
         * created. */
        if( xTasksAlreadyCreated == pdFALSE )
        {
            /* See the comments above the definitions of these pre-processor
             * macros at the top of this file for a description of the individual
             * demo tasks. */

            #if ( mainCREATE_TCP_ECHO_TASKS_SINGLE == 1 )
                {
                    vStartTCPEchoClientTasks_SingleTasks( mainECHO_CLIENT_TASK_STACK_SIZE, mainECHO_CLIENT_TASK_PRIORITY );
                }
            #endif /* mainCREATE_TCP_ECHO_TASKS_SINGLE */

            #if (mainCREATE_TCP_ECHO_SERVER == 1)
                {
                    vStartSimpleTCPServerTasks( mainECHO_CLIENT_TASK_STACK_SIZE, mainECHO_CLIENT_TASK_PRIORITY );
                }
            #endif /* mainCREATE_TCP_ECHO_SERVER */

            #if (mainCREATE_PACKETDRILL_BRIDGE_THREAD == 1)
                {
                    BaseType_t ret = prvCreateThreadSafeBuffers();

                    if (ret == pdPASS) {
                        pthread_create(&packetDrillBridgeThreadHandle, NULL, packetDrillBridgeThread, NULL);
                        vStartPacketDrillHandlerTask(mainECHO_CLIENT_TASK_STACK_SIZE, mainPACKETDRILL_HANDLER_PRIORITY);
                    } else {
                        FreeRTOS_debug_printf(("We could not create the thread buffers...\n"));

                    }

                }
            #endif

            xTasksAlreadyCreated = pdTRUE;
        }

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
    else
    {
        FreeRTOS_printf( "Application idle hook network down\n" );
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

    BaseType_t xApplicationDNSQueryHook( const char * pcName )
    {
        BaseType_t xReturn;

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

#define BACKLOG 5
#define SOCKET_NAME "/tmp/mysocket1"
#define BUF_SIZE 20

static void *packetDrillBridgeThread (void *pvParameters)
{
    sigset_t set;
    sigfillset( &set );
    pthread_sigmask( SIG_SETMASK, &set, NULL);

    const time_t xMaxMSToWait = 500000;

    FreeRTOS_debug_printf(("PacketDrill Bridge Thread started...\n"));

    struct sockaddr_un addr;

    unlink(SOCKET_NAME);

    int sfd = socket(AF_UNIX, SOCK_STREAM, 0);

    if (sfd == -1) {
        FreeRTOS_debug_printf(("Error creating socket...\n"));
        return NULL;
    }

    // Zero out the address, and set family and path.
    memset(&addr, 0, sizeof(struct sockaddr_un));
    addr.sun_family = AF_UNIX;
    strcpy(addr.sun_path, SOCKET_NAME);

    if (bind(sfd, (struct sockaddr *) &addr, sizeof(struct sockaddr_un)) == -1) {
        FreeRTOS_debug_printf(("Error binding socket to port...\n"));
        return NULL;
    }

    if (listen(sfd, BACKLOG) ==-1) {
        FreeRTOS_debug_printf(("Error listening on socket...\n"));
        return NULL;
    }

    for (;;) {

        FreeRTOS_debug_printf(("Waiting to accept a connection...\n"));

        int cfd = accept(sfd, NULL, NULL);

        if (cfd == -1) {
            FreeRTOS_debug_printf(("Error accepting connection...\n"));
            return NULL;
        }
        FreeRTOS_debug_printf(("Accepted socket fd = %d\n", cfd));

        //
        // Transfer data from connected socket to stdout until EOF */
        //

        ssize_t numRead;
        struct SyscallPackage syscallPackage;

        size_t xSpace;

            // Read at most BUF_SIZE bytes from the socket into buf.
        while ((numRead = read(cfd, &syscallPackage, sizeof(struct SyscallPackage))) > 0) {

            if (syscallPackage.bufferedMessage == 1) {
                void *buffer = malloc(syscallPackage.bufferedCount);
                size_t bufferCount = read(cfd, buffer, syscallPackage.bufferedCount);

                if (bufferCount <= 0) {
                    FreeRTOS_debug_printf(("Error reading buffer content from socket\n"));
                } else if (bufferCount != syscallPackage.bufferedCount) {
                    FreeRTOS_debug_printf(("Count of buffer not equal to expected count.\n"));
                } else {
                    FreeRTOS_debug_printf(("Successfully read buffer count from socket.\n"));
                }

                syscallPackage.buffer = buffer;

            }

            xSpace = uxStreamBufferGetSpace( xSendBuffer );

            if (xSpace >= sizeof(struct SyscallPackage)) {
                uxStreamBufferAdd( xSendBuffer,
                                   0,
                                   ( const uint8_t * ) &syscallPackage,
                                   sizeof( struct SyscallPackage ) );

            } else {
                FreeRTOS_debug_printf(("There is not enough space in send buffer...\n"));
                continue;
            }

            //TODO: Modify the wait time such that for calls like accept, it waits indefinitely,
            // while it returns an error for other non-blocking calls.

            event_wait_timed( pvSendEvent, xMaxMSToWait );

            size_t data_size = sizeof(struct SyscallResponsePackage);
            struct SyscallResponsePackage syscallResponse;

            if (uxStreamBufferGetSize( xRecvBuffer ) < data_size) {
                FreeRTOS_debug_printf(("Not enough data in receive buffer...\n"));
            }

            uxStreamBufferGet( xRecvBuffer, 0, ( uint8_t * ) &syscallResponse, data_size, pdFALSE );

            FreeRTOS_debug_printf(("Syscall response buffer received: %d...\n", syscallResponse.result));

            int numWrote = write(cfd, &syscallResponse, data_size);

            if (numWrote == -1) {
                FreeRTOS_debug_printf(("Error writing socket response...\n"));
            } else {
                FreeRTOS_debug_printf(("Successfully wrote socket response to Packetdrill...\n"));
            }


        }

        if (numRead == 0) {
            FreeRTOS_debug_printf(("About to unlink\n"));
        }

        if (numRead == -1) {
          FreeRTOS_debug_printf(("Error reading from socket...\n"));

        }

        if (close(cfd) == -1) {
          FreeRTOS_debug_printf(("Error closing socket...\n"));

        }

        resetPacketDrillTask();
    }

    // TODO: How do I close this socket when the program is terminated.
    close(sfd);
    unlink(SOCKET_NAME);
}

/*  IntToString converts the int x to a decimal numeral, which is written to s.
    No terminal null character is written.  The number of characters written is
    returned.  s MUST point to space with enough room for the numeral,
    including a leading '-' if x is negative.
    Copied from https://stackoverflow.com/questions/15746983/how-to-write-int-to-file-using-write-system-call-and-read-them-exactly-as-writte
*/
size_t IntToString1(char *s, int x)
{
    //  Set pointer to current position.
    char *p = s;

    //  Set t to absolute value of x.
    unsigned t = x;
    if (x < 0) t = -t;

    //  Write digits.
    do
    {
        *p++ = '0' + t % 10;
        t /= 10;
    } while (t);

    //  If x is negative, write sign.
    if (x < 0)
        *p++ = '-';

    //  Remember the return value, the number of characters written.
    size_t r = p-s;

    //  Since we wrote the characters in reverse order, reverse them.
    while (s < --p)
    {
        char t = *s;
        *s++ = *p;
        *p = t;
    }

    return r;
}

