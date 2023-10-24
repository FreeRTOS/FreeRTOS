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
 * A set of tasks are created that send UDP echo requests to the
 * IP address set by the configECHO_SERVER_ADDR0 to
 * configECHO_SERVER_ADDR_STRING constant, then wait for and verify the reply
 *
 * See the following web page for essential demo usage and configuration
 * details:
 * https://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"


#define USE_ZERO_COPY           ( 1 )

/* The echo tasks create a socket, send out a number of echo requests, listen
 * for the echo reply, then close the socket again before starting over.  This
 * delay is used between each iteration to ensure the network does not get too
 * congested. */
#define echoLOOP_DELAY          pdMS_TO_TICKS( 2U )

/* The number of instances of the echo client task to create. */
#define echoNUM_ECHO_CLIENTS    ( 1 )

#define TX_RX_STR_SIZE          ( 25 )

/* Rx and Tx time outs are used to ensure the sockets do not wait too long for
 * missing data. */
static const TickType_t xReceiveTimeOut = pdMS_TO_TICKS( 4000 );
static const TickType_t xSendTimeOut = pdMS_TO_TICKS( 4000 );
static BaseType_t xHasStarted = pdFALSE;

/*
 * UDP echo client task
 */
static void prvUDPEchoClientTask( void * pvParameters );

void vStartUDPEchoClientTasks_SingleTasks( uint16_t usTaskStackSize,
                                           UBaseType_t uxTaskPriority )
{
    if( xHasStarted == pdFALSE )
    {
        BaseType_t xCount = 0;
        BaseType_t x;

        xHasStarted = pdTRUE;

        /* Create the echo client tasks. */
        for( x = 0; x < echoNUM_ECHO_CLIENTS; x++ )
        {
            char ucName[ 16 ];
            snprintf( ucName, sizeof ucName, "echo_%02d", ( int ) x );
            BaseType_t rc = xTaskCreate( prvUDPEchoClientTask, /* The function that implements the task. */
                                         ucName,               /* Just a text name for the task to aid debugging. */
                                         usTaskStackSize,      /* The stack size is defined in FreeRTOSIPConfig.h. */
                                         ( void * ) x,         /* The task parameter, not used in this case. */
                                         uxTaskPriority,       /* The priority assigned to the task is defined in FreeRTOSConfig.h. */
                                         NULL );               /* The task handle is not used. */

            if( rc == pdPASS )
            {
                xCount++;
            }
        }

        configPRINTF( ( "Started %d / %d tasks\n", ( int ) xCount, ( int ) echoNUM_ECHO_CLIENTS ) );
    }
    else
    {
        configPRINTF( ( "vStartUDPEchoClientTasks_SingleTasks: already started\n" ) );
    }
}
/*-----------------------------------------------------------*/

static void prvUDPEchoClientTask( void * pvParameters )
{
    Socket_t xSocket;
    struct freertos_sockaddr xEchoServerAddress, xRxAddress;
    int8_t cTxString[ TX_RX_STR_SIZE ], cRxString[ TX_RX_STR_SIZE ]; /* Make sure the stack is large enough to hold these.  Turn on stack overflow checking during debug to be sure. */
    int32_t lLoopCount = 0UL;
    int32_t lReturned;
    const int32_t lMaxLoopCount = 50;
    volatile uint32_t ulRxCount = 0UL, ulTxCount = 0UL;
    uint32_t xAddressLength = sizeof( xEchoServerAddress );
    BaseType_t xFamily = FREERTOS_AF_INET;
    uint8_t ucIPType = ipTYPE_IPv4;

    /* Remove compiler warning about unused parameters. */
    ( void ) pvParameters;

    memset( &xEchoServerAddress, 0, sizeof( xEchoServerAddress ) );
    memset( &xRxAddress, 0, sizeof( xRxAddress ) );

    /* Echo requests are sent to the echo server.  The address of the echo
     * server is configured by the constants configECHO_SERVER_ADDR0 to
     * configECHO_SERVER_ADDR3 in FreeRTOSConfig.h. */

    #ifdef configECHO_SERVER_ADDR_STRING
    {
        BaseType_t rc = FreeRTOS_inet_pton( FREERTOS_AF_INET6, configECHO_SERVER_ADDR_STRING, ( void * ) xEchoServerAddress.sin_address.xIP_IPv6.ucBytes );

        if( rc == pdPASS )
        {
            xFamily = FREERTOS_AF_INET6;
            ucIPType = ipTYPE_IPv6;
        }
        else
        {
            rc = FreeRTOS_inet_pton( FREERTOS_AF_INET4, configECHO_SERVER_ADDR_STRING, ( void * ) &( xEchoServerAddress.sin_address.ulIP_IPv4 ) );
            configASSERT( rc == pdPASS );
            xFamily = FREERTOS_AF_INET4;
            ucIPType = ipTYPE_IPv4;
        }
    }
    #else /* ifdef configECHO_SERVER_ADDR_STRING */
    {
        xEchoServerAddress.sin_address.ulIP_IPv4 = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0, configECHO_SERVER_ADDR1, configECHO_SERVER_ADDR2, configECHO_SERVER_ADDR3 );
    }
    #endif /* ifdef configECHO_SERVER_ADDR_STRING */

    xEchoServerAddress.sin_len = sizeof( xEchoServerAddress );
    xEchoServerAddress.sin_port = FreeRTOS_htons( configECHO_SERVER_PORT );
    xEchoServerAddress.sin_family = xFamily;

    for( ; ; )
    {
        configPRINTF( ( "-------- Starting New Iteration --------\n" ) );
        /* Create a socket. */
        xSocket = FreeRTOS_socket( xFamily, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
        configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

        /* Set a time out so a missing reply does not cause the task to block
         * indefinitely. */
        FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );

        /* Send a number of echo requests. */
        for( lLoopCount = 0; lLoopCount < lMaxLoopCount; lLoopCount++ )
        {
            /* Create the string that is sent to the echo server. */
            sprintf( ( char * ) cTxString, "Message number %u\r\n", ulTxCount );

            #if USE_ZERO_COPY

                /*
                 * First obtain a buffer of adequate length from the TCP/IP stack into which
                 * the string will be written. */
                uint8_t * pucBuffer = FreeRTOS_GetUDPPayloadBuffer_Multi( TX_RX_STR_SIZE, portMAX_DELAY, ucIPType );
                configASSERT( pucBuffer != NULL );
                memcpy( pucBuffer, &cTxString, strlen( ( const char * ) cTxString ) + 1 );

                /* Send the string to the socket.  ulFlags is set to 0, so the zero
                 * copy interface is not used.  That means the data from cTxString is
                 * copied into a network buffer inside FreeRTOS_sendto(), and cTxString
                 * can be reused as soon as FreeRTOS_sendto() has returned.  1 is added
                 * to ensure the NULL string terminator is sent as part of the message. */
                lReturned = FreeRTOS_sendto( xSocket,                                  /* The socket being sent to. */
                                             ( void * ) pucBuffer,                     /* The data being sent. */
                                             strlen( ( const char * ) pucBuffer ) + 1, /* The length of the data being sent. */
                                             FREERTOS_ZERO_COPY,                       /* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
                                             &xEchoServerAddress,                      /* The destination address. */
                                             sizeof( xEchoServerAddress ) );
            #else /* if USE_ZERO_COPY */

                /* Send the string to the socket.  ulFlags is set to 0, so the zero
                 * copy interface is not used.  That means the data from cTxString is
                 * copied into a network buffer inside FreeRTOS_sendto(), and cTxString
                 * can be reused as soon as FreeRTOS_sendto() has returned.  1 is added
                 * to ensure the NULL string terminator is sent as part of the message. */
                lReturned = FreeRTOS_sendto( xSocket,                                  /* The socket being sent to. */
                                             ( void * ) cTxString,                     /* The data being sent. */
                                             strlen( ( const char * ) cTxString ) + 1, /* The length of the data being sent. */
                                             0,                                        /* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
                                             &xEchoServerAddress,                      /* The destination address. */
                                             sizeof( xEchoServerAddress ) );
            #endif /* if USE_ZERO_COPY */

            if( lReturned == 0 )
            {
                /* The send operation failed. */
            }
            else
            {
                /* Keep a count of how many echo requests have been transmitted so
                 * it can be compared to the number of echo replies received.  It would
                 * be expected to loose at least one to an ARP message the first time
                 * the	connection is created. */
                ulTxCount++;
                /* The send was successful. */
                FreeRTOS_debug_printf( ( "[Echo Client] Data sent...  \r\n" ) );
            }

            /* Receive data echoed back to the socket.  ulFlags is zero, so the
             * zero copy option is not being used and the received data will be
             * copied into the buffer pointed to by cRxString.  xAddressLength is
             * not actually used (at the time of writing this comment, anyway) by
             * FreeRTOS_recvfrom(), but is set appropriately in case future
             * versions do use it. */

            memset( ( void * ) cRxString, 0x00, sizeof( cRxString ) );


            #if USE_ZERO_COPY
                uint8_t * pucReceivedUDPPayload = NULL;
                lReturned = FreeRTOS_recvfrom( xSocket,
                                               &pucReceivedUDPPayload,
                                               0,
                                               FREERTOS_ZERO_COPY,
                                               &xRxAddress,
                                               &xAddressLength );

                if( pucReceivedUDPPayload != NULL )
                {
                    memcpy( ( void * ) ( cRxString ), pucReceivedUDPPayload, TX_RX_STR_SIZE );

                    FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucReceivedUDPPayload );
                }
            #else /* if USE_ZERO_COPY */
                lReturned = FreeRTOS_recvfrom( xSocket,             /* The socket being received from. */
                                               cRxString,           /* The buffer into which the received data will be written. */
                                               sizeof( cRxString ), /* The size of the buffer provided to receive the data. */
                                               0,                   /* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
                                               &xRxAddress,         /* The address from where the data was sent (the source address). */
                                               &xAddressLength );
            #endif /* USE_ZERO_COPY */

            if( lReturned > 0 )
            {
                /* Compare the transmitted string to the received string. */
                if( strcmp( ( char * ) cRxString, ( char * ) cTxString ) == 0 )
                {
                    /* The echo reply was received without error. */
                    ulRxCount++;

                    if( ( ulRxCount % 10 ) == 0 )
                    {
                        configPRINTF( ( "[Echo Client] Data was received correctly.\r\n" ) );
                    }
                }
                else
                {
                    FreeRTOS_debug_printf( ( "[Echo Client] Data received was erroneous.\r\n" ) );
                }
            }
            else
            {
                FreeRTOS_debug_printf( ( "[Echo Client] Data was not received\r\n" ) );
            }
        }

        configPRINTF( ( "Exchange (Sent/Received) : %u/%u\n", ulTxCount, ulRxCount ) );
        configPRINTF( ( "--------------------------------------\n\n" ) );

        /* Pause for a short while to ensure the network is not too
         * congested. */
        vTaskDelay( echoLOOP_DELAY );

        /* Close this socket before looping back to create another. */
        FreeRTOS_closesocket( xSocket );
    }
}
