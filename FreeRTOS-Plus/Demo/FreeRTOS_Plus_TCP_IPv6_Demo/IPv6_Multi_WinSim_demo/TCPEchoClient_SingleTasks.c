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
 * A set of tasks are created that send TCP echo requests to the standard echo
 * port (port 7) on the IP address set by the configECHO_SERVER_ADDR0 to
 * configECHO_SERVER_ADDR3 constants, then wait for and verify the reply
 * (another demo is available that demonstrates the reception being performed in
 * a task other than that from with the request was made).
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

/*#include "tcp_echo_config.h" */

/* Exclude the whole file if FreeRTOSIPConfig.h is configured to use UDP only. */
#if ( ipconfigUSE_TCP == 1 )

/* The echo tasks create a socket, send out a number of echo requests, listen
 * for the echo reply, then close the socket again before starting over.  This
 * delay is used between each iteration to ensure the network does not get too
 * congested. */
    #define echoLOOP_DELAY                pdMS_TO_TICKS( 2U )

/* The size of the buffers is a multiple of the MSS - the length of the data
 * sent is a pseudo random size between 20 and echoBUFFER_SIZES. */
    #define echoBUFFER_SIZE_MULTIPLIER    ( 3 )
    #define echoBUFFER_SIZES              ( ipconfigTCP_MSS * echoBUFFER_SIZE_MULTIPLIER )

/* The number of instances of the echo client task to create. */
    #define echoNUM_ECHO_CLIENTS          ( 1 )

/* To enable the use of zero copy interface of the TCP sockets */
    #define USE_TCP_ZERO_COPY             ( 0 )

/*-----------------------------------------------------------*/

/*
 * Uses a socket to send data to, then receive data from, the standard echo
 * port number 7.
 */
    static void prvEchoClientTask( void * pvParameters );

/*
 * Creates a pseudo random sized buffer of data to send to the echo server.
 */
    static BaseType_t prvCreateTxData( char * ucBuffer,
                                       uint32_t ulBufferLength );

/*-----------------------------------------------------------*/

/* Rx and Tx time outs are used to ensure the sockets do not wait too long for
 * missing data. */
    static const TickType_t xReceiveTimeOut = pdMS_TO_TICKS( 4000 );
    static const TickType_t xSendTimeOut = pdMS_TO_TICKS( 4000 );
    static BaseType_t xHasStarted = pdFALSE;

/* Counters for each created task - for inspection only. */
    static uint32_t ulTxRxCycles[ echoNUM_ECHO_CLIENTS ] = { 0 },
                    ulTxRxFailures[ echoNUM_ECHO_CLIENTS ] = { 0 },
                    ulConnections[ echoNUM_ECHO_CLIENTS ] = { 0 };

/* Rx and Tx buffers for each created task. */
    static char cTxBuffers[ echoNUM_ECHO_CLIENTS ][ echoBUFFER_SIZES ],
                cRxBuffers[ echoNUM_ECHO_CLIENTS ][ echoBUFFER_SIZES ];

/*-----------------------------------------------------------*/

    void vStartTCPEchoClientTasks_SingleTasks( uint16_t usTaskStackSize,
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
                BaseType_t rc = xTaskCreate( prvEchoClientTask, /* The function that implements the task. */
                                             ucName,            /* Just a text name for the task to aid debugging. */
                                             usTaskStackSize,   /* The stack size is defined in FreeRTOSIPConfig.h. */
                                             ( void * ) x,      /* The task parameter, not used in this case. */
                                             uxTaskPriority,    /* The priority assigned to the task is defined in FreeRTOSConfig.h. */
                                             NULL );            /* The task handle is not used. */

                if( rc == pdPASS )
                {
                    xCount++;
                }
            }

            configPRINTF( ( "Started %d / %d tasks\n", ( int ) xCount, ( int ) echoNUM_ECHO_CLIENTS ) );
        }
        else
        {
            configPRINTF( ( "vStartTCPEchoClientTasks_SingleTasks: already started\n" ) );
        }
    }
/*-----------------------------------------------------------*/

    static BaseType_t xIsFatalError( BaseType_t xCode )
    {
        BaseType_t xReturn = pdFALSE;

        if( ( xCode < 0 ) && ( xCode != -pdFREERTOS_ERRNO_EWOULDBLOCK ) )
        {
            xReturn = pdTRUE;
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

    static BaseType_t vTCPCreateAndSendData( Socket_t xSocket,
                                             char * pcTransmitBuffer,
                                             volatile uint32_t * pulTxCount,
                                             uint32_t ulBufferLength )
    {
        BaseType_t lStringLength;
        BaseType_t lTransmitted;
        char * pcDstBuffer;

        #if USE_TCP_ZERO_COPY
            BaseType_t xStreamBufferLength;
            char * pcBuffer;
        #endif /* USE_TCP_ZERO_COPY */

        pcDstBuffer = pcTransmitBuffer;

        #if USE_TCP_ZERO_COPY
            /* Get a direct pointer to the TX head of the circular transmit buffer */
            pcBuffer = ( char * ) FreeRTOS_get_tx_head( xSocket, &xStreamBufferLength );

            /* Check if sufficient space is there in the stream buffer. If there
             * isn't enough size use application provided buffer */
            if( xStreamBufferLength >= ulBufferLength )
            {
                /* Use the TCP stream buffer to directly create the TX data */
                pcDstBuffer = pcBuffer;
            }
        #endif /* USE_TCP_ZERO_COPY */

        lStringLength = prvCreateTxData( pcDstBuffer, ulBufferLength );

        /* Add in some unique text at the front of the string. */
        sprintf( pcDstBuffer, "TxRx message number %u", ( unsigned ) *pulTxCount );
        ( *pulTxCount )++;

        #if USE_TCP_ZERO_COPY
            /* Check to see if zero copy is used */
            if( pcDstBuffer != pcTransmitBuffer )
            {
                /* Save a copy of the data in pcTransmitBuffer
                 * which can be used to verify the echoed back data */
                memcpy( pcTransmitBuffer, pcDstBuffer, lStringLength );

                /* Set the buffer pointer as NULL to let the stack know
                 * that its a zero copy */
                pcDstBuffer = NULL;
            }
        #endif /* USE_TCP_ZERO_COPY */

        /* Send the string to the socket. */
        lTransmitted = FreeRTOS_send( xSocket,                /* The socket being sent to. */
                                      ( void * ) pcDstBuffer, /* The data being sent. */
                                      lStringLength,          /* The length of the data being sent. */
                                      0 );                    /* No flags. */

        configPRINTF( ( "FreeRTOS_send: %u/%u\n", ( unsigned ) lTransmitted, ( unsigned ) lStringLength ) );

        return lTransmitted;
    }

/*-----------------------------------------------------------*/

    static void prvEchoClientTask( void * pvParameters )
    {
        Socket_t xSocket;
        struct freertos_sockaddr xEchoServerAddress;
        int32_t lLoopCount = 0UL;
        const int32_t lMaxLoopCount = 1;
        volatile uint32_t ulTxCount = 0UL;
        BaseType_t xReceivedBytes, xReturned = 0, xInstance;
        BaseType_t lTransmitted;
        char * pcTransmittedString, * pcReceivedString;
        WinProperties_t xWinProps;
        TickType_t xTimeOnEntering;
        TickType_t uxDuration = 0;
        size_t xTotalSent = 0U;
        size_t xTotalRecv = 0U;
        BaseType_t xFamily = FREERTOS_AF_INET;

        /* Fill in the buffer and window sizes that will be used by the socket. */
        #ifdef _WINDOWS_
            xWinProps.lTxBufSize = 8 * ipconfigTCP_MSS;
            xWinProps.lTxWinSize = 5;
            xWinProps.lRxBufSize = 8 * ipconfigTCP_MSS;
            xWinProps.lRxWinSize = 5;
        #else
            xWinProps.lTxBufSize = 3 * ipconfigTCP_MSS;
            xWinProps.lTxWinSize = 2;
            xWinProps.lRxBufSize = 3 * ipconfigTCP_MSS;
            xWinProps.lRxWinSize = 2;
        #endif

        /* This task can be created a number of times.  Each instance is numbered
         * to enable each instance to use a different Rx and Tx buffer.  The number is
         * passed in as the task's parameter. */
        xInstance = ( BaseType_t ) pvParameters;

        /* Point to the buffers to be used by this instance of this task. */
        pcTransmittedString = &( cTxBuffers[ xInstance ][ 0 ] );
        pcReceivedString = &( cRxBuffers[ xInstance ][ 0 ] );

        memset( &xEchoServerAddress, 0, sizeof( xEchoServerAddress ) );

        /* Echo requests are sent to the echo server.  The address of the echo
         * server is configured by the constants configECHO_SERVER_ADDR0 to
         * configECHO_SERVER_ADDR3 in FreeRTOSConfig.h. */

        #ifdef configECHO_SERVER_ADDR_STRING
        {
            BaseType_t rc = FreeRTOS_inet_pton( FREERTOS_AF_INET6, configECHO_SERVER_ADDR_STRING, ( void * ) xEchoServerAddress.sin_address.xIP_IPv6.ucBytes );

            if( rc == pdPASS )
            {
                xFamily = FREERTOS_AF_INET6;
            }
            else
            {
                rc = FreeRTOS_inet_pton( FREERTOS_AF_INET4, configECHO_SERVER_ADDR_STRING, ( void * ) xEchoServerAddress.sin_address.xIP_IPv6.ucBytes );
                configASSERT( rc == pdPASS );
                xFamily = FREERTOS_AF_INET4;
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
            BaseType_t xResult;
            /* Create a TCP socket. */
            xSocket = FreeRTOS_socket( xFamily, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );
            configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

            /* Set a time out so a missing reply does not cause the task to block
             * indefinitely. */
            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

            /* Set the window and buffer sizes. */
            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_WIN_PROPERTIES, ( void * ) &xWinProps, sizeof( xWinProps ) );
            xTotalSent = 0U;
            xTotalRecv = 0U;

            /* Connect to the echo server. */
            xResult = FreeRTOS_connect( xSocket, &xEchoServerAddress, sizeof( xEchoServerAddress ) );
            configPRINTF( ( "FreeRTOS_connect returns %d\n", ( int ) xResult ) );

            if( xResult == 0 )
            {
                ulConnections[ xInstance ]++;

                /* Send a number of echo requests. */
                for( lLoopCount = 0; lLoopCount < lMaxLoopCount; lLoopCount++ )
                {
                    lTransmitted = vTCPCreateAndSendData( xSocket, pcTransmittedString, &ulTxCount, echoBUFFER_SIZES );

                    if( xIsFatalError( lTransmitted ) )
                    {
                        /* Error? */
                        break;
                    }

                    xTotalSent += lTransmitted;

                    /* Clear the buffer into which the echoed string will be
                     * placed. */
                    memset( ( void * ) pcReceivedString, 0x00, echoBUFFER_SIZES );
                    xReceivedBytes = 0;

                    /* Receive data echoed back to the socket. */
                    while( xReceivedBytes < lTransmitted )
                    {
                        #if USE_TCP_ZERO_COPY
                            uint8_t * pucZeroCopyRxBuffPtr = NULL;
                            xReturned = FreeRTOS_recv( xSocket,               /* The socket being received from. */
                                                       &pucZeroCopyRxBuffPtr, /* While using FREERTOS_ZERO_COPY flag, pvBuffer is taken as a double pointer which will be updated with pointer to TCP RX stream buffer. */
                                                       ipconfigTCP_MSS,       /* The size of the buffer provided to receive the data. */
                                                       FREERTOS_ZERO_COPY );  /* Use FREERTOS_ZERO_COPY flag to enable zero copy. */

                            if( pucZeroCopyRxBuffPtr != NULL )
                            {
                                memcpy( &( pcReceivedString[ xReceivedBytes ] ), pucZeroCopyRxBuffPtr, xReturned );

                                /* Release the memory that was previously obtained by calling FreeRTOS_recv()
                                 * with the flag 'FREERTOS_ZERO_COPY' */
                                FreeRTOS_ReleaseTCPPayloadBuffer( xSocket, pucZeroCopyRxBuffPtr, xReturned );
                            }
                        #else /* if USE_TCP_ZERO_COPY */
                            xReturned = FreeRTOS_recv( xSocket,                                 /* The socket being received from. */
                                                       &( pcReceivedString[ xReceivedBytes ] ), /* The buffer into which the received data will be written. */
                                                       lTransmitted - xReceivedBytes,           /* The size of the buffer provided to receive the data. */
                                                       0 );                                     /* No flags. */
                        #endif /* USE_TCP_ZERO_COPY */

                        if( xIsFatalError( xReturned ) )
                        {
                            /* Error occurred.  Latch it so it can be detected
                             * below. */
                            break;
                        }

                        if( xReturned == 0 )
                        {
                            /* Timed out. */
                            configPRINTF( ( "recv returned %u\n", ( unsigned ) xReturned ) );
                            break;
                        }

                        /* Keep a count of the bytes received so far. */
                        xReceivedBytes += xReturned;
                        xTotalRecv += xReturned;
                    }

                    /* If an error occurred it will be latched in xReceivedBytes,
                     * otherwise xReceived bytes will be just that - the number of
                     * bytes received from the echo server. */
                    if( xReceivedBytes > 0 )
                    {
                        /* Compare the transmitted string to the received string. */
                        configASSERT( strncmp( pcReceivedString, pcTransmittedString, lTransmitted ) == 0 );

                        if( strncmp( pcReceivedString, pcTransmittedString, lTransmitted ) == 0 )
                        {
                            /* The echo reply was received without error. */
                            ulTxRxCycles[ xInstance ]++;
                        }
                        else
                        {
                            /* The received string did not match the transmitted
                             * string. */
                            ulTxRxFailures[ xInstance ]++;
                            break;
                        }
                    }
                    else if( xIsFatalError( xReturned ) )
                    {
                        /* FreeRTOS_recv() returned an error. */
                        break;
                    }
                    else
                    {
                        /* Timed out without receiving anything? */
                        break;
                    }
                }

                /* Finished using the connected socket, initiate a graceful close:
                 * FIN, FIN+ACK, ACK. */
                FreeRTOS_shutdown( xSocket, FREERTOS_SHUT_RDWR );

                /* Expect FreeRTOS_recv() to return an error once the shutdown is
                 * complete. */
                xTimeOnEntering = xTaskGetTickCount();

                do
                {
                    xReturned = FreeRTOS_recv( xSocket,                    /* The socket being received from. */
                                               &( pcReceivedString[ 0 ] ), /* The buffer into which the received data will be written. */
                                               echoBUFFER_SIZES,           /* The size of the buffer provided to receive the data. */
                                               0 );

                    uxDuration = ( xTaskGetTickCount() - xTimeOnEntering );

                    if( xReturned < 0 )
                    {
                        break;
                    }
                } while( uxDuration < xReceiveTimeOut );
            }

            configPRINTF( ( "Instance[%u]: Good %u/%u shutdown %u\n",
                            ( unsigned ) xInstance,
                            ( unsigned ) ( ulTxRxCycles[ xInstance ] - ulTxRxFailures[ xInstance ] ),
                            ( unsigned ) ( ulTxRxCycles[ xInstance ] ),
                            ( unsigned ) uxDuration ) );
            configPRINTF( ( "%u x %u = %u Exchange %u/%u\n",
                            ( unsigned ) echoBUFFER_SIZE_MULTIPLIER,
                            ( unsigned ) echoBUFFER_SIZES,
                            ( unsigned ) ( echoBUFFER_SIZE_MULTIPLIER * echoBUFFER_SIZES ),
                            ( unsigned ) xTotalSent,
                            ( unsigned ) xTotalRecv ) );
            configPRINTF( ( "--------------------------------------\n\n" ) );

            /* Close this socket before looping back to create another. */
            FreeRTOS_closesocket( xSocket );

            /* Pause for a short while to ensure the network is not too
             * congested. */
            vTaskDelay( echoLOOP_DELAY );
        }
    }
/*-----------------------------------------------------------*/

    static BaseType_t prvCreateTxData( char * cBuffer,
                                       uint32_t ulBufferLength )
    {
        BaseType_t lCharactersToAdd, lCharacter;
        char cChar = '0';
        const BaseType_t lMinimumLength = 60;
        uint32_t ulRandomNumber;
        static uint32_t ulNextnumber = 1U;

        /* Randomise the number of characters that will be sent in the echo
         * request. */
        do
        {
            ( void ) xApplicationGetRandomNumber( &ulRandomNumber );
            lCharactersToAdd = ulRandomNumber % ( ulBufferLength - 20UL );
        } while( ( lCharactersToAdd == 0 ) || ( lCharactersToAdd < lMinimumLength ) ); /* Must be at least enough to add the unique text to the start of the string later. */

        /* Fill the buffer. */
        for( lCharacter = 0; lCharacter < lCharactersToAdd; lCharacter++ )
        {
            cBuffer[ lCharacter ] = cChar;
            cChar++;

            if( cChar > '~' )
            {
                cChar = '0';
            }
        }

        {
            /* Replace the string "0123456789" with an increasing number. */
            char pcBuf[ 16 ];
            char * pcPtr = cBuffer;
            const char * ucLast = &( cBuffer[ ulBufferLength ] );

            for( ; ; )
            {
                char * next = strchr( pcPtr, '0' );

                if( ( next == NULL ) || ( ( next + 10 ) >= ucLast ) )
                {
                    break;
                }

                snprintf( pcBuf, sizeof pcBuf, "%010u", ulNextnumber );
                memcpy( next, pcBuf, 10 );
                ulNextnumber++;
                pcPtr = next + 10;
            }
        }
        return lCharactersToAdd;
    }
/*-----------------------------------------------------------*/

    BaseType_t xAreSingleTaskTCPEchoClientsStillRunning( void )
    {
        static uint32_t ulLastEchoSocketCount[ echoNUM_ECHO_CLIENTS ] = { 0 }, ulLastConnections[ echoNUM_ECHO_CLIENTS ] = { 0 };
        BaseType_t xReturn = pdPASS, x;

        /* Return fail is the number of cycles does not increment between
         * consecutive calls. */
        for( x = 0; x < echoNUM_ECHO_CLIENTS; x++ )
        {
            if( ulTxRxCycles[ x ] == ulLastEchoSocketCount[ x ] )
            {
                xReturn = pdFAIL;
            }
            else
            {
                ulLastEchoSocketCount[ x ] = ulTxRxCycles[ x ];
            }

            if( ulConnections[ x ] == ulLastConnections[ x ] )
            {
                xReturn = pdFAIL;
            }
            else
            {
                ulConnections[ x ] = ulLastConnections[ x ];
            }
        }

        return xReturn;
    }

#endif /* ipconfigUSE_TCP */
