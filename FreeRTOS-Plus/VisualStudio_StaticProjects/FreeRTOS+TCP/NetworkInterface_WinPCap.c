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

#include <stdlib.h>

/* WinPCap includes. */
#define HAVE_REMOTE
#include "pcap.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )
    #include "FreeRTOS_Routing.h"
#endif

/* Thread-safe circular buffers are being used to pass data to and from the PCAP
 * access functions. */
#include "Win32-Extensions.h"
#include "FreeRTOS_Stream_Buffer.h"

/* Sizes of the thread safe circular buffers used to pass data to and from the
 * WinPCAP Windows threads. */
#define xSEND_BUFFER_SIZE    32768
#define xRECV_BUFFER_SIZE    32768

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* Used to insert test code only. */
#define niDISRUPT_PACKETS    0

/*-----------------------------------------------------------*/

/*
 * Windows threads that are outside of the control of the FreeRTOS simulator are
 * used to interface with the WinPCAP libraries.
 */
DWORD WINAPI prvWinPcapRecvThread( void * pvParam );
DWORD WINAPI prvWinPcapSendThread( void * pvParam );

/*
 * Print out a numbered list of network interfaces that are available on the
 * host computer.
 */
static pcap_if_t * prvPrintAvailableNetworkInterfaces( void );

/*
 * Open the network interface.  The number of the interface to be opened is set
 * by the configNETWORK_INTERFACE_TO_USE constant in FreeRTOSConfig.h.
 */
static void prvOpenSelectedNetworkInterface( pcap_if_t * pxAllNetworkInterfaces );
static int prvOpenInterface( const char * pucName );

/*
 * Configure the capture filter to allow blocking reads, and to filter out
 * packets that are not of interest to this demo.
 */
static void prvConfigureCaptureBehaviour( void );

/*
 * A function that simulates Ethernet interrupts by periodically polling the
 * WinPCap interface for new data.
 */
static void prvInterruptSimulatorTask( void * pvParameters );

/*
 * Create the buffers that are used to pass data between the FreeRTOS simulator
 * and the Win32 threads that manage WinPCAP.
 */
static void prvCreateThreadSafeBuffers( void );

/*
 * This function is equivalent to uxStreamBufferAdd from
 * FreeRTOS_Stream_Buffer.c in the case that the stream buffer is being used
 * as a normal circular buffer (i.e. only the tail and head pointers are
 * needed). Thus, this function does not take the offset argument, and does not
 * update the front pointer of the stream buffer. This allows the removal of
 * the calls to vTaskSuspendAll and xTaskResumeAll, as the head and front
 * pointer no longer need to be atomically updated, allowing this function to be
 * safely used by a Windows thread.
 */
static size_t prvStreamBufferAdd( StreamBuffer_t * pxBuffer,
                                  const uint8_t * pucData,
                                  size_t uxByteCount );

/*
 * Utility function used to format print messages only.
 */
static const char * prvRemoveSpaces( char * pcBuffer,
                                     int aBuflen,
                                     const char * pcMessage );

/*-----------------------------------------------------------*/

/* Required by the WinPCap library. */
static char cErrorBuffer[ PCAP_ERRBUF_SIZE ];

/* An event used to wake up the Win32 thread that sends data through the WinPCAP
 * library. */
static void * pvSendEvent = NULL;

/* _HT_ made the PCAP interface number configurable through the program's
 * parameters in order to test in different machines. */
static BaseType_t xConfigNetworkInterfaceToUse = configNETWORK_INTERFACE_TO_USE;

/* Handles to the Windows threads that handle the PCAP IO. */
static HANDLE vWinPcapRecvThreadHandle = NULL;
static HANDLE vWinPcapSendThreadHandle = NULL;

/* The interface being used by WinPCap. */
static pcap_t * pxOpenedInterfaceHandle = NULL;

/* Circular buffers used by the PCAP Win32 threads. */
static StreamBuffer_t * xSendBuffer = NULL;
static StreamBuffer_t * xRecvBuffer = NULL;

/* Logs the number of WinPCAP send failures, for viewing in the debugger only. */
static volatile uint32_t ulWinPCAPSendFailures = 0;

#if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )
/*
 * A pointer to the network interface is needed later when receiving packets.
 */
    static NetworkInterface_t * pxMyInterface;

    extern NetworkEndPoint_t * pxGetEndpoint( BaseType_t xIPType );

    static BaseType_t xWinPcap_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
    static BaseType_t xWinPcap_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                       NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                       BaseType_t bReleaseAfterSend );
    static BaseType_t xWinPcap_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

    NetworkInterface_t * pxWinPcap_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                            NetworkInterface_t * pxInterface );
#endif

/*-----------------------------------------------------------*/

#if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )
    static BaseType_t xWinPcap_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
#else
    BaseType_t xNetworkInterfaceInitialise( void )
#endif
{
    BaseType_t xReturn = pdFALSE;
    pcap_if_t * pxAllNetworkInterfaces;

    /* Query the computer the simulation is being executed on to find the
     * network interfaces it has installed. */
    pxAllNetworkInterfaces = prvPrintAvailableNetworkInterfaces();

    /* Open the network interface.  The number of the interface to be opened is
     * set by the configNETWORK_INTERFACE_TO_USE constant in FreeRTOSConfig.h.
     * Calling this function will set the pxOpenedInterfaceHandle variable.  If,
     * after calling this function, pxOpenedInterfaceHandle is equal to NULL, then
     * the interface could not be opened. */
    if( pxAllNetworkInterfaces != NULL )
    {
        prvOpenSelectedNetworkInterface( pxAllNetworkInterfaces );
    }

    if( pxOpenedInterfaceHandle != NULL )
    {
        xReturn = pdPASS;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static void prvCreateThreadSafeBuffers( void )
{
    /* The buffer used to pass data to be transmitted from a FreeRTOS task to
     * the Win32 thread that sends via the WinPCAP library. */
    if( xSendBuffer == NULL )
    {
        xSendBuffer = ( StreamBuffer_t * ) malloc( sizeof( *xSendBuffer ) - sizeof( xSendBuffer->ucArray ) + xSEND_BUFFER_SIZE + 1 );
        configASSERT( xSendBuffer );
        memset( xSendBuffer, '\0', sizeof( *xSendBuffer ) - sizeof( xSendBuffer->ucArray ) );
        xSendBuffer->LENGTH = xSEND_BUFFER_SIZE + 1;
    }

    /* The buffer used to pass received data from the Win32 thread that receives
     * via the WinPCAP library to the FreeRTOS task. */
    if( xRecvBuffer == NULL )
    {
        xRecvBuffer = ( StreamBuffer_t * ) malloc( sizeof( *xRecvBuffer ) - sizeof( xRecvBuffer->ucArray ) + xRECV_BUFFER_SIZE + 1 );
        configASSERT( xRecvBuffer );
        memset( xRecvBuffer, '\0', sizeof( *xRecvBuffer ) - sizeof( xRecvBuffer->ucArray ) );
        xRecvBuffer->LENGTH = xRECV_BUFFER_SIZE + 1;
    }
}

/*-----------------------------------------------------------*/

static size_t prvStreamBufferAdd( StreamBuffer_t * pxBuffer,
                                  const uint8_t * pucData,
                                  size_t uxByteCount )
{
    size_t uxSpace, uxNextHead, uxFirst;
    size_t uxCount = uxByteCount;

    uxSpace = uxStreamBufferGetSpace( pxBuffer );

    /* The number of bytes that can be written is the minimum of the number of
     * bytes requested and the number available. */
    uxCount = FreeRTOS_min_size_t( uxSpace, uxCount );

    if( uxCount != 0U )
    {
        uxNextHead = pxBuffer->uxHead;

        if( pucData != NULL )
        {
            /* Calculate the number of bytes that can be added in the first
            * write - which may be less than the total number of bytes that need
            * to be added if the buffer will wrap back to the beginning. */
            uxFirst = FreeRTOS_min_size_t( pxBuffer->LENGTH - uxNextHead, uxCount );

            /* Write as many bytes as can be written in the first write. */
            ( void ) memcpy( &( pxBuffer->ucArray[ uxNextHead ] ), pucData, uxFirst );

            /* If the number of bytes written was less than the number that
             * could be written in the first write... */
            if( uxCount > uxFirst )
            {
                /* ...then write the remaining bytes to the start of the
                 * buffer. */
                ( void ) memcpy( pxBuffer->ucArray, &( pucData[ uxFirst ] ), uxCount - uxFirst );
            }
        }

        uxNextHead += uxCount;

        if( uxNextHead >= pxBuffer->LENGTH )
        {
            uxNextHead -= pxBuffer->LENGTH;
        }

        pxBuffer->uxHead = uxNextHead;
    }

    return uxCount;
}

/*-----------------------------------------------------------*/

#if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )
    static BaseType_t xWinPcap_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                       NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                       BaseType_t bReleaseAfterSend )
#else
    BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                        BaseType_t bReleaseAfterSend )
#endif
{
    size_t xSpace;

    iptraceNETWORK_INTERFACE_TRANSMIT();
    configASSERT( xIsCallingFromIPTask() == pdTRUE );

    /* Both the length of the data being sent and the actual data being sent
     *  are placed in the thread safe buffer used to pass data between the FreeRTOS
     *  tasks and the Win32 thread that sends data via the WinPCAP library.  Drop
     *  the packet if there is insufficient space in the buffer to hold both. */
    xSpace = uxStreamBufferGetSpace( xSendBuffer );

    if( ( pxNetworkBuffer->xDataLength <= ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ) ) &&
        ( xSpace >= ( pxNetworkBuffer->xDataLength + sizeof( pxNetworkBuffer->xDataLength ) ) ) )
    {
        /* First write in the length of the data, then write in the data
         * itself. */
        uxStreamBufferAdd( xSendBuffer, 0, ( const uint8_t * ) &( pxNetworkBuffer->xDataLength ), sizeof( pxNetworkBuffer->xDataLength ) );
        uxStreamBufferAdd( xSendBuffer, 0, ( const uint8_t * ) pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );
    }
    else
    {
        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: send buffers full to store %lu\n", pxNetworkBuffer->xDataLength ) );
    }

    /* Kick the Tx task in either case in case it doesn't know the buffer is
     * full. */
    SetEvent( pvSendEvent );

    /* The buffer has been sent so can be released. */
    if( bReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return pdPASS;
}
/*-----------------------------------------------------------*/

#if defined( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )

    static BaseType_t xWinPcap_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
    {
        BaseType_t xResult = pdFALSE;

        ( void ) pxInterface;

        if( pxOpenedInterfaceHandle != NULL )
        {
            xResult = pdTRUE;
        }

        return xResult;
    }

    /*-----------------------------------------------------------*/

    NetworkInterface_t * pxWinPcap_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                            NetworkInterface_t * pxInterface )
    {
        static char pcName[ 17 ];

        /* This function pxWinPcap_FillInterfaceDescriptor() adds a network-interface.
         * Make sure that the object pointed to by 'pxInterface'
         * is declared static or global, and that it will continue to exist. */

        pxMyInterface = pxInterface;

        snprintf( pcName, sizeof( pcName ), "eth%ld", xEMACIndex );

        memset( pxInterface, '\0', sizeof( *pxInterface ) );
        pxInterface->pcName = pcName;                    /* Just for logging, debugging. */
        pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has only meaning for the driver functions. */
        pxInterface->pfInitialise = xWinPcap_NetworkInterfaceInitialise;
        pxInterface->pfOutput = xWinPcap_NetworkInterfaceOutput;
        pxInterface->pfGetPhyLinkStatus = xWinPcap_GetPhyLinkStatus;

        FreeRTOS_AddNetworkInterface( pxInterface );

        return pxInterface;
    }
#endif
/*-----------------------------------------------------------*/

static pcap_if_t * prvPrintAvailableNetworkInterfaces( void )
{
    pcap_if_t * pxAllNetworkInterfaces = NULL, * xInterface;
    int32_t lInterfaceNumber = 1;
    char cBuffer[ 512 ];
    static BaseType_t xInvalidInterfaceDetected = pdFALSE;

    if( xInvalidInterfaceDetected == pdFALSE )
    {
        if( pcap_findalldevs_ex( PCAP_SRC_IF_STRING, NULL, &pxAllNetworkInterfaces, cErrorBuffer ) == -1 )
        {
            printf( "Could not obtain a list of network interfaces\n%s\n", cErrorBuffer );
            pxAllNetworkInterfaces = NULL;
        }
        else
        {
            printf( "\r\n\r\nThe following network interfaces are available:\r\n\r\n" );
        }

        if( pxAllNetworkInterfaces != NULL )
        {
            /* Print out the list of network interfaces.  The first in the list
             * is interface '1', not interface '0'. */
            for( xInterface = pxAllNetworkInterfaces; xInterface != NULL; xInterface = xInterface->next )
            {
                /* The descriptions of the devices can be full of spaces, clean them
                 * a little.  printf() can only be used here because the network is not
                 * up yet - so no other network tasks will be running. */
                printf( "Interface %d - %s\n", lInterfaceNumber, prvRemoveSpaces( cBuffer, sizeof( cBuffer ), xInterface->name ) );
                printf( "              (%s)\n", prvRemoveSpaces( cBuffer, sizeof( cBuffer ), xInterface->description ? xInterface->description : "No description" ) );
                printf( "\n" );
                lInterfaceNumber++;
            }
        }

        if( lInterfaceNumber == 1 )
        {
            /* The interface number was never incremented, so the above for() loop
             * did not execute meaning no interfaces were found. */
            printf( " \nNo network interfaces were found.\n" );
            pxAllNetworkInterfaces = NULL;
        }

        printf( "\r\nThe interface that will be opened is set by " );
        printf( "\"configNETWORK_INTERFACE_TO_USE\", which\r\nshould be defined in FreeRTOSConfig.h\r\n" );

        if( ( xConfigNetworkInterfaceToUse < 1L ) || ( xConfigNetworkInterfaceToUse >= lInterfaceNumber ) )
        {
            printf( "\r\nERROR:  configNETWORK_INTERFACE_TO_USE is set to %d, which is an invalid value.\r\n", xConfigNetworkInterfaceToUse );
            printf( "Please set configNETWORK_INTERFACE_TO_USE to one of the interface numbers listed above,\r\n" );
            printf( "then re-compile and re-start the application.  Only Ethernet (as opposed to WiFi)\r\n" );
            printf( "interfaces are supported.\r\n\r\nHALTING\r\n\r\n\r\n" );
            xInvalidInterfaceDetected = pdTRUE;

            if( pxAllNetworkInterfaces != NULL )
            {
                /* Free the device list, as no devices are going to be opened. */
                pcap_freealldevs( pxAllNetworkInterfaces );
                pxAllNetworkInterfaces = NULL;
            }
        }
        else
        {
            printf( "Attempting to open interface number %d.\n", xConfigNetworkInterfaceToUse );
        }
    }

    return pxAllNetworkInterfaces;
}
/*-----------------------------------------------------------*/

static int prvOpenInterface( const char * pucName )
{
    static char pucInterfaceName[ 256 ];

    if( pucName != NULL )
    {
        strncpy( pucInterfaceName, pucName, sizeof( pucInterfaceName ) );
    }

    pxOpenedInterfaceHandle = pcap_open( pucInterfaceName,            /* The name of the selected interface. */
                                         ipTOTAL_ETHERNET_FRAME_SIZE, /* The size of the packet to capture. */
                                         PCAP_OPENFLAG_PROMISCUOUS,   /* Open in promiscuous mode as the MAC and
                                                                       * IP address is going to be "simulated", and
                                                                       * not be the real MAC and IP address.  This allows
                                                                       * traffic to the simulated IP address to be routed
                                                                       * to uIP, and traffic to the real IP address to be
                                                                       * routed to the Windows TCP/IP stack. */
                                         100,
                                         NULL,                        /* No authentication is required as this is
                                                                       * not a remote capture session. */
                                         cErrorBuffer
                                         );

    if( pxOpenedInterfaceHandle == NULL )
    {
        printf( "\n%s is not supported by WinPcap and cannot be opened\n", pucInterfaceName );
        return 1;
    }
    else
    {
        /* Configure the capture filter to allow blocking reads, and to filter
         * out packets that are not of interest to this demo. */
        prvConfigureCaptureBehaviour();
    }

    return 0;
}
/*-----------------------------------------------------------*/

static void prvOpenSelectedNetworkInterface( pcap_if_t * pxAllNetworkInterfaces )
{
    pcap_if_t * pxInterface;
    int32_t x;

    /* Walk the list of devices until the selected device is located. */
    pxInterface = pxAllNetworkInterfaces;

    for( x = 0L; x < ( xConfigNetworkInterfaceToUse - 1L ); x++ )
    {
        pxInterface = pxInterface->next;
    }

    /* Open the selected interface. */
    if( prvOpenInterface( pxInterface->name ) == 0 )
    {
        printf( "Successfully opened interface number %d.\n", x + 1 );
    }
    else
    {
        printf( "Failed to open interface number %d.\n", x + 1 );
    }

    /* The device list is no longer required. */
    pcap_freealldevs( pxAllNetworkInterfaces );
}
/*-----------------------------------------------------------*/

static void prvConfigureCaptureBehaviour( void )
{
    struct bpf_program xFilterCode;
    uint32_t ulNetMask;

    /* Set up a filter so only the packets of interest are passed to the IP
     * stack.  cErrorBuffer is used for convenience to create the string.  Don't
     * confuse this with an error message. */
    sprintf( cErrorBuffer, "broadcast or multicast or ether host %x:%x:%x:%x:%x:%x",
             ipLOCAL_MAC_ADDRESS[ 0 ], ipLOCAL_MAC_ADDRESS[ 1 ], ipLOCAL_MAC_ADDRESS[ 2 ], ipLOCAL_MAC_ADDRESS[ 3 ], ipLOCAL_MAC_ADDRESS[ 4 ], ipLOCAL_MAC_ADDRESS[ 5 ] );

    ulNetMask = ( configNET_MASK3 << 24UL ) | ( configNET_MASK2 << 16UL ) | ( configNET_MASK1 << 8L ) | configNET_MASK0;

    if( pcap_compile( pxOpenedInterfaceHandle, &xFilterCode, cErrorBuffer, 1, ulNetMask ) < 0 )
    {
        printf( "\nThe packet filter string is invalid\n" );
    }
    else
    {
        if( pcap_setfilter( pxOpenedInterfaceHandle, &xFilterCode ) < 0 )
        {
            printf( "\nAn error occurred setting the packet filter.\n" );
        }

        /* When pcap_compile() succeeds, it allocates memory for the memory pointed to by the bpf_program struct
         * parameter.pcap_freecode() will free that memory. */
        pcap_freecode( &xFilterCode );
    }

    /* Create the buffers used to pass packets between the FreeRTOS simulator
     * and the Win32 threads that are handling WinPCAP. */
    prvCreateThreadSafeBuffers();

    if( pvSendEvent == NULL )
    {
        /* Create event used to signal the Win32 WinPCAP Tx thread. */
        pvSendEvent = CreateEvent( NULL, FALSE, TRUE, NULL );

        /* Create the Win32 thread that handles WinPCAP Rx. */
        vWinPcapRecvThreadHandle = CreateThread(
            NULL,                 /* Pointer to thread security attributes. */
            0,                    /* Initial thread stack size, in bytes. */
            prvWinPcapRecvThread, /* Pointer to thread function. */
            NULL,                 /* Argument for new thread. */
            0,                    /* Creation flags. */
            NULL );

        /* Use the cores that are not used by the FreeRTOS tasks. */
        SetThreadAffinityMask( vWinPcapRecvThreadHandle, ~0x01u );

        /* Create the Win32 thread that handlers WinPCAP Tx. */
        vWinPcapSendThreadHandle = CreateThread(
            NULL,                 /* Pointer to thread security attributes. */
            0,                    /* initial thread stack size, in bytes. */
            prvWinPcapSendThread, /* Pointer to thread function. */
            NULL,                 /* Argument for new thread. */
            0,                    /* Creation flags. */
            NULL );

        /* Use the cores that are not used by the FreeRTOS tasks. */
        SetThreadAffinityMask( vWinPcapSendThreadHandle, ~0x01u );

        /* Create a task that simulates an interrupt in a real system.  This will
         * block waiting for packets, then send a message to the IP task when data
         * is available. */
        xTaskCreate( prvInterruptSimulatorTask, "MAC_ISR", configMINIMAL_STACK_SIZE, NULL, configMAC_ISR_SIMULATOR_PRIORITY, NULL );
    }
}
/*-----------------------------------------------------------*/

/* WinPCAP function. */
void pcap_callback( u_char * user,
                    const struct pcap_pkthdr * pkt_header,
                    const u_char * pkt_data )
{
    ( void ) user;

    /* THIS IS CALLED FROM A WINDOWS THREAD - DO NOT ATTEMPT ANY FREERTOS CALLS
     * OR TO PRINT OUT MESSAGES HERE. */

    /* Pass data to the FreeRTOS simulator on a thread safe circular buffer. */
    if( ( pkt_header->caplen <= ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ) ) &&
        ( uxStreamBufferGetSpace( xRecvBuffer ) >= ( ( ( size_t ) pkt_header->caplen ) + sizeof( *pkt_header ) ) ) )
    {
        /* The received packets will be written to a C source file,
         * only if 'ipconfigUSE_DUMP_PACKETS' is defined.
         * Otherwise, there is no action. */
        iptraceDUMP_PACKET( ( const uint8_t * ) pkt_data, ( size_t ) pkt_header->caplen, pdTRUE );

        /* NOTE. The prvStreamBufferAdd function is used here in place of
         * uxStreamBufferAdd since the uxStreamBufferAdd call will suspend
         * the FreeRTOS scheduler to atomically update the head and front
         * of the stream buffer. Since xRecvBuffer is being used as a regular
         * circular buffer (i.e. only the head and tail are needed), this call
         * only updates the head of the buffer, removing the need to suspend
         * the scheduler, and allowing this function to be safely called from
         * a Windows thread. */
        prvStreamBufferAdd( xRecvBuffer, ( const uint8_t * ) pkt_header, sizeof( *pkt_header ) );
        prvStreamBufferAdd( xRecvBuffer, ( const uint8_t * ) pkt_data, ( size_t ) pkt_header->caplen );
    }
}
/*-----------------------------------------------------------*/

DWORD WINAPI prvWinPcapRecvThread( void * pvParam )
{
    ( void ) pvParam;

    /* THIS IS A WINDOWS THREAD - DO NOT ATTEMPT ANY FREERTOS CALLS	OR TO PRINT
     * OUT MESSAGES HERE. */

    for( ; ; )
    {
        pcap_dispatch( pxOpenedInterfaceHandle, 1, pcap_callback, ( u_char * ) "mydata" );
    }
}
/*-----------------------------------------------------------*/

DWORD WINAPI prvWinPcapSendThread( void * pvParam )
{
    size_t xLength;
    uint8_t ucBuffer[ ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ];
    static char cErrorMessage[ 1024 ];
    const DWORD xMaxMSToWait = 1000;

    /* THIS IS A WINDOWS THREAD - DO NOT ATTEMPT ANY FREERTOS CALLS	OR TO PRINT
     * OUT MESSAGES HERE. */

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParam;

    for( ; ; )
    {
        /* Wait until notified of something to send. */
        WaitForSingleObject( pvSendEvent, xMaxMSToWait );

        /* Is there more than the length value stored in the circular buffer
         * used to pass data from the FreeRTOS simulator into this Win32 thread? */
        while( uxStreamBufferGetSize( xSendBuffer ) > sizeof( xLength ) )
        {
            uxStreamBufferGet( xSendBuffer, 0, ( uint8_t * ) &xLength, sizeof( xLength ), pdFALSE );
            uxStreamBufferGet( xSendBuffer, 0, ( uint8_t * ) ucBuffer, xLength, pdFALSE );

            /* The packets sent will be written to a C source file,
             * only if 'ipconfigUSE_DUMP_PACKETS' is defined.
             * Otherwise, there is no action. */
            iptraceDUMP_PACKET( ucBuffer, xLength, pdFALSE );

            if( pcap_sendpacket( pxOpenedInterfaceHandle, ucBuffer, xLength ) != 0 )
            {
                ulWinPCAPSendFailures++;
            }
        }
    }
}
/*-----------------------------------------------------------*/

#if defined  ( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )

    static BaseType_t xPacketBouncedBack( const uint8_t * pucBuffer )
    {
        static BaseType_t xHasWarned = pdFALSE;
        EthernetHeader_t * pxEtherHeader;
        NetworkEndPoint_t * pxEndPoint;
        BaseType_t xResult = pdFALSE;

        pxEtherHeader = ( EthernetHeader_t * ) pucBuffer;

        /* Sometimes, packets are bounced back by the driver and we need not process them. Check
         * whether this packet is one such packet. */
        for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            if( memcmp( pxEndPoint->xMACAddress.ucBytes, pxEtherHeader->xSourceAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
            {
                if( xHasWarned == pdFALSE )
                {
                    xHasWarned = pdTRUE;
                    FreeRTOS_printf( ( "Bounced back by WinPCAP interface: %02x:%02x:%02x:%02x:%02x:%02x\n",
                                        pxEndPoint->xMACAddress.ucBytes[ 0 ],
                                        pxEndPoint->xMACAddress.ucBytes[ 1 ],
                                        pxEndPoint->xMACAddress.ucBytes[ 2 ],
                                        pxEndPoint->xMACAddress.ucBytes[ 3 ],
                                        pxEndPoint->xMACAddress.ucBytes[ 4 ],
                                        pxEndPoint->xMACAddress.ucBytes[ 5 ] ) );
                }

                xResult = pdTRUE;
                break;
            }
        }

        return xResult;
    }

#else

    static BaseType_t xPacketBouncedBack( const uint8_t * pucBuffer )
    {
        EthernetHeader_t * pxEtherHeader;
        BaseType_t xResult = pdFALSE;

        pxEtherHeader = ( EthernetHeader_t * ) pucBuffer;

        /* Sometimes, packets are bounced back by the driver and we need not process them. Check
        * whether this packet is one such packet. */
        if( memcmp( ipLOCAL_MAC_ADDRESS, pxEtherHeader->xSourceAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
        {
            xResult = pdTRUE;
        }
        else
        {
            xResult = pdFALSE;
        }

        return xResult;
    }

#endif
/*-----------------------------------------------------------*/

static void prvInterruptSimulatorTask( void * pvParameters )
{
    struct pcap_pkthdr xHeader;
    static struct pcap_pkthdr * pxHeader;
    const uint8_t * pucPacketData;
    uint8_t ucRecvBuffer[ ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ];
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    eFrameProcessingResult_t eResult;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    for( ; ; )
    {
        /* Does the circular buffer used to pass data from the Win32 thread that
         * handles WinPCAP Rx into the FreeRTOS simulator contain another packet? */
        if( uxStreamBufferGetSize( xRecvBuffer ) > sizeof( xHeader ) )
        {
            /* Get the next packet. */
            uxStreamBufferGet( xRecvBuffer, 0, ( uint8_t * ) &xHeader, sizeof( xHeader ), pdFALSE );
            uxStreamBufferGet( xRecvBuffer, 0, ( uint8_t * ) ucRecvBuffer, ( size_t ) xHeader.len, pdFALSE );
            pucPacketData = ucRecvBuffer;
            pxHeader = &xHeader;

            iptraceNETWORK_INTERFACE_RECEIVE();

            /* Check for minimal size. */
            if( pxHeader->len >= sizeof( EthernetHeader_t ) )
            {
                eResult = ipCONSIDER_FRAME_FOR_PROCESSING( pucPacketData );
            }
            else
            {
                eResult = eReleaseBuffer;
            }

            if( eResult == eProcessBuffer )
            {
                /* Will the data fit into the frame buffer? */
                if( pxHeader->len <= ipTOTAL_ETHERNET_FRAME_SIZE )
                {
                    /* Obtain a buffer into which the data can be placed.  This
                     * is only	an interrupt simulator, not a real interrupt, so it
                     * is ok to call the task level function here, but note that
                     * some buffer implementations cannot be called from a real
                     * interrupt. */
                    if( xPacketBouncedBack( pucPacketData ) == pdFALSE )
                    {
                        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( pxHeader->len, 0 );
                    }
                    else
                    {
                        pxNetworkBuffer = NULL;
                    }

                    if( pxNetworkBuffer != NULL )
                    {
                        memcpy( pxNetworkBuffer->pucEthernetBuffer, pucPacketData, pxHeader->len );
                        pxNetworkBuffer->xDataLength = ( size_t ) pxHeader->len;

                        #if ( niDISRUPT_PACKETS == 1 )
                            {
                                pxNetworkBuffer = vRxFaultInjection( pxNetworkBuffer, pucPacketData );
                            }
                        #endif /* niDISRUPT_PACKETS */

                        if( pxNetworkBuffer != NULL )
                        {
                            xRxEvent.pvData = ( void * ) pxNetworkBuffer;
                        #if defined ( FREERTOS_PLUS_TCP_VERSION ) && ( FREERTOS_PLUS_TCP_VERSION >= 10 )
                            pxNetworkBuffer->pxInterface = pxMyInterface;
                            pxNetworkBuffer->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pxNetworkBuffer->pucEthernetBuffer );

                            {
                                char pcDescription[ 129 ] = "unknown";
                                const EthernetHeader_t * pxEthernetHeader = ( ( const EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );
                                uint8_t ucType = ipTYPE_IPv4;

                                switch( pxEthernetHeader->usFrameType )
                                {
                                    case ipARP_FRAME_TYPE:
                                       {
                                           const ProtocolPacket_t * pxPacket = ( ( const ProtocolPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
                                           snprintf( pcDescription, sizeof pcDescription, "ARP frame for %xip",
                                                     FreeRTOS_ntohl( pxPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress ) );
                                       }
                                       break;

                                    case ipPROTOCOL_ICMP:
                                        snprintf( pcDescription, sizeof pcDescription, "ICMP frame" );
                                        break;

                                    case ipIPv4_FRAME_TYPE:
                                       {
                                           const IPPacket_t * pxIPPacket;
                                           uint8_t ucProtocol;
                                           pxIPPacket = ( const IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
                                           ucProtocol = pxIPPacket->xIPHeader.ucProtocol;

                                           if( ucProtocol == ( uint8_t ) ipPROTOCOL_TCP )
                                           {
                                               const ProtocolHeaders_t * pxProtocolHeaders = ( ( const ProtocolHeaders_t * )
                                                                                               &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizePacket( pxNetworkBuffer ) ] ) );
                                               uint32_t ulLocalIP, ulRemoteIP;
                                               uint16_t usLocalPort = FreeRTOS_htons( pxProtocolHeaders->xTCPHeader.usDestinationPort );
                                               uint16_t usRemotePort = FreeRTOS_htons( pxProtocolHeaders->xTCPHeader.usSourcePort );
                                               const IPHeader_t * pxIPHeader;
                                               pxIPHeader = ( ( const IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
                                               ulLocalIP = FreeRTOS_htonl( pxIPHeader->ulDestinationIPAddress );
                                               ulRemoteIP = FreeRTOS_htonl( pxIPHeader->ulSourceIPAddress );

                                               snprintf( pcDescription, sizeof pcDescription, "TCP v4 packet %xip port%u to %xip: port %u",
                                                         ulRemoteIP, usRemotePort, ulLocalIP, usLocalPort );
                                           }
                                           else if( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
                                           {
                                               snprintf( pcDescription, sizeof pcDescription, "UDP v4 packet" );
                                               const UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

                                               if( pxUDPPacket->xIPHeader.ulSourceIPAddress == 0x642c6276U )
                                               {
                                                   FreeRTOS_printf( ( "Received UDP packet from %xip\n",
                                                                      ( unsigned ) ( FreeRTOS_htonl( pxUDPPacket->xIPHeader.ulSourceIPAddress ) ) ) );
                                               }
                                           }
                                           else
                                           {
                                               snprintf( pcDescription, sizeof pcDescription, "v4 packet protocol %02X", ucProtocol );
                                           }
                                       }
                                       break;

                                    case ipIPv6_FRAME_TYPE:
                                       {
                                           const IPHeader_IPv6_t * pxIPHeader_IPv6;
                                           uint8_t ucProtocol;

                                           ucType = ipTYPE_IPv6;
                                           pxIPHeader_IPv6 = ( const IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );

                                           ucProtocol = pxIPHeader_IPv6->ucNextHeader;

                                           if( ucProtocol == ( uint8_t ) ipPROTOCOL_TCP )
                                           {
                                               snprintf( pcDescription, sizeof pcDescription, "TCP v6 packet" );
                                           }
                                           else if( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
                                           {
                                               snprintf( pcDescription, sizeof pcDescription, "UDP v6 packet" );
                                           }
                                           else if( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP_IPv6 )
                                           {
                                               snprintf( pcDescription, sizeof pcDescription, "ICMP v6 packet" );
                                           }
                                           else
                                           {
                                               snprintf( pcDescription, sizeof pcDescription, "v6 packet protocol %02X", ucProtocol );
                                           }
                                       }
                                       break;

                                    default:
                                        snprintf( pcDescription, sizeof pcDescription, "Unknown frame %04x", pxEthernetHeader->usFrameType );
                                        break;
                                }

                                if( pxNetworkBuffer->pxEndPoint == NULL )
                                {
                                    pxNetworkBuffer->pxEndPoint = pxGetEndpoint( ucType );

                                    if( strncasecmp( "ARP", pcDescription, 3 ) != 0 )
                                    {
                                        FreeRTOS_printf( ( "No end-point for \"%s\". Using 0x%p type IPv%d\n",
                                                           pcDescription,
                                                           pxNetworkBuffer->pxEndPoint,
                                                           ucType == ipTYPE_IPv6 ? 6 : 4 ) );
                                    }
                                }
                            }
                        #endif

                            /* Data was received and stored.  Send a message to
                             * the IP task to let it know. */
                            if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
                            {
                                /* The buffer could not be sent to the stack so
                                 * must be released again.  This is only an
                                 * interrupt simulator, not a real interrupt, so it
                                 * is ok to use the task level function here, but
                                 * note no all buffer implementations will allow
                                 * this function to be executed from a real
                                 * interrupt. */
                                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                                iptraceETHERNET_RX_EVENT_LOST();
                            }
                        }
                        else
                        {
                            /* The packet was already released or stored inside
                             * vRxFaultInjection().  Don't release it here. */
                        }
                    }
                    else
                    {
                        iptraceETHERNET_RX_EVENT_LOST();
                    }
                }
                else
                {
                    /* Log that a packet was dropped because it would have
                     * overflowed the buffer, but there may be more buffers to
                     * process. */
                }
            }
        }
        else
        {
            /* There is no real way of simulating an interrupt.  Make sure
             * other tasks can run. */
            vTaskDelay( configWINDOWS_MAC_INTERRUPT_SIMULATOR_DELAY );
        }
    }
}
/*-----------------------------------------------------------*/

static const char * prvRemoveSpaces( char * pcBuffer,
                                     int aBuflen,
                                     const char * pcMessage )
{
    char * pcTarget = pcBuffer;

    /* Utility function used to format messages being printed only. */
    while( ( *pcMessage != 0 ) && ( pcTarget < ( pcBuffer + aBuflen - 1 ) ) )
    {
        *( pcTarget++ ) = *pcMessage;

        if( isspace( *pcMessage ) != pdFALSE )
        {
            while( isspace( *pcMessage ) != pdFALSE )
            {
                pcMessage++;
            }
        }
        else
        {
            pcMessage++;
        }
    }

    *pcTarget = '\0';

    return pcBuffer;
}
/*-----------------------------------------------------------*/

#define BUFFER_SIZE               ( ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING )
#define BUFFER_SIZE_ROUNDED_UP    ( ( BUFFER_SIZE + 7 ) & ~0x07UL )

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t * pucNetworkPacketBuffers = NULL;
    size_t uxIndex;

    if( pucNetworkPacketBuffers == NULL )
    {
        pucNetworkPacketBuffers = ( uint8_t * ) malloc( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * BUFFER_SIZE_ROUNDED_UP );
    }

    if( pucNetworkPacketBuffers == NULL )
    {
        FreeRTOS_printf( ( "Failed to allocate memory for pxNetworkBuffers" ) );
        configASSERT( 0 );
    }
    else
    {
        for( uxIndex = 0; uxIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; uxIndex++ )
        {
            size_t uxOffset = uxIndex * BUFFER_SIZE_ROUNDED_UP;
            NetworkBufferDescriptor_t ** ppDescriptor;

            /* At the beginning of each pbuff is a pointer to the relevant descriptor */
            ppDescriptor = ( NetworkBufferDescriptor_t ** ) &( pucNetworkPacketBuffers[ uxOffset ] );

            /* Set this pointer to the address of the correct descriptor */
            *ppDescriptor = &( pxNetworkBuffers[ uxIndex ] );

            /* pucEthernetBuffer is set to point ipBUFFER_PADDING bytes in from the
             * beginning of the allocated buffer. */
            pxNetworkBuffers[ uxIndex ].pucEthernetBuffer = &( pucNetworkPacketBuffers[ uxOffset + ipBUFFER_PADDING ] );
        }
    }
}
/*-----------------------------------------------------------*/
