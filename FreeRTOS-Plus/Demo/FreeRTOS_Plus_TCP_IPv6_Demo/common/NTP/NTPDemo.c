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
 * NTPDemo.c
 *
 * An example of how to lookup a domain using DNS
 * And also how to send and receive UDP messages to get the NTP time
 *
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_Stream_Buffer.h"

/* Use the date & time functions from +FAT. */
#if ( USE_PLUS_FAT != 0 )
    #include "ff_time.h"
#endif /* ( USE_PLUS_FAT != 0 ) */

#include "NTPDemo.h"
#include "ntpClient.h"

#include "date_and_time.h"

#if ( ipconfigDNS_USE_CALLBACKS == 0 )
    #error ipconfigDNS_USE_CALLBACKS must be 1
#endif

#if ( ipconfigMULTI_INTERFACE == 0 )
    #ifndef ipSIZE_OF_IPv4_ADDRESS
        #define ipSIZE_OF_IPv4_ADDRESS    4
    #endif
    #define FREERTOS_AF_INET4             FREERTOS_AF_INET
#endif

/* Set time: sets the current time in seconds-after-1/1/1970
 * This function must be provided by the application. */

time_t get_time( time_t * puxTime );
int set_time( const time_t * t );

enum EStatus
{
    EStatusLookup,
    EStatusAsking,
    EStatusPause,
    EStatusFailed,
};

static struct SNtpPacket xNTPPacket;

BaseType_t xNTPHasTime;
uint32_t ulNTPTime;

#if ( ipconfigUSE_CALLBACKS == 0 )
    static char cRecvBuffer[ sizeof( struct SNtpPacket ) + 64 ];
#endif

static enum EStatus xStatus = EStatusLookup;

static const char * pcTimeServers[] =
{
    "0.asia.pool.ntp.org",
    "0.europe.pool.ntp.org",
    "0.id.pool.ntp.org",
    "0.south-america.pool.ntp.org",
    "0.oceania.pool.ntp.org",
    "0.north-america.pool.ntp.org"
};

static SemaphoreHandle_t xNTPWakeupSem = NULL;
static uint32_t ulIPAddressFound;

#if ( ipconfigUSE_IPv6 != 0 )
    static struct freertos_sockaddr xIPAddressFound;
#endif
static BaseType_t xHasIPAddress = pdFALSE;

static Socket_t xUDPSocket = NULL;
static TaskHandle_t xNTPTaskhandle = NULL;
static TickType_t uxSendTime;
static BaseType_t xPreferredHostType = FREERTOS_AF_INET4;
static BaseType_t xDNSAsynchronous = pdTRUE;
static BaseType_t xDNSLogging = pdFALSE;

static void prvNTPTask( void * pvParameters );

static void vSignalTask( void )
{
    #if ( ipconfigUSE_CALLBACKS == 0 )
        if( xUDPSocket != NULL )
        {
            /* Send a signal to the socket so that the
             *  FreeRTOS_recvfrom will get interrupted. */
            FreeRTOS_SignalSocket( xUDPSocket );
        }
        else
    #endif

    if( xNTPWakeupSem != NULL )
    {
        xSemaphoreGive( xNTPWakeupSem );
    }
}

void vNTPClearCache( void )
{
    ulIPAddressFound = 0U;
    #if ( ipconfigUSE_IPv6 != 0 )
    {
        memset( &( xIPAddressFound ), 0, sizeof xIPAddressFound );
    }
    #endif
    xHasIPAddress = pdFALSE;
}

void vNTPSetNTPType( BaseType_t aIPType,
                     BaseType_t xAsynchronous,
                     BaseType_t xLogging )
{
    switch( aIPType )
    {
        case 4:
            xPreferredHostType = FREERTOS_AF_INET4;
            break;

            #if ( ipconfigUSE_IPv6 != 0 )
                case 6:
                    xPreferredHostType = FREERTOS_AF_INET6;
                    break;
            #endif
        default:
            break;
    }

    xDNSAsynchronous = xAsynchronous;
    xDNSLogging = xLogging;
}

void vStartNTPTask( uint16_t usTaskStackSize,
                    UBaseType_t uxTaskPriority )
{
    /* The only public function in this module: start a task to contact
     * some NTP server. */

    if( xNTPTaskhandle != NULL )
    {
        switch( xStatus )
        {
            case EStatusPause:
                xStatus = EStatusAsking;
                vSignalTask();
                break;

            case EStatusLookup:
                FreeRTOS_printf( ( "NTP looking up server\n" ) );
                break;

            case EStatusAsking:
                FreeRTOS_printf( ( "NTP still asking\n" ) );
                break;

            case EStatusFailed:
                FreeRTOS_printf( ( "NTP failed somehow\n" ) );
                ulIPAddressFound = 0ul;
                xStatus = EStatusLookup;
                vSignalTask();
                break;
        }
    }
    else
    {
        xUDPSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

        if( xUDPSocket != NULL )
        {
            struct freertos_sockaddr xAddress;
            #if ( ipconfigUSE_CALLBACKS != 0 )
                BaseType_t xReceiveTimeOut = pdMS_TO_TICKS( 0 );
            #else
                BaseType_t xReceiveTimeOut = pdMS_TO_TICKS( 5000 );
            #endif

            xAddress.sin_address.ulIP_IPv4 = 0ul;
            xAddress.sin_port = FreeRTOS_htons( NTP_PORT );
            xAddress.sin_family = FREERTOS_AF_INET;

            FreeRTOS_bind( xUDPSocket, &xAddress, sizeof( xAddress ) );
            FreeRTOS_setsockopt( xUDPSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
            xTaskCreate( prvNTPTask,                    /* The function that implements the task. */
                         ( const char * ) "NTP client", /* Just a text name for the task to aid debugging. */
                         usTaskStackSize,               /* The stack size is defined in FreeRTOSIPConfig.h. */
                         NULL,                          /* The task parameter, not used in this case. */
                         uxTaskPriority,                /* The priority assigned to the task is defined in FreeRTOSConfig.h. */
                         &xNTPTaskhandle );             /* The task handle. */
        }
        else
        {
            FreeRTOS_printf( ( "Creating socket failed\n" ) );
        }
    }
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )
    static void vDNS_callback( const char * pcName,
                               void * pvSearchID,
                               struct freertos_addrinfo * pxAddress )
    {
        xStatus = EStatusAsking;

        ( void ) pvSearchID;
        ( void ) pcName;

        if( pxAddress == NULL )
        {
            FreeRTOS_printf( ( "DNS lookup timed out\n" ) );
        }
        else
        {
            if( pxAddress->ai_family == FREERTOS_AF_INET4 )
            {
                char pcBuf[ 16 ];
                uint32_t ulIPAddress;

                /* The DNS lookup has a result, or it has reached the time-out. */
                ulIPAddress = pxAddress->ai_addr->sin_address.ulIP_IPv4;
                FreeRTOS_inet_ntoa( ulIPAddress, pcBuf );
                FreeRTOS_printf( ( "vDNS_callback: IP address of %s found: %s\n", pcName, pcBuf ) );

                /*			if( ulIPAddressFound == 0U ) */
                /*			{ */
                /*				ulIPAddressFound = FreeRTOS_inet_addr_quick( 162, 159, 200, 1 ); */
                /*			} */
                if( ulIPAddressFound != 0U )
                {
                    memset( xIPAddressFound.sin_address.xIP_IPv6.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
                    xHasIPAddress = pdTRUE;
                }
            }
            else if( pxAddress->ai_family == FREERTOS_AF_INET6 )
            {
                /*  struct freertos_sockaddr * ai_addr */
                struct freertos_sockaddr * sockaddr6 = ( struct freertos_sockaddr * ) pxAddress->ai_addr;

                xIPAddressFound.sin_len = sizeof( xIPAddressFound ); /* Ignored, still present for backward compatibility. */
                xIPAddressFound.sin_family = FREERTOS_AF_INET6;      /* Set to FREERTOS_AF_INET6. */
                xIPAddressFound.sin_port = FreeRTOS_htons( NTP_PORT );
                xIPAddressFound.sin_flowinfo = 0;                    /* IPv6 flow information. */
                memcpy( xIPAddressFound.sin_address.xIP_IPv6.ucBytes, sockaddr6->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

                FreeRTOS_printf( ( "vDNS_callback: using address %pip\n", xIPAddressFound.sin_address.xIP_IPv6.ucBytes ) );
                ulIPAddressFound = 0U;
                xHasIPAddress = pdTRUE;
            }
        }

        vSignalTask();
    }
#else /* if ( ipconfigUSE_IPv6 != 0 ) */
    static void vDNS_callback( const char * pcName,
                               void * pvSearchID,
                               uint32_t ulIPAddress )
    {
        char pcBuf[ 16 ];

        /* The DNS lookup has a result, or it has reached the time-out. */
        FreeRTOS_inet_ntoa( ulIPAddress, pcBuf );
        FreeRTOS_printf( ( "IP address of %s found: %s\n", pcName, pcBuf ) );

        if( ulIPAddressFound == 0U )
        {
            ulIPAddressFound = ulIPAddress;
        }

        /* For testing: in case DNS doesn't respond, still try some NTP server
         * with a known IP-address. */
/*		if( ulIPAddressFound == 0U ) */
/*		{ */
/*			ulIPAddressFound = FreeRTOS_inet_addr_quick( 184, 105, 182, 7 ); */
/*			/ *		ulIPAddressFound = FreeRTOS_inet_addr_quick( 103, 242,  70, 4 );	* / */
/*		} */
        if( ulIPAddressFound != 0U )
        {
            xHasIPAddress = pdTRUE;
            xStatus = EStatusAsking;
        }

        vSignalTask();
    }
#endif /* if ( ipconfigUSE_IPv6 != 0 ) */
/*-----------------------------------------------------------*/

static void prvSwapFields( struct SNtpPacket * pxPacket )
{
    /* NTP messages are big-endian */
    pxPacket->rootDelay = FreeRTOS_htonl( pxPacket->rootDelay );
    pxPacket->rootDispersion = FreeRTOS_htonl( pxPacket->rootDispersion );

    pxPacket->referenceTimestamp.seconds = FreeRTOS_htonl( pxPacket->referenceTimestamp.seconds );
    pxPacket->referenceTimestamp.fraction = FreeRTOS_htonl( pxPacket->referenceTimestamp.fraction );

    pxPacket->originateTimestamp.seconds = FreeRTOS_htonl( pxPacket->originateTimestamp.seconds );
    pxPacket->originateTimestamp.fraction = FreeRTOS_htonl( pxPacket->originateTimestamp.fraction );

    pxPacket->receiveTimestamp.seconds = FreeRTOS_htonl( pxPacket->receiveTimestamp.seconds );
    pxPacket->receiveTimestamp.fraction = FreeRTOS_htonl( pxPacket->receiveTimestamp.fraction );

    pxPacket->transmitTimestamp.seconds = FreeRTOS_htonl( pxPacket->transmitTimestamp.seconds );
    pxPacket->transmitTimestamp.fraction = FreeRTOS_htonl( pxPacket->transmitTimestamp.fraction );
}
/*-----------------------------------------------------------*/

static void prvNTPPacketInit()
{
    memset( &xNTPPacket, '\0', sizeof( xNTPPacket ) );

    xNTPPacket.flags = 0xDB;                /* value 0xDB : mode 3 (client), version 3, leap indicator unknown 3 */
    xNTPPacket.poll = 10;                   /* 10 means 1 << 10 = 1024 seconds */
    xNTPPacket.precision = 0xFA;            /* = 250 = 0.015625 seconds */
    xNTPPacket.rootDelay = 0x5D2E;          /* 0x5D2E = 23854 or (23854/65535)= 0.3640 sec */
    xNTPPacket.rootDispersion = 0x0008CAC8; /* 0x0008CAC8 = 8.7912  seconds */

    /* use the recorded NTP time */
    time_t uxSecs = get_time( NULL );               /* apTime may be NULL, returns seconds */

    xNTPPacket.referenceTimestamp.seconds = uxSecs; /* Current time */
    xNTPPacket.transmitTimestamp.seconds = uxSecs + 3;

    /* Transform the contents of the fields from native to big endian. */
    prvSwapFields( &xNTPPacket );
}
/*-----------------------------------------------------------*/

static void prvReadTime( struct SNtpPacket * pxPacket )
{
    #if ( USE_PLUS_FAT != 0 )
        FF_TimeStruct_t xTimeStruct;
    #else
        struct tm xTimeStruct;
    #endif

    time_t uxPreviousSeconds;
    time_t uxPreviousMS;

    time_t uxCurrentSeconds;
    time_t uxCurrentMS;

    const char * pcTimeUnit;
    int32_t ilDiff;
    TickType_t uxTravelTime;

    uxTravelTime = xTaskGetTickCount() - uxSendTime;

    /* Transform the contents of the fields from big to native endian. */
    prvSwapFields( pxPacket );

    uxCurrentSeconds = pxPacket->receiveTimestamp.seconds - TIME1970;
    uxCurrentMS = pxPacket->receiveTimestamp.fraction / 4294967;
    uxCurrentSeconds += uxCurrentMS / 1000;
    uxCurrentMS = uxCurrentMS % 1000;

    /* Get the last time recorded */
    uxPreviousSeconds = FreeRTOS_get_secs_msec( &uxPreviousMS );

    /* Set the new time with precision in msec. * / */
    FreeRTOS_set_secs_msec( &uxCurrentSeconds, &uxCurrentMS );

    if( uxCurrentSeconds >= uxPreviousSeconds )
    {
        ilDiff = ( int32_t ) ( uxCurrentSeconds - uxPreviousSeconds );
    }
    else
    {
        ilDiff = 0 - ( int32_t ) ( uxPreviousSeconds - uxCurrentSeconds );
    }

    if( ( ilDiff < -5 ) || ( ilDiff > 5 ) )
    {
        /* More than 5 seconds difference. */
        pcTimeUnit = "sec";
    }
    else
    {
        /* Less than or equal to 5 second difference. */
        pcTimeUnit = "ms";
        uint32_t ulLowest = ( uxCurrentSeconds <= uxPreviousSeconds ) ? uxCurrentSeconds : uxPreviousSeconds;
        int32_t iCurMS = 1000 * ( uxCurrentSeconds - ulLowest ) + uxCurrentMS;
        int32_t iPrevMS = 1000 * ( uxPreviousSeconds - ulLowest ) + uxPreviousMS;
        ilDiff = iCurMS - iPrevMS;
    }

    /*uxCurrentSeconds -= iTimeZone; */

    #if ( USE_PLUS_FAT != 0 )
        FreeRTOS_gmtime_r( &uxCurrentSeconds, &xTimeStruct );
    #else
        extern struct tm * gmtime_r( const time_t * pxTime,
                                     struct tm * tmStruct );
        gmtime_r( &uxCurrentSeconds, &xTimeStruct );
    #endif /* ( USE_PLUS_FAT != 0 ) */

    /*
     *  378.067 [NTP client] NTP time: 9/11/2015 16:11:19.559 Diff -20 ms (289 ms)
     *  379.441 [NTP client] NTP time: 9/11/2015 16:11:20.933 Diff 0 ms (263 ms)
     */
    /* NTP time: -858993460/-858993459/-858991560 -858993460:-858993460:-858993460.158 Diff 1607503255 sec (60 ms) */
    FreeRTOS_printf( ( "NTP time: %u/%u/%02u %2u:%02u:%02u.%03u Diff %d %s (%lu ms)\n",
                       ( unsigned ) xTimeStruct.tm_mday,
                       ( unsigned ) xTimeStruct.tm_mon + 1,
                       ( unsigned ) xTimeStruct.tm_year + 1900,
                       ( unsigned ) xTimeStruct.tm_hour,
                       ( unsigned ) xTimeStruct.tm_min,
                       ( unsigned ) xTimeStruct.tm_sec,
                       ( unsigned ) uxCurrentMS,
                       ( signed ) ilDiff,
                       pcTimeUnit,
                       uxTravelTime ) );

    xNTPHasTime = pdTRUE;
    ulNTPTime = uxCurrentSeconds;
    set_time( &uxCurrentSeconds );

    /* Remove compiler warnings in case FreeRTOS_printf() is not used. */
    ( void ) pcTimeUnit;
    ( void ) uxTravelTime;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_CALLBACKS != 0 )

    static BaseType_t xOnUDPReceive( Socket_t xSocket,
                                     void * pvData,
                                     size_t xLength,
                                     const struct freertos_sockaddr * pxFrom,
                                     const struct freertos_sockaddr * pxDest )
    {
        ( void ) xSocket;
        ( void ) pxFrom;
        ( void ) pxDest;

        if( xLength >= sizeof( xNTPPacket ) )
        {
            prvReadTime( ( struct SNtpPacket * ) pvData );

            if( xStatus != EStatusPause )
            {
                xStatus = EStatusPause;
            }
        }

        vSignalTask();
        /* Tell the driver not to store the RX data */
        return 1;
    }
    /*-----------------------------------------------------------*/

#endif /* ipconfigUSE_CALLBACKS != 0 */

static void prvNTPTask( void * pvParameters )
{
    BaseType_t xServerIndex = 3;
    struct freertos_sockaddr xAddress;

    #if ( ipconfigUSE_CALLBACKS != 0 )
        F_TCP_UDP_Handler_t xHandler;
    #endif /* ipconfigUSE_CALLBACKS != 0 */

    ( void ) pvParameters;

    xStatus = EStatusLookup;
    #if ( ipconfigSOCKET_HAS_USER_SEMAPHORE != 0 ) || ( ipconfigUSE_CALLBACKS != 0 )
    {
        xNTPWakeupSem = xSemaphoreCreateBinary();
    }
    #endif

    #if ( ipconfigUSE_CALLBACKS != 0 )
    {
        memset( &xHandler, '\0', sizeof( xHandler ) );
        xHandler.pxOnUDPReceive = xOnUDPReceive;
        FreeRTOS_setsockopt( xUDPSocket, 0, FREERTOS_SO_UDP_RECV_HANDLER, ( void * ) &xHandler, sizeof( xHandler ) );
    }
    #endif
    #if ( ipconfigSOCKET_HAS_USER_SEMAPHORE != 0 )
    {
        FreeRTOS_setsockopt( xUDPSocket, 0, FREERTOS_SO_SET_SEMAPHORE, ( void * ) &xNTPWakeupSem, sizeof( xNTPWakeupSem ) );
    }
    #endif

    for( ; ; )
    {
        switch( xStatus )
        {
            case EStatusLookup:

                if( xHasIPAddress == 0 )
                {
                    char pcServerName[ 64 ];

                    if( ++xServerIndex == sizeof( pcTimeServers ) / sizeof( pcTimeServers[ 0 ] ) )
                    {
                        xServerIndex = 0;
                    }

                    snprintf( pcServerName, sizeof pcServerName, "%s", pcTimeServers[ xServerIndex ] );

                    if( ( pcServerName[ 0 ] == '0' ) && ( xPreferredHostType == FREERTOS_AF_INET6 ) )
                    {
                        pcServerName[ 0 ] = '2';
                    }

                    FreeRTOS_printf( ( "Looking up server '%s' IPv%c\n",
                                       pcServerName,
                                       ( xPreferredHostType == FREERTOS_AF_INET4 ) ? '4' : '6' ) );
                    #if ( ipconfigMULTI_INTERFACE != 0 )
                        struct freertos_addrinfo xHints;
                        struct freertos_addrinfo * pxResults = NULL;

                        memset( &( xHints ), 0, sizeof xHints );
                        xHints.ai_family = xPreferredHostType;

                        if( xDNSAsynchronous != 0 )
                        {
                            FreeRTOS_getaddrinfo_a( pcServerName,    /* The name of the node or device */
                                                    NULL,            /* Ignored for now. */
                                                    &( xHints ),     /* If not NULL: preferences. */
                                                    &( pxResults ),  /* An allocated struct, containing the results. */
                                                    vDNS_callback,
                                                    ( void * ) NULL, /* An object or a reference. */
                                                    pdMS_TO_TICKS( 2500U ) );
                        }
                        else
                        {
                            FreeRTOS_getaddrinfo( pcServerName,     /* The name of the node or device */
                                                  NULL,             /* Ignored for now. */
                                                  &( xHints ),      /* If not NULL: preferences. */
                                                  &( pxResults ) ); /* An allocated struct, containing the results. */

                            if( pxResults != NULL )
                            {
                                vDNS_callback( pcServerName, NULL, pxResults );
                            }
                        }
                    #else /* if ( ipconfigMULTI_INTERFACE != 0 ) */
                        FreeRTOS_gethostbyname_a( pcServerName, vDNS_callback, ( void * ) NULL, 1200 );
                    #endif /* if ( ipconfigMULTI_INTERFACE != 0 ) */
                }
                else
                {
                    xStatus = EStatusAsking;
                }

                break;

            case EStatusAsking:
                prvNTPPacketInit();
                uxSendTime = xTaskGetTickCount();
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( memcmp( xIPAddressFound.sin_address.xIP_IPv6.ucBytes, FreeRTOS_in6addr_any.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) != 0 )
                    {
                        FreeRTOS_printf( ( "Sending UDP message to %pip:%u\n",
                                           xIPAddressFound.sin_address.xIP_IPv6.ucBytes,
                                           FreeRTOS_ntohs( xIPAddressFound.sin_port ) ) );

                        FreeRTOS_sendto( xUDPSocket,
                                         ( void * ) &xNTPPacket, sizeof( xNTPPacket ),
                                         0,
                                         ( const struct freertos_sockaddr * ) &( xIPAddressFound ),
                                         sizeof( xIPAddressFound ) );
                    }
                    else
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                {
                    xAddress.sin_address.ulIP_IPv4 = ulIPAddressFound;
                    xAddress.sin_port = FreeRTOS_htons( NTP_PORT );
                    xAddress.sin_family = FREERTOS_AF_INET;

                    FreeRTOS_printf( ( "Sending UDP message to %lxip:%u\n",
                                       FreeRTOS_ntohl( ulIPAddressFound ),
                                       FreeRTOS_ntohs( xAddress.sin_port ) ) );

                    FreeRTOS_sendto( xUDPSocket,
                                     ( void * ) &xNTPPacket,
                                     sizeof( xNTPPacket ),
                                     0, &( xAddress ),
                                     sizeof( xAddress ) );
                }

                break;

            case EStatusPause:
                break;

            case EStatusFailed:
                break;
        }

        #if ( ipconfigUSE_CALLBACKS != 0 )
        {
            xSemaphoreTake( xNTPWakeupSem, 5000 );
        }
        #else
        {
            uint32_t xAddressSize;
            BaseType_t xReturned;

            xAddressSize = sizeof( xAddress );
            xReturned = FreeRTOS_recvfrom( xUDPSocket, ( void * ) cRecvBuffer, sizeof( cRecvBuffer ), 0, &xAddress, &xAddressSize );

            switch( xReturned )
            {
                case 0:
                case -pdFREERTOS_ERRNO_EAGAIN:
                case -pdFREERTOS_ERRNO_EINTR:
                    break;

                default:

                    if( xReturned < sizeof( xNTPPacket ) )
                    {
                        FreeRTOS_printf( ( "FreeRTOS_recvfrom: returns %ld\n", xReturned ) );
                    }
                    else
                    {
                        prvReadTime( ( struct SNtpPacket * ) cRecvBuffer );

                        if( xStatus != EStatusPause )
                        {
                            xStatus = EStatusPause;
                        }
                    }

                    break;
            }
        }
        #endif /* if ( ipconfigUSE_CALLBACKS != 0 ) */
    }
}
/*-----------------------------------------------------------*/
