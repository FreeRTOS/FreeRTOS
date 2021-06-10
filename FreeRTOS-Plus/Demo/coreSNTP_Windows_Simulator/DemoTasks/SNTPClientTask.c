/*
 * FreeRTOS V202104.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * This file is part of the demo project that shows use of the coreSNTP library to create
 * an SNTP client (daemon) task for synchronizing system time with internet time and
 * maintaining Coordinated Universal Time (UTC) (or wall-clock time) in the system.
 *
 * This file contains the SNTP client (daemon) task as well as functionality for
 * maintaining wall-clock or UTC time in RAM. The SNTP client periodically synchronizes
 * system clock with an SNTP/NTP servers. Any other task running an application in the
 * system can query the system time. For an example of an application task querying time
 * from the system, refer to the SampleAppTask.c file in this project.
 *
 * !!! NOTE !!!
 * This SNTP demo does not authenticate the server nor the client.
 * Hence, this demo should not be used as production ready code.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <time.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo include. */
#include "common_demo_include.h"

/* SNTP library include. */
#include "core_sntp_client.h"

/* Synchronization primitive include. */
#include "semphr.h"

/* FreeRTOS+TCP includes */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"

/*-----------------------------------------------------------*/

/* Compile time error for undefined configs. */

#ifndef democonfigLIST_OF_TIME_SERVERS
    #error "Define the democonfigLIST_OF_TIME_SERVERS config by following the instructions in demo_config.h file."
#endif

#ifndef democonfigDESIRED_CLOCK_ACCURACY_MS
    #error "Define the democonfigDESIRED_CLOCK_ACCURACY_MS config by following instructions in demo_config.h file."
#endif

#ifndef democonfigSYSTEM_CLOCK_TOLERANCE_PPM
    #error "Define the democonfigSYSTEM_CLOCK_TOLERANCE_PPM config by following instructions in demo_config.h file."
#endif

#ifndef democonfigSYSTEM_START_YEAR
    #error "Define the democonfigSYSTEM_START_YEAR config by following instructions in demo_config.h file."
#endif

/*-----------------------------------------------------------*/
/* Default values for configuration . */

#ifndef democonfigSERVER_RESPONSE_TIMEOUT_MS
    #define democonfigSERVER_RESPONSE_TIMEOUT_MS    ( 5000 )
#endif

/**
 * @brief The size for network buffer that is allocated for initializing the coreSNTP library in the
 * demo.
 *
 * @note The size of the buffer MUST be large enough to hold an entire SNTP packet, which includes the standard SNTP
 * packet data of 48 bytes and authentication data for security mechanism, if used, in communication with time server.
 */
#define SNTP_CONTEXT_NETWORK_BUFFER_SIZE    ( SNTP_PACKET_BASE_SIZE )

/**
 * @brief The constant for storing the number of milliseconds per FreeRTOS tick in the system.
 * @note This value represents the time duration per tick from the perspective of the
 * of Windows Simulator based FreeRTOS system that carries lagging clock drift in relation to
 * internet time or UTC time. Thus, the actual time duration value per tick of the system will be
 * larger from the perspective of internet time.
 */
#define MILLISECONDS_PER_TICK               ( 1000 / configTICK_RATE_HZ )

/*-----------------------------------------------------------*/

/**
 * @brief The definition of the @ref NetworkContext_t structure for the demo.
 * The structure wraps a FreeRTOS+TCP socket that is used for UDP communication
 * with time servers.
 *
 * @note The context is used in the @ref UdpTransportInterface_t interface required
 * by the coreSNTP library.
 *
 */
struct NetworkContext
{
    Socket_t socket;
};

/**
 * @brief Structure aggregating state variables for RAM-based wall-clock time
 * in Coordinated Universal Time (UTC) for system.
 *
 * @note This demo uses the following mathematical model to represent current
 * time in RAM.
 *
 *  BaseTime = Time set at boot or the last synchronized time
 *  Slew Rate = Number of seconds to adjust per system time second
 *  No. of ticks since last SNTP sync = Current FreeRTOS Tick Count -
 *                                      Tick count at last SNTP sync
 *
 *  Time Elapsed since last SNTP sync = No. of ticks since last SNTP sync
 *                                                    x
 *                                      Number of milliseconds per FreeRTOS tick
 *
 *  Slew Adjustment = Slew Rate x Time Elapsed since last SNTP sync
 *
 *  Current Time = Base Time +
 *                 Time Elapsed since last SNTP sync +
 *                 Slew Adjustment
 */
typedef struct SystemClock
{
    UTCTime_t baseTime;
    TickType_t lastSyncTickCount;
    uint32_t pollPeriod;
    uint32_t slewRate; /* Seconds/Seconds */
    bool firstTimeSyncDone;
} SystemClock_t;

/**
 * @brief Shared global system clock object for representing UTC/wall-clock
 * time in system.
 */
static SystemClock_t systemClock;

/**
 * @brief Mutex for protecting access to the shared memory of the
 * system clock parameters.
 */
static SemaphoreHandle_t xMutex = NULL;
static StaticSemaphore_t xSemaphoreMutex;

/*-----------------------------------------------------------*/

/**
 * @brief Utility function to convert the passed year to UNIX time representation
 * of seconds since 1st Jan 1970 00h:00m:00s seconds to 1st Jan 00h:00m:00s of the
 * the passed year.
 *
 * This utility does account for leap years.
 *
 * @param[in] The year to translate.
 */
static uint32_t translateYearToUnixSeconds( uint16_t year );

/**
 * @brief Calculates the current time in the system.
 * It calculates the current time as:
 *
 *   BaseTime = Time set at device boot or the last synchronized time
 *   SlewRate = Number of seconds to adjust per system time second
 *
 *   Current Time = Base Time +
 *                  Time since last SNTP Synchronization +
 *                  Slew Adjustment (if slew rate > 0) for time period since
 *                  last SNTP synchronization
 *
 * @param[in] pBaseTime The base time in the system clock parameters.
 * @param[in] lastSyncTickCount The tick count at the last time synchronization
 * with a time server.
 * @param[in] slewRate The slew rate as seconds of clock adjustment per FreeRTOS
 * system time second.
 * @param[out] pCurrentTime This will be populated with the calculated current
 * UTC time in the system.
 */
static void calculateCurrentTime( UTCTime_t * pBaseTime,
                                  TickType_t lastSyncTickCount,
                                  uint32_t slewRate,
                                  UTCTime_t * pCurrentTime );

/**
 * @brief Initializes the SNTP context for the SNTP client task.
 * This function generates an array of the configured time servers, creates a FreeRTOS UDP socket
 * for the UDP transport interface and initializes the passed SNTP context by calling the
 * Sntp_Init() API of the coreSNTP library.
 *
 * @param[in, out] pContext The memory for the SNTP client context that will be initialized with
 * Sntp_Init API.
 * @param[in] pTimeServers The list of time servers configured through the democonfigLIST_OF_TIME_SERVERS
 * macro in demo_config.h.
 * @param[in] numOfServers The number of time servers configured in democonfigLIST_OF_TIME_SERVERS.
 * @param[in] pContextBuffer The allocated network buffer that will be initialized in the SNTP context.
 * @param[in] pUdpContext The memory for the network context for the UDP transport interface that will
 * be passed to the SNTP client context. This will be filled with a UDP context created by this function.
 *
 * @return Returns `true` if initialization of SNTP client context is successful; otherwise `false`.
 */
static bool initializeSntpClient( SntpContext_t * pContext,
                                  const char ** pTimeServers,
                                  size_t numOfServers,
                                  uint8_t * pContextBuffer,
                                  size_t contextBufferSize,
                                  NetworkContext_t * pUdpContext );

/**
 * @brief The demo implementation of the @ref SntpResolveDns_t interface to
 * allow the coreSNTP library to resolve DNS name of a time server being
 * used for requesting time from.
 *
 * @param[in] pTimeServer The time-server whose IPv4 address is to be resolved.
 * @param[out] pIpV4Addr This is filled with the resolved IPv4 address of
 * @p pTimeServer.
 */
static bool resolveDns( const SntpServerInfo_t * pServerAddr,
                        uint32_t * pIpV4Addr );

/**
 * @brief The demo implementation of the @ref UdpTransportSendTo_t function
 * of the UDP transport interface to allow the coreSNTP library to perform
 * network operation of sending time request over UDP to the provided time server.
 *
 * @param[in] pNetworkContext This will be the NetworkContext_t context object
 * representing the FreeRTOS UDP socket to use for network send operation.
 * @param[in] serverAddr The IPv4 address of the time server.
 * @param[in] serverPort The port of the server to send data to.
 * @param[in] pBuffer The demo-supplied network buffer of size, SNTP_CONTEXT_NETWORK_BUFFER_SIZE,
 * containing the data to send over the network.
 * @param[in] bytesToSend The size of data in @p pBuffer to send.
 *
 * @return Returns the return code of FreeRTOS UDP send API, FreeRTOS_sendto, which returns
 * 0 for error or timeout OR the number of bytes sent over the network.
 */
static int32_t UdpTransport_Send( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  const void * pBuffer,
                                  size_t bytesToSend );

/**
 * @brief The demo implementation of the @ref UdpTransportRecvFrom_t function
 * of the UDP transport interface to allow the coreSNTP library to perform
 * network operation of reading expected time response over UDP from
 * provided time server.
 *
 * @param[in] pNetworkContext This will be the NetworkContext_t context object
 * representing the FreeRTOS UDP socket to use for network read operation.
 * @param[in] pTimeServer The IPv4 address of the time server to receive data from.
 * @param[in] serverPort The port of the server to receive data from.
 * @param[out] pBuffer The demo-supplied network buffer of size, SNTP_CONTEXT_NETWORK_BUFFER_SIZE,
 * that will be filled with data received from the network.
 * @param[in] bytesToRecv The expected number of bytes to receive from the network
 * for the server response server.
 *
 * @return Returns one of the following:
 * - 0 for timeout in receiving any data from the network (by translating the
 * -pdFREERTOS_ERRNO_EWOULDBLOCK return code from FreeRTOS_recvfrom API )
 *                         OR
 * - The number of bytes read from the network.
 */
static int32_t UdpTransport_Recv( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  void * pBuffer,
                                  size_t bytesToRecv );

/**
 * @brief The demo implementation of the @ref SntpGetTime_t interface
 * for obtaining system clock time for the coreSNTP library.
 *
 * @param[out] pTime This will be populated with the current time from
 * the system.
 */
static void sntpClient_GetTime( SntpTimestamp_t * pCurrentTime );

/**
 * @brief The demo implementation of the @ref SntpSetTime_t interface
 * for correcting the system clock time based on the  time received
 * from the server response and the clock-offset value calculated by
 * the coreSNTP library.
 *
 * @note This demo uses either the "slew" OR "step" methodology of system
 * clock correction based on the use-case:
 * 1. "Step" correction is used if:
 *   - System time is ahead of server time so that system time is immediately
 *     corrected instead of potentially receding back in time with a "slew"
 *     correction approach.
 *                                      OR
 *   - It is the first time synchronization for the system since boot-up. Using
 *     "step" approach immediately corrects the system if it is far away from the
 *     server time on device startup instead of slowly correcting over time with
 *     the "slew" approach.
 *
 * 2. The "slew" correction approach is used for all cases other than the above
 *    as they represent regular time synchronization during device runtime where
 *    the system time may have drifted behind the server time, and can be corrected
 *    gradually over the SNTP client's polling interval period.
 *
 * @note The above system clock correction algorithm is just one example of a correction
 * approach. It can be modified to suit your application needs. Examples include:
 * - Always using "slew" correction if the device is always within a small time offset from
 *   server and your application is sensitive to non-abrupt changes in time (that could occur
 *   with "step" approach) for use-cases like logging events in correct order
 * - Always using a "step" approach for a simplicity if your application is not sensitive to
 *   abrupt changes/progress in time.
 */
static void sntpClient_SetTime( const SntpServerInfo_t * pTimeServer,
                                const SntpTimestamp_t * pServerTime,
                                int32_t clockOffsetSec,
                                SntpLeapSecondInfo_t leapSecondInfo );


/*------------------------------------------------------------------------------*/

static uint32_t translateYearToUnixSeconds( uint16_t year )
{
    configASSERT( year >= 1970 );

    uint32_t numOfDaysSince1970 = ( year - 1970 ) * 365;

    /* Calculate the extra days in leap years (for February 29) over the time
    * period from 1st Jan 1970 to 1st Jan of the passed year.
    * By subtracting from the year 1969, the extra day in 1972 is covered. */
    numOfDaysSince1970 += ( ( year - 1969 ) / 4 );

    return( numOfDaysSince1970 * 24 * 3600 );
}

void calculateCurrentTime( UTCTime_t * pBaseTime,
                           TickType_t lastSyncTickCount,
                           uint32_t slewRate,
                           UTCTime_t * pCurrentTime )
{
    uint64_t msElapsedSinceLastSync = 0;
    TickType_t ticksElapsedSinceLastSync = xTaskGetTickCount() - lastSyncTickCount;

    /* Calculate time elapsed since last synchronization according to the number
     * of system ticks passed. */
    msElapsedSinceLastSync = ticksElapsedSinceLastSync * MILLISECONDS_PER_TICK;

    /* If slew rate is set, then apply the slew-based clock adjustment for the elapsed time. */
    if( slewRate > 0 )
    {
        msElapsedSinceLastSync += ( uint64_t ) slewRate * msElapsedSinceLastSync;
    }

    /* Set the current UTC time in the output parameter. */
    if( msElapsedSinceLastSync >= 1000 )
    {
        pCurrentTime->secs = pBaseTime->secs + msElapsedSinceLastSync / 1000;
        pCurrentTime->msecs = msElapsedSinceLastSync % 1000;
    }
    else
    {
        pCurrentTime->secs = pBaseTime->secs;
        pCurrentTime->msecs = msElapsedSinceLastSync;
    }
}

/********************** DNS Resolution Interface *******************************/
static bool resolveDns( const SntpServerInfo_t * pServerAddr,
                        uint32_t * pIpV4Addr )
{
    uint32_t resolvedAddr = 0;
    bool status = false;

    resolvedAddr = FreeRTOS_gethostbyname( pServerAddr->pServerName );

    /* Set the output parameter if DNS look up succeeded. */
    if( resolvedAddr != 0 )
    {
        /* DNS Look up succeeded. */
        status = true;

        *pIpV4Addr = resolvedAddr;

        #if defined( LIBRARY_LOG_LEVEL ) && ( LIBRARY_LOG_LEVEL != LOG_NONE )
            uint8_t stringAddr[ 16 ];
            FreeRTOS_inet_ntoa( resolvedAddr, stringAddr );
            LogInfo( ( "Resolved time server as %s", stringAddr ) );
        #endif
    }

    return status;
}

/********************** UDP Interface definition *******************************/
int32_t UdpTransport_Send( NetworkContext_t * pNetworkContext,
                           uint32_t serverAddr,
                           uint16_t serverPort,
                           const void * pBuffer,
                           size_t bytesToSend )
{
    struct freertos_sockaddr destinationAddress;
    int32_t bytesSent;

    destinationAddress.sin_addr = serverAddr;
    destinationAddress.sin_port = FreeRTOS_htons( serverPort );

    /* Send the buffer with ulFlags set to 0, so the FREERTOS_ZERO_COPY bit
     * is clear. */
    bytesSent = FreeRTOS_sendto( /* The socket being send to. */
        pNetworkContext->socket,
        /* The data being sent. */
        pBuffer,
        /* The length of the data being sent. */
        bytesToSend,
        /* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
        0,
        /* Where the data is being sent. */
        &destinationAddress,
        /* Not used but should be set as shown. */
        sizeof( destinationAddress )
        );

    return bytesSent;
}

static int32_t UdpTransport_Recv( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  void * pBuffer,
                                  size_t bytesToRecv )
{
    struct freertos_sockaddr sourceAddress;
    int32_t bytesReceived;
    socklen_t addressLength = sizeof( struct freertos_sockaddr );

    /* Receive into the buffer with ulFlags set to 0, so the FREERTOS_ZERO_COPY bit
     * is clear. */
    bytesReceived = FreeRTOS_recvfrom( /* The socket data is being received on. */
        pNetworkContext->socket,

        /* The buffer into which received data will be
         * copied. */
        pBuffer,

        /* The length of the buffer into which data will be
         * copied. */
        bytesToRecv,
        /* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
        0,
        /* Will get set to the source of the received data. */
        &sourceAddress,
        /* Not used but should be set as shown. */
        &addressLength
        );

    /* If data is received from the network, discard the data if  received from a different source than
     * the server. */
    if( ( bytesReceived > 0 ) && ( ( sourceAddress.sin_addr != serverAddr ) ||
                                   ( FreeRTOS_ntohs( sourceAddress.sin_port ) != serverPort ) ) )
    {
        bytesReceived = 0;

        #if defined( LIBRARY_LOG_LEVEL ) && ( LIBRARY_LOG_LEVEL != LOG_NONE )
            /* Convert the IP address of the sender's address to string for logging. */
            char stringAddr[ 16 ];
            FreeRTOS_inet_ntoa( sourceAddress.sin_addr, stringAddr );

            /* Log about reception of packet from unexpected sender. */
            LogWarn( ( "Received UDP packet from unexpected source: Addr=%s Port=%u",
                       stringAddr, FreeRTOS_ntohs( sourceAddress.sin_port ) ) );
        #endif
    }

    /* Translate the return code of timeout to the UDP transport interface expected
     * code to indicate read retry. */
    else if( bytesReceived == -pdFREERTOS_ERRNO_EWOULDBLOCK )
    {
        bytesReceived = 0;
    }

    return bytesReceived;
}


/**************************** Time Interfaces ************************************************/
static void sntpClient_GetTime( SntpTimestamp_t * pCurrentTime )
{
    UTCTime_t currentTime;
    uint64_t ntpSecs;

    /* Obtain mutex for accessing system clock variables */
    xSemaphoreTake( xMutex, portMAX_DELAY );

    calculateCurrentTime( &systemClock.baseTime,
                          systemClock.lastSyncTickCount,
                          systemClock.slewRate,
                          &currentTime );

    /* Release mutex. */
    xSemaphoreGive( xMutex );

    /* Convert UTC time from UNIX timescale to SNTP timestamp format. */
    ntpSecs = currentTime.secs + SNTP_TIME_AT_UNIX_EPOCH_SECS;

    /* Support case of SNTP timestamp rollover on 7 February 2036 when
     * converting from UNIX time to SNTP timestamp. */
    if( ntpSecs > UINT32_MAX )
    {
        /* Subtract an extra second as timestamp 0 represents the epoch for
         * NTP era 1. */
        pCurrentTime->seconds = ntpSecs - UINT32_MAX - 1;
    }
    else
    {
        pCurrentTime->seconds = ntpSecs;
    }

    pCurrentTime->fractions = MILLISECONDS_TO_SNTP_FRACTIONS( currentTime.msecs );
}

static void sntpClient_SetTime( const SntpServerInfo_t * pTimeServer,
                                const SntpTimestamp_t * pServerTime,
                                int32_t clockOffsetSec,
                                SntpLeapSecondInfo_t leapSecondInfo )
{
    /* TODO - Handle leap second. */
    ( void ) leapSecondInfo;

    ( void ) pTimeServer;

    /* Obtain the mutext for accessing system clock variables. */
    xSemaphoreTake( xMutex, portMAX_DELAY );

    /* Use "step" approach if:
     * The system clock has drifted ahead of server time.
     *                         OR
     * This is the first time synchronization with NTP server since device boot-up.
     */
    if( ( clockOffsetSec < 0 ) || ( systemClock.firstTimeSyncDone == false ) )
    {
        SntpStatus_t status;
        uint32_t unixSecs;
        uint32_t unixMicroSecs;

        /* Convert server time from NTP timestamp to UNIX format. */
        status = Sntp_ConvertToUnixTime( pServerTime,
                                         &unixSecs,
                                         &unixMicroSecs );
        configASSERT( status == SntpSuccess );

        /* Immediately correct the base time of the system clock as server time. */
        systemClock.baseTime.secs = unixSecs;
        systemClock.baseTime.msecs = unixMicroSecs / 1000;

        /* Reset slew rate to zero as the time has been immediately corrected to server time. */
        systemClock.slewRate = 0;

        /* Store the tick count of the current time synchronization in the system clock. */
        systemClock.lastSyncTickCount = xTaskGetTickCount();

        /* Set the system clock flag that indicates completion of the first time synchronization since device boot-up. */
        if( systemClock.firstTimeSyncDone == false )
        {
            systemClock.firstTimeSyncDone = true;
        }
    }

    /* As the system clock is behind server time, we will use a "slew" approach to gradually
     * correct system time over the poll interval period. */
    else
    {
        /* Update the base time based on the previous slew rate and the time period transpired
         * since last time synchronization. */
        calculateCurrentTime( &systemClock.baseTime,
                              systemClock.lastSyncTickCount,
                              systemClock.slewRate,
                              &systemClock.baseTime );

        /* Calculate the new slew rate as offset in seconds of adjustment per second. */
        systemClock.slewRate = clockOffsetSec / systemClock.pollPeriod;

        /* Store the tick count of the current time synchronization in the system clock. */
        systemClock.lastSyncTickCount = xTaskGetTickCount();
    }

    xSemaphoreGive( xMutex );
}

/*************************************************************************************/

void initializeSystemClock( void )
{
    /* On boot-up initialize the system time as the first second in the configured year. */
    int64_t startupTimeInUnixSecs = translateYearToUnixSeconds( democonfigSYSTEM_START_YEAR );

    systemClock.baseTime.secs = startupTimeInUnixSecs;
    systemClock.baseTime.msecs = 0;

    LogInfo( ( "System time has been initialized to the year %u", democonfigSYSTEM_START_YEAR ) );
    printTime( &systemClock.baseTime );

    /* Initialize semaphore for guarding access to system clock variables. */
    xMutex = xSemaphoreCreateMutexStatic( &xSemaphoreMutex );
    configASSERT( xMutex );

    /* Clear the first time sync completed flag of the system clock object so that a "step" correction
     * of system time is utilized for the first time synchronization from a time server. */
    systemClock.firstTimeSyncDone = false;
}

/*-----------------------------------------------------------*/

static bool initializeSntpClient( SntpContext_t * pContext,
                                  const char ** pTimeServers,
                                  size_t numOfServers,
                                  uint8_t * pContextBuffer,
                                  size_t contextBufferSize,
                                  NetworkContext_t * pUdpContext )
{
    bool initStatus = false;

    /* Populate the list of time servers. */
    SntpServerInfo_t * pServers = pvPortMalloc( sizeof( SntpServerInfo_t ) * numOfServers );

    if( pServers == NULL )
    {
        LogError( ( "Unable to initialize SNTP client: Malloc failed for memory of configured time servers." ) );
    }
    else
    {
        for( int8_t index = 0; index < numOfServers; index++ )
        {
            pServers[ index ].pServerName = pTimeServers[ index ];
            pServers[ index ].port = SNTP_DEFAULT_SERVER_PORT;
        }

        LogInfo( ( "Calculated poll interval: %lus", systemClock.pollPeriod ) );

        /* Create a UDP socket for network I/O with server. */
        pUdpContext->socket = FreeRTOS_socket( FREERTOS_AF_INET,
                                               FREERTOS_SOCK_DGRAM,
                                               FREERTOS_IPPROTO_UDP );

        /* Check the socket was created successfully. */
        /* TODO - Consider using random port assigned by FreeRTOS for better protection */
        /* against "off-path" attacker. */
        if( pUdpContext->socket == FREERTOS_INVALID_SOCKET )
        {
            /* There was insufficient FreeRTOS heap memory available for the socket
             * to be created. */
            LogError( ( "Failed to create UDP socket for SNTP client due to insufficient memory." ) );
        }
        else
        {
            struct freertos_sockaddr bindAddress;
            UdpTransportInterface_t udpTransportIntf;

            bindAddress.sin_port = FreeRTOS_htons( SNTP_DEFAULT_SERVER_PORT );

            if( FreeRTOS_bind( pUdpContext->socket, &bindAddress, sizeof( bindAddress ) ) == 0 )
            {
                /* The bind was successful. */
                LogDebug( ( "UDP socket has been bound to port %lu", SNTP_DEFAULT_SERVER_PORT ) );
            }

            /* Set the UDP transport interface object. */
            udpTransportIntf.pUserContext = pUdpContext;
            udpTransportIntf.sendTo = UdpTransport_Send;
            udpTransportIntf.recvFrom = UdpTransport_Recv;

            /* Initialize context. */
            Sntp_Init( pContext,
                       pServers,
                       numOfServers,
                       democonfigSERVER_RESPONSE_TIMEOUT_MS,
                       pContextBuffer,
                       contextBufferSize,
                       resolveDns,
                       sntpClient_GetTime,
                       sntpClient_SetTime,
                       &udpTransportIntf,
                       NULL );

            initStatus = true;
        }
    }

    return initStatus;
}

/*-----------------------------------------------------------*/

void sntpTask( void * pParameters )
{
    SntpContext_t clientContext;
    bool initStatus = false;

    /* Variable representing the SNTP client context. */
    static SntpContext_t context;

    /* Memory for the SNTP packet buffer in the SNTP context. */
    static uint8_t contextBuffer[ SNTP_CONTEXT_NETWORK_BUFFER_SIZE ];

    /* Memory for the network context representing the UDP socket that will be
     * passed to the SNTP client context. */
    static NetworkContext_t udpContext;

    /* Store the configured time servers in an array. */
    static const char * pTimeServers[] = { democonfigLIST_OF_TIME_SERVERS };
    const size_t numOfServers = sizeof( pTimeServers ) / sizeof( char * );

    initStatus = initializeSntpClient( &clientContext,
                                       pTimeServers,
                                       numOfServers,
                                       contextBuffer,
                                       sizeof( contextBuffer ),
                                       &udpContext );

    if( initStatus == true )
    {
        SntpStatus_t status;

        /* Calculate Poll interval of SNTP client based on desired accuracy and clock tolerance of the system. */
        status = Sntp_CalculatePollInterval( democonfigSYSTEM_CLOCK_TOLERANCE_PPM,
                                             democonfigDESIRED_CLOCK_ACCURACY_MS,
                                             &systemClock.pollPeriod );
        configASSERT( status == SntpSuccess );

        LogInfo( ( "Initialized SNTP Client context. Starting the SNTP client loop for time synchronization every %lu seconds",
                   systemClock.pollPeriod ) );

        /* SNTP Client loop of sending and receiving SNTP packets for time synchronization at poll intervals */
        while( 1 )
        {
            /* TODO - Generate random number with corePKCS11. */
            status = Sntp_SendTimeRequest( &clientContext, 100 );
            configASSERT( status == SntpSuccess );

            /* Wait till the server response is not received. */
            do
            {
                /* Attempt to receive server response each time for 200 ms. */
                status = Sntp_ReceiveTimeResponse( &clientContext, 200 );
            } while( status == SntpNoResponseReceived );

            /* Wait for the poll interval period before the next iteration of time synchronization. */
            vTaskDelay( pdMS_TO_TICKS( systemClock.pollPeriod * 1000 ) );
        }
    }
    else
    {
        configASSERT( false );

        /* Terminate the task as the SNTP client failed to be run. */
        LogError( ( "Failed to initialize SNTP client. Terminating SNTP client task.." ) );

        vTaskDelete( NULL );
    }
}

/*-----------------------------------------------------------*/

void systemGetWallClockTime( UTCTime_t * pTime )
{
    TickType_t xTickCount = 0;
    uint32_t ulTimeMs = 0UL;

    /* Obtain the mutext for accessing system clock variables. */
    xSemaphoreTake( xMutex, portMAX_DELAY );

    /* Calculate the current RAM-based time using a mathematical formula using
     * system clock state parameters and the time transpired since last synchronization. */
    calculateCurrentTime( &systemClock.baseTime,
                          systemClock.lastSyncTickCount,
                          systemClock.slewRate,
                          pTime );

    xSemaphoreGive( xMutex );
}

/*-----------------------------------------------------------*/
