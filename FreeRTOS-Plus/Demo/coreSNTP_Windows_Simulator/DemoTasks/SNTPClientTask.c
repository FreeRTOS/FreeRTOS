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
 * @brief The periodicity of the application task in query and logging system time. This is the time
 * interval between consecutive system clock time queries in the sample application task.
 */
#define CLOCK_QUERY_TASK_DELAY_MS           ( 1000 )

/**
 * @brief The constant for storing the number of milliseconds per FreeRTOS tick in the system.
 * @note This value represents the time duration per tick from the perspective of the
 * of Windows Simulator based FreeRTOS system that carries lagging clock drift in relation to
 * internet time or UTC time. Thus, the actual time duration value per tick of the system will be
 * larger from the perspective of internet time.
 */
#define MILLISECONDS_PER_TICK               ( 1000 / configTICK_RATE_HZ )

/**
 * @brief Utility macro to convert the fractions part of SNTP timestamp to milliseconds.
 */
#define SNTP_FRACTIONS_TO_MILLISECONDS( fractions )    ( fractions / ( 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND ) )

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
    Socket_t xSocket;
};

/**
 * @brief Structure aggregating state variables for RAM-based wall-clock time
 * in Coordinated Universal Time (UTC) for system.
 *
 * @note This demo uses the following mathematical model to represent current
 * time in RAM.
 *
 *  Total Time Elapsed since last SNTP synchronization =
 *      No. of FreeRTOS ticks since last time synchronization *
 *      Time Duration between consecutive ticks
 *
 *  Slew Adjustment = (Slew Rate * Total Time Elapsed Since Last Tine Synchronization)
 *
 *  Current Time = Base Time +
 *                 Time Elapsed Since Last synchronization +
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
 * @brief Shared global variables for representing UTC/wall-clock time in system.
 */
static SystemClock_t systemClock;

/**
 * @brief Global variables of mutex protecting access to the shared memory of the
 * system clock parameters.
 */
static SemaphoreHandle_t xMutex = NULL;
static StaticSemaphore_t xSemaphoreMutex;

/*-----------------------------------------------------------*/

/**
 * @brief Utility function to convert the year to UNIX time representation of seconds
 * since 1st Jan 1970 00h:00m:00s seconds.
 * This utility does account for leap years.
 *
 * @note The time represented by the passed year is the
 * first second on 1st January of the year.
 *
 * @param[in] The year to translate.
 */
static uint32_t translateYearToUnixSeconds( uint16_t year );

/**
 * @brief Calculates the current time from the system clock parameters
 * of slew rate and tick count since last time synchronization.
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
 * @param[in] serverAddr The IPv4 address of the time server which will be sent
 * time request to.
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
 * representing the FreeRTOS UDP socket to use for network send operation.
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
 *     correction approach when the system time is ahead by a large margin in the
 *     order of days, months or more.
 *     OR
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
    uint64_t totalOffsetMs = 0;
    TickType_t totalNoOfTicks = xTaskGetTickCount() - lastSyncTickCount;

    /* Calculate time elapsed since last synchronization according to the number
     * of system ticks passed. */
    totalOffsetMs = totalNoOfTicks * MILLISECONDS_PER_TICK;

    /* If slew rate is set, then apply the slew-based clock adjustment for the elapsed time. */
    if( slewRate > 0 )
    {
        totalOffsetMs += ( uint64_t ) slewRate * ( uint64_t ) totalNoOfTicks * MILLISECONDS_PER_TICK;
    }

    /* Set the current UTC time in the output parameter. */
    if( totalOffsetMs >= 1000 )
    {
        pCurrentTime->secs = pBaseTime->secs + totalOffsetMs / 1000;
        pCurrentTime->msecs = totalOffsetMs % 1000;
    }
    else
    {
        pCurrentTime->secs = pBaseTime->secs;
        pCurrentTime->msecs = totalOffsetMs;
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

        uint8_t pcIpAddr[ 16 ];
        FreeRTOS_inet_ntoa( resolvedAddr, pcIpAddr );
        LogInfo( ( "Resolved time server as %s", pcIpAddr ) );
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
    struct freertos_sockaddr xDestinationAddress;
    int32_t iReturned;

    xDestinationAddress.sin_addr = serverAddr;
    xDestinationAddress.sin_port = FreeRTOS_htons( serverPort );

    /* Send the buffer with ulFlags set to 0, so the FREERTOS_ZERO_COPY bit
     * is clear. */
    iReturned = FreeRTOS_sendto( /* The socket being send to. */
        pNetworkContext->xSocket,
        /* The data being sent. */
        pBuffer,
        /* The length of the data being sent. */
        bytesToSend,
        /* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
        0,
        /* Where the data is being sent. */
        &xDestinationAddress,
        /* Not used but should be set as shown. */
        sizeof( xDestinationAddress )
        );

    return iReturned;
}

static int32_t UdpTransport_Recv( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  void * pBuffer,
                                  size_t bytesToRecv )
{
    struct freertos_sockaddr xSourceAddress;
    int32_t iReturned;
    socklen_t xAddressLength = sizeof( struct freertos_sockaddr );

    /* Receive into the buffer with ulFlags set to 0, so the FREERTOS_ZERO_COPY bit
     * is clear. */
    iReturned = FreeRTOS_recvfrom( /* The socket data is being received on. */
        pNetworkContext->xSocket,

        /* The buffer into which received data will be
         * copied. */
        pBuffer,

        /* The length of the buffer into which data will be
         * copied. */
        bytesToRecv,
        /* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
        0,
        /* Will get set to the source of the received data. */
        &xSourceAddress,
        /* Not used but should be set as shown. */
        &xAddressLength
        );

    /* If data is received from the network, discard the data if  received from a different source than
     * the server. */
    if( ( iReturned > 0 ) && ( ( xSourceAddress.sin_addr != serverAddr ) ||
                               ( FreeRTOS_ntohs( xSourceAddress.sin_port ) != serverPort ) ) )
    {
        iReturned = 0;

        /* Convert the IP address of the sender's address to string for logging. */
        char stringAddr[ 16 ];
        FreeRTOS_inet_ntoa( xSourceAddress.sin_addr, stringAddr );

        /* Log about reception of packet from unexpected sender. */
        LogWarn( ( "Received UDP packet from unexpected source: Addr=%s Port=%u",
                   stringAddr, FreeRTOS_ntohs( xSourceAddress.sin_port ) ) );
    }

    /* Translate the return code of timeout to the UDP transport interface expected
     * code to indicate read retry. */
    else if( iReturned == -pdFREERTOS_ERRNO_EWOULDBLOCK )
    {
        iReturned = 0;
    }

    return iReturned;
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

    pCurrentTime->seconds = currentTime.secs + SNTP_TIME_AT_UNIX_EPOCH_SECS;
    pCurrentTime->fractions = MILLISECONDS_TO_SNTP_FRACTIONS( currentTime.msecs );

    /* Release mutex. */
    xSemaphoreGive( xMutex );
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
     * This is the first time of time synchronized with NTP server since device boot-up.
     */
    if( ( clockOffsetSec < 0 ) || ( systemClock.firstTimeSyncDone == false ) )
    {
        SntpStatus_t status;

        /* Immediately correct the base time of the system clock. */
        status = Sntp_ConvertToUnixTime( pServerTime,
                                         &systemClock.baseTime.secs,
                                         &systemClock.baseTime.msecs );
        configASSERT( status == SntpSuccess );

        systemClock.baseTime.msecs /= 1000;

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
    int64_t llnoOfSecondsSince1970 = translateYearToUnixSeconds( democonfigSYSTEM_START_YEAR );

    systemClock.baseTime.secs = llnoOfSecondsSince1970;
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

void sntpTask( void * parameters )
{
    UdpTransportInterface_t udpTransportIntf;
    NetworkContext_t udpContext;
    SntpStatus_t status;
    SntpContext_t clientContext;
    static uint8_t contextBuffer[ SNTP_CONTEXT_NETWORK_BUFFER_SIZE ];
    struct freertos_sockaddr xBindAddress;

    /* Global variable representing the SNTP client context. */
    static SntpContext_t context;

    static const char * pTimeServers[] = { democonfigLIST_OF_TIME_SERVERS };
    static const size_t numOfServers = sizeof( pTimeServers ) / sizeof( char * );

    /* Populate the list of time servers. */
    SntpServerInfo_t * pServers = pvPortMalloc( sizeof( SntpServerInfo_t ) * numOfServers );

    for( int8_t index = 0; index < numOfServers; index++ )
    {
        pServers[ index ].pServerName = pTimeServers[ index ];
        pServers[ index ].port = SNTP_DEFAULT_SERVER_PORT;
    }

    /* Calculate Poll interval of SNTP client based on desired accuracy and clock tolerance of the system. */
    status = Sntp_CalculatePollInterval( democonfigSYSTEM_CLOCK_TOLERANCE_PPM,
                                         democonfigDESIRED_CLOCK_ACCURACY_MS,
                                         &systemClock.pollPeriod );
    configASSERT( status == SntpSuccess );

    LogInfo( ( "Calculated poll interval: %lus", systemClock.pollPeriod ) );

    /* Create a UDP socket for network I/O with server. */
    udpContext.xSocket = FreeRTOS_socket( FREERTOS_AF_INET,
                                          FREERTOS_SOCK_DGRAM,
                                          FREERTOS_IPPROTO_UDP );

    /* Check the socket was created successfully. */
    /* TODO - Consider using random port assigned by FreeRTOS for better protection */
    /* against "off-path" attacker. */
    if( udpContext.xSocket != FREERTOS_INVALID_SOCKET )
    {
        xBindAddress.sin_port = FreeRTOS_htons( SNTP_DEFAULT_SERVER_PORT );

        if( FreeRTOS_bind( udpContext.xSocket, &xBindAddress, sizeof( xBindAddress ) ) == 0 )
        {
            LogDebug( ( "UDP socket has been bound to port %lu", SNTP_DEFAULT_SERVER_PORT ) );
            /* The bind was successful. */
        }
    }
    else
    {
        /* There was insufficient FreeRTOS heap memory available for the socket
         * to be created. */
        LogError( ( "Failed to create UDP socket for SNTP client due to insufficient memory." ) );
    }

    /* Set the UDP transport interface object. */
    udpTransportIntf.pUserContext = &udpContext;
    udpTransportIntf.sendTo = UdpTransport_Send;
    udpTransportIntf.recvFrom = UdpTransport_Recv;

    /* Initialize context. */
    Sntp_Init( &clientContext,
               pServers,
               numOfServers,
               democonfigSERVER_RESPONSE_TIMEOUT_MS,
               contextBuffer,
               sizeof( contextBuffer ),
               resolveDns,
               sntpClient_GetTime,
               sntpClient_SetTime,
               &udpTransportIntf,
               NULL );

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
