/*
 * FreeRTOS V202104.00
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
 * Demo for showing use of the coreSNTP library for synchronizing system time
 * with the internet and maintaining correct wall-clock time.
 *
 * The Example shown below uses this API to create MQTT messages and
 * send them over the connection established using FreeRTOS sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages.
 *
 * !!! NOTE !!!
 * This MQTT demo does not authenticate the server nor the client.
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

/* Demo Specific configs. */
#include "demo_config.h"

/* SNTP library includes. */
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
    #error "Define the config democonfigLIST_OF_TIME_SERVERS by following the instructions in file demo_config.h."
#endif

/*-----------------------------------------------------------*/

/* Default value of the clock accuracy as 100 milliseconds. */
#ifndef democonfigDESIRED_CLOCK_ACCURACY_MS
    #define democonfigDESIRED_CLOCK_ACCURACY_MS    ( 100 )
#endif

#ifndef democonfigCONTEXT_BUFFER_SIZE
    #define democonfigCONTEXT_BUFFER_SIZE    ( SNTP_PACKET_BASE_SIZE )
#endif

#define YEARS_TO_SECONDS( years ) \
    ( ( years * 365 + years / 4 ) * 24 * 3600 )

#define CLOCK_QUERY_TASK_DELAY_MS    ( 1000 )

#define MILLISECONDS_PER_SECOND      ( 1000U )                                        /**< @brief Milliseconds per second. */
#define MILLISECONDS_PER_TICK        ( MILLISECONDS_PER_SECOND / configTICK_RATE_HZ ) /**< Milliseconds per FreeRTOS tick. */


/*-----------------------------------------------------------*/

/* Type representing UTC time. */
typedef struct UTCTime
{
    uint32_t secs;
    uint32_t msecs;
} UTCTime_t;

struct NetworkContext
{
    Socket_t xSocket;
};


/* Shared global variables for representing UTC/wall-clock time in system. */
/* TODO - Group all system clock variables in a struct. */
static UTCTime_t baseTime;
static TickType_t lastSyncTickCount;
static uint32_t pollPeriod;
static uint32_t slewRate; /* Milliseconds/second */

SemaphoreHandle_t xMutex = NULL;
StaticSemaphore_t xSemaphoreMutex;

/* Global variable representing the SNTP client context. */
static SntpContext_t context;

static const char * pTimeServers[] = { democonfigLIST_OF_TIME_SERVERS };
static const size_t numOfServers = sizeof( pTimeServers ) / sizeof( char * );

/*-----------------------------------------------------------*/
static void getTime( UTCTime_t * pTime );
static void prvClockQueryTask( void * pvParameters );
static void sntpTask( void * parameters );
static void printTime( UTCTime_t * pTime );
static bool ResolveDns( const SntpServerInfo_t * pServerAddr,
                        uint32_t * pIpV4Addr );
static int32_t UdpTransport_Send( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  const void * pBuffer,
                                  size_t bytesToSend );
static int32_t UdpTransport_Recv( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  void * pBuffer,
                                  size_t bytesToRecv );
static void sntpClient_GetTime( SntpTimestamp_t * pCurrentTime );
static void sntpClient_SetTime( const SntpServerInfo_t * pTimeServer,
                                const SntpTimestamp_t * pServerTime,
                                int32_t clockOffsetSec,
                                SntpLeapSecondInfo_t leapSecondInfo );

static void printTime( UTCTime_t * pTime )
{
    struct tm * currTime;
    time_t time;
    SntpTimestamp_t ntpTime;
    SntpStatus_t status;
    UTCTime_t unixTime;


    /* Represent system time as NTP time. */
    ntpTime.seconds = pTime->secs;
    ntpTime.fractions = pTime->msecs * 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND;

    /* Convert from NTP to UNIX time representation. */
    status = Sntp_ConvertToUnixTime( &ntpTime, &unixTime.secs, &unixTime.msecs );
    unixTime.msecs /= 1000;

    /* Obtain the broken-down UTC representation of the current system time. */
    time = unixTime.secs;
    currTime = gmtime( &time );

    /* Log the time as both UNIX timestamp and Human Readable time. */
    LogInfo( ( "Time\nUNIX=%lusecs %lums\nHuman Readable= %lu-%02lu-%02lu %02luh:%02lum:%02lus",
               unixTime.secs, unixTime.msecs,
               currTime->tm_year + 1900, currTime->tm_mon + 1, currTime->tm_mday,
               currTime->tm_hour, currTime->tm_min, currTime->tm_sec ) );
}

static void calculateCurrentTime( UTCTime_t * pBaseTime,
                                  TickType_t lastSyncTickCount,
                                  uint32_t slewRate,
                                  UTCTime_t * pCurrentTime )
{
    uint64_t totalOffsetMs = 0;
    TickType_t totalNoOfTicks = xTaskGetTickCount() - lastSyncTickCount;

    /* If slew rate is set, then calculate the offset only based on the slew rate. */
    if (slewRate > 0)
    {
        totalOffsetMs = (uint64_t) slewRate * (uint64_t) totalNoOfTicks * MILLISECONDS_PER_TICK;
    }
    /* Without a slew correction rate, calculate the time based solely on tick counts. */
    else
    {
        totalOffsetMs = totalNoOfTicks * MILLISECONDS_PER_TICK;
    }

    /* Set the current UTC time in the output parameter. */
    if(totalOffsetMs >= 1000 )
    {
        uint32_t totalOffsetSec = totalOffsetMs / 1000;
        pCurrentTime->secs = pBaseTime->secs + totalOffsetSec;
        pCurrentTime->msecs = totalOffsetMs % 1000;
    }
    else
    {
        pCurrentTime->secs = pBaseTime->secs;
        pCurrentTime->msecs = totalOffsetMs;
    }
}

/********************** DNS Resolution Interface *******************************/
static bool ResolveDns( const SntpServerInfo_t * pServerAddr,
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
/* TODO - Consider efficiency improvements of: */
/* 1. Returning immediately if TX buffer is full to avoid blocking for default send timeout? */
/*    Can use FreeRTOS_maywrite API */
/* 2. Storing source address and UDP port for validation of reverse information in UDP */
/* packer received from server in receive function. */
int32_t UdpTransport_Send( NetworkContext_t * pNetworkContext,
                           uint32_t serverAddr,
                           uint16_t serverPort,
                           const void * pBuffer,
                           size_t bytesToSend )
{
    struct freertos_sockaddr xDestinationAddress;
    int32_t iReturned;

    /* TODO - Is this required? */
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

    /* The UDP socket may have a receive block time.  If bytesToRecv is greater
     * than 1 then a frame is likely already part way through reception and
     * blocking to wait for the desired number of bytes to be available is the
     * most efficient thing to do.  If bytesToRecv is 1 then this may be a
     * speculative call to read to find the start of a new frame, in which case
     * blocking is not desirable as it could block an entire protocol agent
     * task for the duration of the read block time and therefore negatively
     * impact performance.  So if bytesToRecv is 1 then don't call recv unless
     * it is known that bytes are already available. */
    /*TODO - Add logic to for non-blocking read for single byte read request by changing */
    /* socket timeout config temporarily. */

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

    /* Obtain mutex for accessing system clock variables */
    xSemaphoreTake( xMutex, portMAX_DELAY );

    calculateCurrentTime( &baseTime, lastSyncTickCount, slewRate, &currentTime );

    /* Convert UTC time to SNTP timestamp format. */
    pCurrentTime->seconds = currentTime.secs;
    pCurrentTime->fractions = currentTime.msecs * 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND;

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

    /* Use "step" approach if the system clock has drifted ahead of server time. */
    if( clockOffsetSec < 0 )
    {
        /* Immediately correct the base time of the system clock. */
        baseTime.secs = pServerTime->seconds;
        baseTime.msecs = ( pServerTime->fractions / (1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND ));

        /* Reset slew rate to zero as the time has been immediately corrected to server time. */
        slewRate = 0;

        lastSyncTickCount = xTaskGetTickCount();
    }

    /* As the system clock is behind server time, we will use a "slew" approach to gradually
     * correct system time over the poll interval period. */
    else
    {
        /* Update the base time based on the previous slew rate and the time period transpired
         * since last time synchronization. */
        calculateCurrentTime( &baseTime, lastSyncTickCount, slewRate, &baseTime );

        /* Calculate the new slew rate as offset in milliseconds per second. */
        slewRate = clockOffsetSec / pollPeriod;

        lastSyncTickCount = xTaskGetTickCount();
    }

    xSemaphoreGive( xMutex );
}

/*************************************************************************************/

/**
 * @brief Create the task that demonstrates the MQTT API over a plaintext TCP
 * connection.
 */
void vStartSntpDemo( void )
{
    /* On boot-up initialize the system time as the first second in the configured year. */
    int32_t lNoOfYearsSince1900 = democonfigSYSTEM_START_YEAR - 1900;
    int64_t llnoOfSecondsSince1900 = YEARS_TO_SECONDS( lNoOfYearsSince1900 );

    if( llnoOfSecondsSince1900 <= UINT32_MAX )
    {
        baseTime.secs = llnoOfSecondsSince1900;
    }
    else
    {
        baseTime.secs = ( uint32_t ) llnoOfSecondsSince1900 - UINT32_MAX - 1UL;
    }

    LogInfo( ( "System time has been initialized to the year %u", democonfigSYSTEM_START_YEAR ) );
    printTime( &baseTime );

    /* Initialize sempahore for guarding access to system clock variables. */
    xMutex = xSemaphoreCreateMutexStatic( &xSemaphoreMutex );
    configASSERT( xMutex );

    /* Create the SNTP client task that is reponsible for synchronizing system time with the time servers
     * periodically. This is created as a high priority task to keep the SNTP client operation uninhindered. */
    xTaskCreate( sntpTask,                 /* Function that implements the task. */
                 "SntpClientTask",         /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 configMAX_PRIORITIES - 1, /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );

    /* Create the task that represents an application needing wall-clock time. */
    xTaskCreate( prvClockQueryTask,        /* Function that implements the task. */
                 "SampleApp",              /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

/* Task that will query and log system time every second. */
static void prvClockQueryTask( void * pvParameters )
{
    UTCTime_t systemTime;

    while( 1 )
    {
        getTime( &systemTime );

        printTime( &systemTime );

        vTaskDelay( pdMS_TO_TICKS( CLOCK_QUERY_TASK_DELAY_MS ) );
    }
}

/*-----------------------------------------------------------*/
static void sntpTask( void * parameters )
{
    UdpTransportInterface_t udpTransportIntf;
    NetworkContext_t udpContext;
    SntpStatus_t status;
    SntpContext_t clientContext;
    static uint8_t contextBuffer[ democonfigCONTEXT_BUFFER_SIZE ];
    struct freertos_sockaddr xBindAddress;

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
                                         &pollPeriod );
    configASSERT( status == SntpSuccess );

    LogInfo( ( "Calculated poll interval: %lus", pollPeriod ) );

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
               ResolveDns,
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
        vTaskDelay( pdMS_TO_TICKS( pollPeriod * 1000 ) );
    }
}

/*-----------------------------------------------------------*/

static void getTime( UTCTime_t * pTime )
{
    TickType_t xTickCount = 0;
    uint32_t ulTimeMs = 0UL;

    /* Obtain the mutext for accessing system clock variables. */
    xSemaphoreTake( xMutex, portMAX_DELAY );

    /* Calculate the current RAM-based time using a mathematical formula using
     * system clock state parameters and the time transpired since last synchronization. */
    calculateCurrentTime( &baseTime, lastSyncTickCount, slewRate, pTime );

    xSemaphoreGive( xMutex );
}

/*-----------------------------------------------------------*/
