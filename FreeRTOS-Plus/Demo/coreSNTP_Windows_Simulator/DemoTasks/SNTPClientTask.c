/*
 * FreeRTOS V202112.00
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
 * system clock with SNTP/NTP server(s). Any other task running an application in the
 * system can query the system time. For an example of an application task querying time
 * from the system, refer to the SampleAppTask.c file in this project.
 *
 * This demo shows how the coreSNTP library can be used to communicate with SNTP/NTP
 * servers in a mutually authenticated through the use of symmetric-key based AES-128-CMAC
 * algorithm. To run this demo with an SNTP/NTP server in authenticated mode, the AES-128-CMAC
 * symmetric key needs to be pre-shared between the client (i.e. this demo) and the server.
 *
 * !!!Note!!!:
 * Even though this demo shows the use of AES-128-CMAC, a symmetric-key cryptographic based
 * solution, for authenticating SNTP communication between the demo (SNTP client) and
 * SNTP/NTP server, we instead RECOMMEND that production devices use the most secure authentication
 * mechanism alternative available with the Network Time Security (NTS) protocol, an asymmetric-key
 * cryptographic protocol. For more information, refer to the NTS specification here:
 * https://datatracker.ietf.org/doc/html/rfc8915
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

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

/* PKCS11 includes. */
#include "core_pki_utils.h"
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"

/* Backoff Algorithm include. */
#include "backoff_algorithm.h"

/*-----------------------------------------------------------*/

/* Compile time error for undefined configs. */

#ifndef democonfigLIST_OF_TIME_SERVERS
    #error "Define the democonfigLIST_OF_TIME_SERVERS config by following the instructions in demo_config.h file."
#endif

#ifndef democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS
    #error "Define the democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS config by following the instructions in demo_config.h file."
#endif

#ifndef democonfigLIST_OF_AUTHENTICATION_KEY_IDS
    #error "Define the democonfigLIST_OF_AUTHENTICATION_KEY_IDS config by following the instructions in demo_config.h file."
#endif

#ifndef democonfigSNTP_CLIENT_POLLING_INTERVAL_SECONDS
    #error "Define the democonfigSNTP_CLIENT_POLLING_INTERVAL_SECONDS config by following instructions in demo_config.h file."
#endif

#ifndef democonfigSYSTEM_START_YEAR
    #error "Define the democonfigSYSTEM_START_YEAR config by following instructions in demo_config.h file."
#endif

/*-----------------------------------------------------------*/
/* Default values for timeout configurations . */

#ifndef democonfigSERVER_RESPONSE_TIMEOUT_MS
    #define democonfigSERVER_RESPONSE_TIMEOUT_MS    ( 5000 )
#endif

#ifndef democonfigSEND_TIME_REQUEST_TIMEOUT_MS
    #define democonfigSEND_TIME_REQUEST_TIMEOUT_MS    ( 50 )
#endif

#ifndef democonfigRECEIVE_SERVER_RESPONSE_BLOCK_TIME_MS
    #define democonfigRECEIVE_SERVER_RESPONSE_BLOCK_TIME_MS    ( 200 )
#endif

/**
 * @brief The size for network buffer that is allocated for initializing the coreSNTP library in the
 * demo.
 *
 * @note The size of the buffer MUST be large enough to hold an entire SNTP packet, which includes the standard SNTP
 * packet data of 48 bytes and authentication data for security mechanism, if used, in communication with time server.
 */
#define SNTP_CONTEXT_NETWORK_BUFFER_SIZE        ( SNTP_PACKET_BASE_SIZE )

/**
 * @brief The constant for storing the number of milliseconds per FreeRTOS tick in the system.
 * @note This value represents the time duration per tick from the perspective of the
 * of Windows Simulator based FreeRTOS system that carries lagging clock drift in relation to
 * internet time or UTC time. Thus, the actual time duration value per tick of the system will be
 * larger from the perspective of internet time.
 */
#define MILLISECONDS_PER_TICK                   ( 1000 / configTICK_RATE_HZ )

/**
 * @brief The fixed size of the key for the AES-128-CMAC algorithm used for authenticating communication
 * between the time server and the client.
 */
#define AES_CMAC_AUTHENTICATION_KEY_SIZE        ( 16 )

/**
 * @brief The size of the "Key Identifier" field in the SNTP packet when symmetric key authentication mode as
 * security mechanism in communicating with time server.
 *
 * The "Key Identifier" field appears immediately after the 48 bytes of standard SNTP packet created by the coreSNTP
 * library. For more information, refer to the SNTPv4 specification: https://datatracker.ietf.org/doc/html/rfc4330#page-8
 *
 * @note This demo uses the "Key Identifier" field to communicate with time servers that support authentication mechanism.
 * This field is stored with the Key ID of the AES-128-CMAC based authentication key stored in the time server.
 */
#define SNTP_PACKET_SYMMETRIC_KEY_ID_LENGTH     4

/**
 * @brief The offset for the starting byte of the "Key Identifier" field in an SNTPv4/NTPv4 packet.
 * This field is only used when symmetric key authentication mode is used for communicating with time server.
 *
 * For more information of the SNTP packet format, refer to the SNTPv4 specification
 * https://datatracker.ietf.org/doc/html/rfc4330#page-8
 */
#define SNTP_PACKET_SYMMETRIC_KEY_ID_OFFSET     SNTP_PACKET_BASE_SIZE

/**
 * @brief The total size of an SNTP packet (which remains same for both client request and server response in SNTP communication)
 * when using symmetric key based authentication mechanism.
 *
 * This value includes size of the 48 bytes of standard SNTP packet, and the "Key Identifier" and "Message Digest" fields
 * that are used for authentication information in SNTP communication between client and server.
 *
 * For more information of the SNTP packet format, refer to the SNTPv4 specification
 * https://datatracker.ietf.org/doc/html/rfc4330#page-8
 */
#define SNTP_PACKET_AUTHENTICATED_MODE_SIZE     ( SNTP_PACKET_BASE_SIZE + SNTP_PACKET_SYMMETRIC_KEY_ID_LENGTH + pkcs11AES_CMAC_SIGNATURE_LENGTH )

/**
 * @brief The maximum poll period that the SNTP client can use as back-off on receiving a rejection from a time server.
 *
 * @note This demo performs back-off in polling rate from time server ONLY for the case when a single time server being
 * is configured through the democonfigLIST_OF_TIME_SERVERS macro.
 * This is because when more than one time server is configured, the coreSNTP library automatically handles the case
 * of server rejection of time request by rotating to the next configured server for subsequent time polling requests.
 */
#define SNTP_DEMO_POLL_MAX_BACKOFF_DELAY_SEC    UINT16_MAX

/**
 * @brief The maximum number of times of retrying time requests at exponentially backed-off polling frequency
 * from a server that rejects time requests.
 *
 * @note This macro is only relevant for the case when a single time server is configured in
 * the demo through, democonfigLIST_OF_TIME_SERVERS.
 */
#define SNTP_DEMO_MAX_SERVER_BACKOFF_RETRIES    10

/*-----------------------------------------------------------*/

/**
 * @brief The definition of the @ref NetworkContext_t structure for the demo.
 * The structure wraps a FreeRTOS+TCP socket that is used for UDP communication
 * with time servers.
 *
 * @note The context is used in the @ref UdpTransportInterface_t interface required
 * by the coreSNTP library.
 */
struct NetworkContext
{
    Socket_t socket;
};

/**
 * @brief The definition of the @ref SntpAuthContext_t structure for the demo.
 * This structure represents the symmetric key for the AES-128-CMAC algorithm based
 * authentication mechanism shown in the demo for securing SNTP communication
 * between client and time server.
 *
 * @note The context is used in the @ref SntpAuthInterface_t interface required
 * by the coreSNTP library for enabling authentication.
 */
struct SntpAuthContext
{
    const char * pServer;
    int32_t keyId;
    uint8_t pAuthKey[ AES_CMAC_AUTHENTICATION_KEY_SIZE ];
};

/**
 * @brief Structure aggregating state variables for RAM-based wall-clock time
 * in Coordinated Universal Time (UTC) for system.
 *
 * @note This demo uses the following mathematical model to represent current
 * time in RAM.
 *
 *  BaseTime = Time set at boot or the last synchronized time
 *  Slew Rate = Number of milliseconds to adjust per system time second
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
    uint64_t slewRate; /* Milliseconds/Seconds */
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


/*
 * @brief Stores the configured time servers in an array.
 */
static const char * pTimeServers[] = { democonfigLIST_OF_TIME_SERVERS };
const size_t numOfServers = sizeof( pTimeServers ) / sizeof( char * );

/**
 * @brief Stores the list of configured AES-128-CMAC symmetric keys for authentication
 * mechanism for corresponding time servers in democonfigLIST_OF_TIME_SERVERS.
 */
static const char * pAESCMACAuthKeys[] = { democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS };

/**
 * @brief Stores list of Key IDs corresponding to the authentication keys configured
 * in democonfigLIST_OF_TIME_SERVERS.
 */
static const int32_t pAuthKeyIds[] = { democonfigLIST_OF_AUTHENTICATION_KEY_IDS };

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
 *   SlewRate = Number of milliseconds to adjust per system time second
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
                                  uint64_t slewRate,
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
                                  NetworkContext_t * pUdpContext,
                                  SntpAuthContext_t * pAuthContext );

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
                                  uint16_t bytesToSend );

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
                                  uint16_t bytesToRecv );

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
 * @note This demo uses a combination of "step" AND "slew" methodology
 * for system clock correction.
 * 1. "Step" correction is ALWAYS used to immediately correct the system clock
 *    to match server time on every successful time synchronization with a
 *    time server (that occurs periodically on the poll interval gaps).
 *
 * 2. "Slew" correction approach is used for compensating system clock drift
 *    during the poll interval period between time synchronization attempts with
 *    time server(s) when latest time server is not known. The "slew rate" is
 *    calculated ONLY once on the occasion of the second successful time
 *    synchronization with a time server. This is because the demo initializes
 *    system time with (the first second of) the democonfigSYSTEM_START_YEAR
 *    configuration, and thus, the the actual system clock drift over a period
 *    of time can be calculated only AFTER the demo system time has been synchronized
 *    with server time once. Thus, after the first time period of poll interval has
 *    transpired, the system clock drift is calculated correctly on the subsequent
 *    successful time synchronization with a time server.
 *
 * @note The above system clock correction algorithm is just one example of a correction
 * approach. It can be modified to suit your application needs. For example, your
 * application can use ONLY the "step" correction methodology for simplicity of system clock
 * time calculation logic if the application is not sensitive to abrupt time changes
 * (that occur at the instances of periodic time synchronization attempts). In such a case,
 * the Sntp_CalculatePollInterval() API of coreSNTP library can be used to calculate
 * the optimum time polling period for your application based on the factors of your
 * system's clock drift rate and the maximum clock drift tolerable by your application.
 *
 *
 * @param[in] pTimeServer The time server from whom the time has been received.
 * @param[in] pServerTime The most recent time of the server, @p pTimeServer, sent in its
 * time response.
 * @param[in] clockOffsetMs The value, in milliseconds, of system clock offset relative
 * to the server time calculated by the coreSNTP library. If the value is positive, then
 * the system is BEHIND the server time, and a "slew" clock correction approach is used in
 * this demo. If the value is negative, then the system time is AHEAD of the server time,
 * and a "step" clock correction approach is used in this demo.
 * @param[in] leapSecondInfo This indicates whether there is an upcoming leap second insertion
 * or deletion (according to astronomical time) the last minute of the end of the month that the
 * system time needs to adjust for. Leap second adjustment is valuable for applications that
 * require non-abrupt increment of time for use cases like logging. This demo DOES NOT showcase
 * leap second adjustment in system clock.
 */
static void sntpClient_SetTime( const SntpServerInfo_t * pTimeServer,
                                const SntpTimestamp_t * pServerTime,
                                int64_t clockOffsetMs,
                                SntpLeapSecondInfo_t leapSecondInfo );

/**
 * @brief Utility function to create a PKCS11 session and a PKCS11 object, and obtain the PKCS11
 * global function list for performing 128 bit AES-CMAC operations.
 * This function is called by the definitions of both the authentication interface functions,
 * @ref SntpGenerateAuthCode_t and @ref SntpValidateServerAuth_t, in this demo for the
 * AES-CMAC operations.
 *
 * @param[in] pAuthContext The context representing the symmetric key for the AES-CMAC operation.
 * @param[out] pPkcs11Session This is populated with the created PKCS11 session.
 * @param[out] pFunctionList This is populated with the function list obtained from the created
 * PKCS11 session.
 * @param[out] pCmacKey This is populated with the created PKCS11 object handle for AES-CMAC
 * operations.
 *
 * @return The return status code of PKCS11 API calls.
 */
static CK_RV setupPkcs11ObjectForAesCmac( const SntpAuthContext_t * pAuthContext,
                                          CK_SESSION_HANDLE * pPkcs11Session,
                                          CK_FUNCTION_LIST_PTR * pFunctionList,
                                          CK_OBJECT_HANDLE * pCmacKey );

/**
 * @brief Utility function for filling the authentication context with the time server and
 * its associated authentication key information from the democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS
 * and democonfigLIST_OF_AUTHENTICATION_KEY_IDS configuration lists.
 *
 * The authentication context represents the server and its authentication key information being
 * used by the SNTP client at a time for time query. This function is called to update the context
 * at the time of SNTP client initialization as well as whenever the SNTP client rotates the time
 * server of use.
 *
 * @param[in] pServer The time server whose information is filled in the context.
 * @param[out] pAuthContext The authentication context to update with information about the @p pServer.
 */
static bool populateAuthContextForServer( const char * pServer,
                                          SntpAuthContext_t * pAuthContext );

/**
 * @brief The demo implementation of the @ref SntpGenerateClientAuth_t function of the authentication
 * interface required by the coreSNTP library to execute functionality of generating client-side
 * message authentication code and appending it to the time request before sending to a time server.
 *
 * This function first determines whether the passed time server has an authentication key configured
 * in the demo. If the time server supports authentication, the function utilizes the corePKCS11 library
 * to generate the client authentication code as a signature using the AES-128-CMAC algorithm, and append
 * it to the passed SNTP request packet buffer, @p pRequestBuffer.
 *
 * @note If the time server supports authentication, this function writes the "Key Identifier" and "Message
 * Digest" fields of an SNTP packet.
 *
 * @param[in, out] pAuthContext The authentication context representing the time server and its authentication
 * credentials. If the coreSNTP library rotated the time server of use, then this function updates the context
 * to carry authentication information for the new server.
 * @param[in] pTimeServer The current time server being used for sending time queries by the SNTP client.
 * This is used to determine whether the @p pAuthContext carries stale information of a previously used server,
 * and thus, needs to be updated with information of the current server, @p pTimeServer.
 * @param[in, out] pRequestBuffer The buffer representing the SNTP request packet, which is already populated with
 * the standard 48 bytes of packet data. If the time server supports authentication, then the 48 bytes of data
 * and the authentication key are used to generated AES-128-CMAC signature, and the "Key Identifier" and "Message
 * Digest" fields of the packet are filled in the buffer.
 * @param[in] bufferSize The total buffer size of the @p pRequestBuffer for the SNTP request packet.
 * @param[out] pAuthCodeSize This will be populated with the total bytes for authentication data written to the
 * @p pRequestBuffer when
 *
 * @return Returns one of the following:
 * - SntpSuccess if EITHER no authentication key information has been configured for the time
 * server, and thus, no AES-CMAC operation was performed OR the time server supports authentication and
 * the corePKCS11 operations are successful in generating and appending authentication information to the
 * @p pRequestBuffer.
 * - SntpErrorAuthFailure if there is failure in PKCS#11 operations in generating and appending the AES-128-CMAC
 * signature as the authentication code to the @p pRequestBuffer.
 */
static SntpStatus_t addClientAuthCode( SntpAuthContext_t * pAuthContext,
                                       const SntpServerInfo_t * pTimeServer,
                                       void * pRequestBuffer,
                                       uint16_t bufferSize,
                                       uint16_t * pAuthCodeSize );


/**
 * @brief The demo implementation of the @ref SntpValidateServerAuth_t function of the authentication
 * interface required by the coreSNTP library to execute validation of server as the source of the
 * received SNTP response by verifying the authentication information present in the packet.
 *
 * This function first checks whether the passed time server has authentication key information configured
 * in the demo to determine if the server supports authentication. If the time server supports authentication,
 * the function utilizes the corePKCS11 library to verify the AES-128-CMAC signature in the packet, @p pResponseData
 * that represents the server authentication code.
 *
 * @param[in] pAuthContext The authentication context representing the time server of use and its authentication
 * credentials.
 * @param[in] pTimeServer The current time server of use from which the response data, @p pResponseData has been
 * received by the SNTP client. This SHOULD match the time server information carried by the authentication context.
 * @param[in] pResponseData The buffer representing the SNTP response packet, received from the server, @p pTimeServer,
 * which contains the server authentication code, if the server supports authentication. The authentication code, if present,
 * is verified using corePKCS11 to be the expected AES-128-CMAC signature using the standard 48 bytes of SNTP packet data
 * present in the buffer and the secret symmetric key configured for the server.
 * @param[in] responseSize The total buffer size of the @p pResponseData for the SNTP response packet.
 *
 * @return Returns one of the following:
 * - SntpSuccess if EITHER no authentication key information has been configured for the time server, and thus,
 * no AES-CMAC validation operation is performed OR the time server supports authentication and the authentication
 * code has been successfully validated @p pBuffer.
 * - SntpErrorAuthFailure if there is internal failure in PKCS#11 operations in validating the server authentication code as
 * as the AES-128-CMAC for the information present in the response packet, @p pResponseData.
 * - SntpServerNotAuthenticated if the server is not validated from the response due to the authentication code not matching
 * the expected AES-128-CMAC signature.
 */
static SntpStatus_t validateServerAuth( SntpAuthContext_t * pAuthContext,
                                        const SntpServerInfo_t * pTimeServer,
                                        const void * pResponseData,
                                        size_t responseSize );

/**
 * @brief Generates a random number using PKCS#11.
 *
 * @note It is RECOMMENDED to generate a random number for the call to Sntp_SendTimeRequest API
 * of coreSNTP library to protect against server response spoofing attacks from "network off-path"
 * attackers.
 *
 * @return The generated random number.
 */
static uint32_t generateRandomNumber();

/**
 * @brief Utility to create a new FreeRTOS UDP socket and bind a random
 * port to it.
 * A random port is used for the created UDP socket as a protection mechanism
 * against spoofing attacks from malicious actors that are off the network
 * path of the client-server communication.
 *
 * @param[out] This will be populated with a new FreeRTOS UDP socket
 * that is bound to a random port.
 *
 * @return Returns #true for successful creation of UDP socket; #false
 * otherwise for failure.
 */
static bool createUdpSocket( Socket_t * pSocket );

/**
 * @brief Utility to close the passed FreeRTOS UDP socket.
 *
 * @param pSocket The UDP socket to close.
 */
static void closeUdpSocket( Socket_t * pSocket );

/**
 * @brief Utility to calculate new poll period with exponential backoff and jitter
 * algorithm.
 *
 * @note The demo applies time polling frequency backoff only when a single time server
 * is configured, through the democonfigLIST_OF_SERVERS macro, and the single server
 * rejects time requests.
 *
 * @param[in, out] pContext The context representing the back-off parameters. This
 * context is initialized by the function whenever the caller indicates it with the
 * @p shouldInitializeContext flag.
 * @param[in] shouldInitializeContext Flag to indicate if the passed context should be
 * initialized to start a new sequence of backed-off time request retries.
 * @param[in] minPollPeriod The minimum poll period
 * @param[in] pPollPeriod The new calculated poll period.
 *
 * @return Return #true if a new poll interval is calculated to retry time request
 * from the server; #false otherwise to indicate exhaustion of time request retry attempts
 * with the server.
 */
static bool calculateBackoffForNextPoll( BackoffAlgorithmContext_t * pContext,
                                         bool shouldInitializeContext,
                                         uint32_t minPollPeriod,
                                         uint32_t * pPollPeriod );

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
                           uint64_t slewRate,
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
        /* Slew Adjustment = Slew Rate ( Milliseconds/seconds )
         *                                      x
         *                   No. of seconds since last synchronization. */
        msElapsedSinceLastSync += slewRate * ( msElapsedSinceLastSync / 1000 );
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

        *pIpV4Addr = FreeRTOS_ntohl( resolvedAddr );

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
                           uint16_t bytesToSend )
{
    struct freertos_sockaddr destinationAddress;
    int32_t bytesSent;

    destinationAddress.sin_addr = FreeRTOS_htonl( serverAddr );
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
                                  uint16_t bytesToRecv )
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
    if( ( bytesReceived > 0 ) && ( ( FreeRTOS_ntohl( sourceAddress.sin_addr ) != serverAddr ) ||
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
                                int64_t clockOffsetMs,
                                SntpLeapSecondInfo_t leapSecondInfo )
{
    /* Note: This demo DOES NOT show adjustment of leap second in system time,
     * if an upcoming leap second adjustment is mentioned in server response.
     * Leap second adjustment occurs at low frequency (only for the last minute of June
     * or December) and can be useful for applications that require smooth system
     * time continuum ALWAYS including the time of the leap second adjustment.
     *
     * For more information on leap seconds, refer to
     * https://www.nist.gov/pml/time-and-frequency-division/leap-seconds-faqs.
     */
    ( void ) leapSecondInfo;

    LogInfo( ( "Received time from time server: %s", pTimeServer->pServerName ) );

    /* Obtain the mutext for accessing system clock variables. */
    xSemaphoreTake( xMutex, portMAX_DELAY );

    /* Always correct the system base time on receiving time from server.*/
    SntpStatus_t status;
    uint32_t unixSecs;
    uint32_t unixMicroSecs;

    /* Convert server time from NTP timestamp to UNIX format. */
    status = Sntp_ConvertToUnixTime( pServerTime,
                                     &unixSecs,
                                     &unixMicroSecs );
    configASSERT( status == SntpSuccess );

    /* Always correct the base time of the system clock as the time received from the server. */
    systemClock.baseTime.secs = unixSecs;
    systemClock.baseTime.msecs = unixMicroSecs / 1000;

    /* Set the clock adjustment "slew" rate of system clock if it wasn't set already and this is NOT
     * the first clock synchronization since device boot-up. */
    if( ( systemClock.firstTimeSyncDone == true ) && ( systemClock.slewRate == 0 ) )
    {
        /* We will use a "slew" correction approach to compensate for system clock
         * drift over poll interval period that exists between consecutive time synchronizations
         * with time server. */

        /* Calculate the "slew" rate for system clock as milliseconds of adjustment needed per second. */
        systemClock.slewRate = clockOffsetMs / systemClock.pollPeriod;
    }

    /* Set the system clock flag that indicates completion of the first time synchronization since device boot-up. */
    if( systemClock.firstTimeSyncDone == false )
    {
        systemClock.firstTimeSyncDone = true;
    }

    /* Store the tick count of the current time synchronization in the system clock. */
    systemClock.lastSyncTickCount = xTaskGetTickCount();

    xSemaphoreGive( xMutex );
}

/**************************** Authentication Utilities and Interface Functions ***********************************************/
static bool populateAuthContextForServer( const char * pServer,
                                          SntpAuthContext_t * pAuthContext )

{
    size_t index = 0;

    /* Look for the server in the list of configured servers to determine the
     * index position of the server so that the server's corresponding information of credentials
     * can be found from democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS and democonfigLIST_OF_AUTHENTICATION_KEY_IDS
     * lists. */
    for( index = 0; index < numOfServers; index++ )
    {
        if( ( strlen( pServer ) == strlen( pTimeServers[ index ] ) ) && ( strncmp( pServer, pTimeServers[ index ], strlen( pServer ) ) == 0 ) )
        {
            /* The records for server in the demo configuration lists have been found. */
            break;
        }
    }

    /* Make sure that record for server has been found. */
    configASSERT( index != numOfServers );

    /* Fill the time server in the authentication context. */
    pAuthContext->pServer = pServer;

    /* Determine if the time server has been configured to use authentication mechanism. */
    if( ( pAESCMACAuthKeys[ index ] != NULL ) && ( pAuthKeyIds[ index ] != -1 ) )
    {
        const char * pKeyHexString = pAESCMACAuthKeys[ index ];

        /* Verify that the configured authentication key is 128 bits or 16 bytes in size. As
         * the input format is a hex string, the string length should be 32 bytes. */
        configASSERT( strlen( pKeyHexString ) == 2 * AES_CMAC_AUTHENTICATION_KEY_SIZE );

        /* Set the key ID in the context. */
        pAuthContext->keyId = pAuthKeyIds[ index ];

        /* Store the configured AES-128-CMAC key for authentication in the SntpAuthContext_t context
         * after converting it from hex string to binary. */
        for( index = 0; index < strlen( pKeyHexString ); index += 2 )
        {
            char byteString[ 3 ] = { pKeyHexString[ index ], pKeyHexString[ index + 1 ], '\0' };
            uint8_t byteVal = strtoul( byteString, NULL, 16 );
            pAuthContext->pAuthKey[ index / 2 ] = byteVal;
        }
    }
    else
    {
        /* No key information has been configured for the time server. Thus, communication with the time
         * server will not use authentication mechanism. */
        memset( pAuthContext->pAuthKey, 0, sizeof( pAuthContext->pAuthKey ) );
        pAuthContext->keyId = -1;
    }
}

static CK_RV setupPkcs11ObjectForAesCmac( const SntpAuthContext_t * pAuthContext,
                                          CK_SESSION_HANDLE * pPkcs11Session,
                                          CK_FUNCTION_LIST_PTR * pFunctionList,
                                          CK_OBJECT_HANDLE * pCmacKey )
{
    CK_RV result;

    static CK_BYTE label[] = pkcs11configLABEL_CMAC_KEY;
    static CK_KEY_TYPE cmacKeyType = CKK_AES;
    static CK_OBJECT_CLASS cmacKeyClass = CKO_SECRET_KEY;
    static CK_BBOOL trueObject = CK_TRUE;

    static CK_ATTRIBUTE aes_cmac_template[] =
    {
        { CKA_CLASS,    &cmacKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &cmacKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    label,         sizeof( label ) - 1       },
        { CKA_TOKEN,    &trueObject,   sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &trueObject,   sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &trueObject,   sizeof( CK_BBOOL )        },
        { CKA_VALUE,    NULL,          0                         }
    };

    /* Update the attributes array with the key of AES-CMAC operation. */
    aes_cmac_template[ 6 ].pValue = pAuthContext->pAuthKey;
    aes_cmac_template[ 6 ].ulValueLen = sizeof( pAuthContext->pAuthKey );

    result = xInitializePkcs11Session( pPkcs11Session );

    if( result != CKR_OK )
    {
        LogError( ( "Failed to open PKCS #11 session." ) );
    }

    if( result == CKR_OK )
    {
        result = C_GetFunctionList( pFunctionList );

        if( result != CKR_OK )
        {
            LogError( ( "Failed to get PKCS #11 function list." ) );
        }
    }

    if( result == CKR_OK )
    {
        /* Create the template objects */
        result = ( *pFunctionList )->C_CreateObject( *pPkcs11Session,
                                                     ( CK_ATTRIBUTE_PTR ) &aes_cmac_template,
                                                     sizeof( aes_cmac_template ) / sizeof( CK_ATTRIBUTE ),
                                                     pCmacKey );

        if( result != CKR_OK )
        {
            LogError( ( "Failed to create AES CMAC object." ) );
        }

        configASSERT( *pCmacKey != CK_INVALID_HANDLE );
    }

    return result;
}

SntpStatus_t addClientAuthCode( SntpAuthContext_t * pAuthContext,
                                const SntpServerInfo_t * pTimeServer,
                                void * pRequestBuffer,
                                uint16_t bufferSize,
                                uint16_t * pAuthCodeSize )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList;
    CK_SESSION_HANDLE pkcs11Session = 0;

    CK_OBJECT_HANDLE cMacKey;
    size_t macBytesWritten = pkcs11AES_CMAC_SIGNATURE_LENGTH;

    CK_MECHANISM mechanism =
    {
        CKM_AES_CMAC, NULL_PTR, 0
    };

    /* Determine whether the authentication context information needs to be updated to match
     * the passed time server that is to be used for querying time.
     * Note: The coreSNTP library will rotate the time server of use for communication to the next
     * in the list if either the time server rejects a time request OR times out in its response to the
     * time request. In such a case of rotating time server, the application (or user of the coreSNTP
     * library) is required to necessary updates to the authentication context to reflect the new
     * time server being used for SNTP communication by the SNTP client.*/
    if( ( strlen( pTimeServer->pServerName ) != strlen( pAuthContext->pServer ) ) ||
        ( strncmp( pTimeServer->pServerName, pAuthContext->pServer, strlen( pAuthContext->pServer ) ) != 0 ) )
    {
        /* Update the authentication context to represent the new time server of usage for
         *  time requests. */
        populateAuthContextForServer( pTimeServer->pServerName, pAuthContext );
    }

    /* Check if the time server supports AES-128-CMAC authentication scheme in communication.
     * If the time server supports authentication, then proceed with operation of generating client
     * authentication code from the SNTP request packet and appending it to the request buffer.  */
    if( pAuthContext->keyId != -1 )
    {
        /* Ensure that the buffer is large enough to hold the "Key Identifier" and "Message Digest" fields
         * for authentication information of the SNTP time request packet. */
        configASSERT( bufferSize >= SNTP_PACKET_AUTHENTICATED_MODE_SIZE );

        result = setupPkcs11ObjectForAesCmac( pAuthContext,
                                              &pkcs11Session,
                                              &functionList,
                                              &cMacKey );

        if( result == CKR_OK )
        {
            /* Test SignInit and Sign */
            result = functionList->C_SignInit( pkcs11Session, &mechanism, cMacKey );

            if( result != CKR_OK )
            {
                LogError( ( "Failed to C_SignInit AES CMAC." ) );
            }
        }

        /* Append the Key ID of the signing key before appending the signature to the buffer. */
        *( uint32_t * ) ( ( uint8_t * ) pRequestBuffer + SNTP_PACKET_SYMMETRIC_KEY_ID_OFFSET ) = FreeRTOS_htonl( pAuthContext->keyId );

        /* Generate the authentication code as the signature of the time request packet
         * with the configured key. */
        if( result == CKR_OK )
        {
            result = functionList->C_Sign( pkcs11Session,
                                           ( CK_BYTE_PTR ) pRequestBuffer,
                                           SNTP_PACKET_BASE_SIZE,
                                           ( CK_BYTE_PTR ) pRequestBuffer + SNTP_PACKET_BASE_SIZE + SNTP_PACKET_SYMMETRIC_KEY_ID_LENGTH,
                                           &macBytesWritten );

            if( result != CKR_OK )
            {
                LogError( ( "Failed to generate client auth code: Failed to generate AES-128-CMAC signature of SNTP request packet." ) );
            }
        }

        /* Close the PKCS #11 session as the AES-CMAC operation is completed. */
        if( result == CKR_OK )
        {
            result = functionList->C_CloseSession( pkcs11Session );
            configASSERT( result == CKR_OK );

            result = functionList->C_Finalize( NULL );
            configASSERT( result == CKR_OK );
        }

        if( result == CKR_OK )
        {
            *pAuthCodeSize = SNTP_PACKET_SYMMETRIC_KEY_ID_LENGTH + pkcs11AES_CMAC_SIGNATURE_LENGTH;
        }
    }
    else
    {
        /* Server has not been configured with authentication key information, thus, no data was appended to the
         * request packet buffer. */
        *pAuthCodeSize = 0;
    }

    return ( result == CKR_OK ) ? SntpSuccess : SntpErrorAuthFailure;
}

SntpStatus_t validateServerAuth( SntpAuthContext_t * pAuthContext,
                                 const SntpServerInfo_t * pTimeServer,
                                 const void * pResponseData,
                                 uint16_t responseSize )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList;
    CK_SESSION_HANDLE pkcs11Session = 0;
    SntpStatus_t returnStatus = SntpSuccess;

    CK_OBJECT_HANDLE cMacKey;
    size_t macBytesWritten = pkcs11AES_CMAC_SIGNATURE_LENGTH;

    CK_MECHANISM mechanism =
    {
        CKM_AES_CMAC, NULL_PTR, 0
    };

    /* The time server information in the authentication context, managed by this demo application, and the
     * pTimeServer parameter, passed by the coreSNTP library, MUST be the same.
     * Note: The addClientAuthCode() function
     * is responsible for updating the authentication context to represent the time server being currently used
     * by the coreSNTP library for time querying. */
    configASSERT( ( strlen( pTimeServer->pServerName ) == strlen( pAuthContext->pServer ) ) &&
                  ( strncmp( pTimeServer->pServerName, pAuthContext->pServer, strlen( pAuthContext->pServer ) ) == 0 ) );

    /* Check if the time server supports AES-128-CMAC authentication scheme in communication.
     * If the time server supports authentication, then proceed with operation of validating server
     * from the authentication code in the response payload.  */
    if( pAuthContext->keyId != -1 )
    {
        /* As the server supports authentication mode of communication, the server response size
         * SHOULD contain the authentication code. */
        configASSERT( responseSize >= ( SNTP_PACKET_AUTHENTICATED_MODE_SIZE ) );

        result = setupPkcs11ObjectForAesCmac( pAuthContext,
                                              &pkcs11Session,
                                              &functionList,
                                              &cMacKey );

        if( result == CKR_OK )
        {
            /* Test SignInit and Sign */
            result = functionList->C_VerifyInit( pkcs11Session, &mechanism, cMacKey );

            if( result != CKR_OK )
            {
                returnStatus = SntpErrorAuthFailure;
                LogError( ( "Failed to C_VerifyInit AES CMAC." ) );
            }
        }
        else
        {
            returnStatus = SntpErrorAuthFailure;
        }

        /* Generate the authentication code as the signature of the time request packet
         * with the configured key. */
        if( result == CKR_OK )
        {
            result = functionList->C_Verify( pkcs11Session,
                                             ( CK_BYTE_PTR ) pResponseData,
                                             SNTP_PACKET_BASE_SIZE,
                                             ( CK_BYTE_PTR ) pResponseData + SNTP_PACKET_SYMMETRIC_KEY_ID_OFFSET + SNTP_PACKET_SYMMETRIC_KEY_ID_LENGTH,
                                             pkcs11AES_CMAC_SIGNATURE_LENGTH );

            if( result != CKR_OK )
            {
                returnStatus = SntpServerNotAuthenticated;
                LogError( ( "Server cannot be validated from received response: AES-128-CMAC signature in response packet does not match expected." ) );
            }
        }

        /* Close the PKCS #11 session as the AES-CMAC operation is completed. */
        if( result == CKR_OK )
        {
            result = functionList->C_CloseSession( pkcs11Session );
            configASSERT( result == CKR_OK );

            result = functionList->C_Finalize( NULL );
            configASSERT( result == CKR_OK );
        }
    }

    return returnStatus;
}


/*************************************************************************************/

static uint32_t generateRandomNumber()
{
    CK_RV pkcs11Status = CKR_OK;
    CK_FUNCTION_LIST_PTR pFunctionList = NULL;
    CK_SESSION_HANDLE session = CK_INVALID_HANDLE;
    uint32_t randomNum = 0;

    /* Get list of functions supported by the PKCS #11 port. */
    pkcs11Status = C_GetFunctionList( &pFunctionList );

    if( pkcs11Status != CKR_OK )
    {
        configASSERT( pFunctionList != NULL );
        LogError( ( "Failed to generate random number. "
                    "PKCS #11 API, C_GetFunctionList, failed." ) );
    }

    if( pkcs11Status == CKR_OK )
    {
        /* Initialize PKCS #11 module and create a new session. */
        pkcs11Status = xInitializePkcs11Session( &session );

        if( pkcs11Status != CKR_OK )
        {
            configASSERT( session != CK_INVALID_HANDLE );

            LogError( ( "Failed to generate random number. "
                        "Failed to initialize PKCS #11 session." ) );
        }
    }

    if( pkcs11Status == CKR_OK )
    {
        if( pFunctionList->C_GenerateRandom( session,
                                             &randomNum,
                                             sizeof( randomNum ) ) != CKR_OK )
        {
            LogError( ( "Failed to generate random number. "
                        "PKCS #11 API, C_GenerateRandom, failed to generate random number." ) );
        }
    }

    if( pkcs11Status == CKR_OK )
    {
        if( pFunctionList->C_CloseSession( session ) != CKR_OK )
        {
            LogError( ( " Failed to close PKCS #11 session after generating random number." ) );
        }
    }

    return randomNum;
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
                                  NetworkContext_t * pUdpContext,
                                  SntpAuthContext_t * pAuthContext )
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
        UdpTransportInterface_t udpTransportIntf;
        SntpAuthenticationInterface_t symmetricKeyAuthIntf;

        for( uint8_t index = 0; index < numOfServers; index++ )
        {
            pServers[ index ].pServerName = pTimeServers[ index ];
            pServers[ index ].port = SNTP_DEFAULT_SERVER_PORT;
        }

        /* Set the UDP transport interface object. */
        udpTransportIntf.pUserContext = pUdpContext;
        udpTransportIntf.sendTo = UdpTransport_Send;
        udpTransportIntf.recvFrom = UdpTransport_Recv;

        /* Set the authentication interface object. */
        symmetricKeyAuthIntf.pAuthContext = pAuthContext;
        symmetricKeyAuthIntf.generateClientAuth = addClientAuthCode;
        symmetricKeyAuthIntf.validateServerAuth = validateServerAuth;

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
                   &symmetricKeyAuthIntf );

        initStatus = true;
    }

    return initStatus;
}

/*-----------------------------------------------------------*/

static bool createUdpSocket( Socket_t * pSocket )
{
    bool status = false;
    struct freertos_sockaddr bindAddress;

    configASSERT( pSocket != NULL );

    /* Call the FreeRTOS+TCP API to create a UDP socket. */
    *pSocket = FreeRTOS_socket( FREERTOS_AF_INET,
                                FREERTOS_SOCK_DGRAM,
                                FREERTOS_IPPROTO_UDP );

    /* Check the socket was created successfully. */
    if( *pSocket == FREERTOS_INVALID_SOCKET )
    {
        /* There was insufficient FreeRTOS heap memory available for the socket
         * to be created. */
        LogError( ( "Failed to create UDP socket for SNTP client due to insufficient memory." ) );
    }
    else
    {
        /* Use a random UDP port for SNTP communication with server for protection against
         * spoofing vulnerability from "network off-path" attackers. */
        uint16_t randomPort = ( generateRandomNumber() % UINT16_MAX );
        bindAddress.sin_port = FreeRTOS_htons( randomPort );

        if( FreeRTOS_bind( *pSocket, &bindAddress, sizeof( bindAddress ) ) == 0 )
        {
            /* The bind was successful. */
            LogDebug( ( "UDP socket has been bound to port %u", randomPort ) );
            status = true;
        }
        else
        {
            LogError( ( "Failed to bind UDP socket to port %u", randomPort ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static void closeUdpSocket( Socket_t * pSocket )
{
    bool status = false;
    struct freertos_sockaddr bindAddress;

    configASSERT( pSocket != NULL );

    FreeRTOS_shutdown( *pSocket, FREERTOS_SHUT_RDWR );

    /* Close the socket again. */
    FreeRTOS_closesocket( *pSocket );
}

/*-----------------------------------------------------------*/

static bool calculateBackoffForNextPoll( BackoffAlgorithmContext_t * pBackoffContext,
                                         bool shouldInitializeContext,
                                         uint32_t minPollPeriod,
                                         uint32_t * pPollPeriod )
{
    uint16_t newPollPeriod = 0U;
    BackoffAlgorithmStatus_t status;

    configASSERT( pBackoffContext != NULL );
    configASSERT( pPollPeriod != NULL );

    if( shouldInitializeContext == true )
    {
        /* Initialize reconnect attempts and interval.*/
        BackoffAlgorithm_InitializeParams( &pBackoffContext,
                                           minPollPeriod,
                                           SNTP_DEMO_POLL_MAX_BACKOFF_DELAY_SEC,
                                           SNTP_DEMO_MAX_SERVER_BACKOFF_RETRIES );
    }

    /* Generate a random number and calculate the new backoff poll period to wait before the next
     * time poll attempt. */
    status = BackoffAlgorithm_GetNextBackoff( &pBackoffContext, generateRandomNumber(), &newPollPeriod );

    if( status == BackoffAlgorithmRetriesExhausted )
    {
        LogError( ( "All backed-off attempts of polling time server have expired: MaxAttempts=%d",
                    SNTP_DEMO_MAX_SERVER_BACKOFF_RETRIES ) );
    }
    else
    {
        /* Store the calculated backoff period as the new poll period. */
        *pPollPeriod = newPollPeriod;
    }

    return( status == BackoffAlgorithmSuccess );
}

/*-----------------------------------------------------------*/

void sntpTask( void * pParameters )
{
    SntpContext_t clientContext;
    bool initStatus = false;
    CK_RV pkcs11Status;

    /* Validate that the configured lists of time servers, authentication keys and key IDs
     * are of the same length. */
    configASSERT( numOfServers == ( sizeof( pAESCMACAuthKeys ) / sizeof( pAESCMACAuthKeys[ 0 ] ) ) );
    configASSERT( numOfServers == sizeof( pAuthKeyIds ) / sizeof( pAuthKeyIds[ 0 ] ) );

    /* Variable representing the SNTP client context. */
    static SntpContext_t context;

    /* Memory for the SNTP packet buffer in the SNTP context. */
    static uint8_t contextBuffer[ SNTP_PACKET_AUTHENTICATED_MODE_SIZE ];

    /* Memory for the network context representing the UDP socket that will be
     * passed to the SNTP client context. */
    static NetworkContext_t udpContext;

    /* Initialize PKCS11 module for cryptographic operations of AES-128-CMAC show
     * shown in this demo for authentication mechanism in SNTP communication with server. */
    pkcs11Status = xInitializePKCS11();
    configASSERT( pkcs11Status == CKR_OK );

    /* Memory for authentication context that will be passed to  the SNTP client context through
     * the authentication interface. This represents a combination of the time server and
     * its authentication key information that will be utilized for authentication communication
     * between client and server, if the server supports authentication. */
    static SntpAuthContext_t authContext;

    /* Context used for calculating backoff that is applied to polling interval when the configured
     * time server rejects time request.
     * Note: Backoff is applied to polling interval ONLY when a single server is configured in the demo
     * because in the case of multiple server configurations, the coreSNTP library handles server
     * rejection by rotating server. */
    static BackoffAlgorithmContext_t backoffContext;

    /* Initialize the authentication context for information for the first time server and its
     * keys configured in the demo. */
    populateAuthContextForServer( pTimeServers[ 0 ], &authContext );

    initStatus = initializeSntpClient( &clientContext,
                                       pTimeServers,
                                       numOfServers,
                                       contextBuffer,
                                       sizeof( contextBuffer ),
                                       &udpContext,
                                       &authContext );

    if( initStatus == true )
    {
        SntpStatus_t status;
        bool backoffModeFlag = false;

        /* Set the polling interval for periodic time synchronization attempts by the SNTP client. */
        systemClock.pollPeriod = democonfigSNTP_CLIENT_POLLING_INTERVAL_SECONDS;

        LogDebug( ( "Minimum SNTP client polling interval calculated as %lus", systemClock.pollPeriod ) );

        LogInfo( ( "Initialized SNTP Client context. Starting SNTP client loop to poll time every %lu seconds",
                   systemClock.pollPeriod ) );

        /* The loop of the SNTP Client task that synchronizes system time with a time server (in the configured list of time servers)
         * periodically at intervals of polling period. Each iteration of time synchronization is performed by calling the coreSNTP
         * APIs for sending time request to the server and receiving time response from the server. */
        while( 1 )
        {
            /* For security, this demo keeps a UDP socket open only for one iteration of SNTP request-response cycle.
             * There is a security risk of a UDP socket being flooded with invalid or malicious server response packets
             * when a UDP socket is kept open across multiple time polling cycles. In such a scenario where the UDP
             * socket buffer has received multiple server response packets from a single time request, the extraneous
             * server response present in the UDP socket buffer will prevent the SNTP client application from correctly
             * reading network data of server responses that correspond to future time requests.
             * By closing the UDP socket after receiving the first acceptable server response (within the server response
             * timeout window), any extraneous or malicious server response packets for the same time request will be
             * ignored by the demo. */

            /* Create a UDP socket for the current iteration of time polling. */
            bool socketStatus = createUdpSocket( &udpContext.socket );
            configASSERT( socketStatus == true );

            status = Sntp_SendTimeRequest( &clientContext, generateRandomNumber(), democonfigSEND_TIME_REQUEST_TIMEOUT_MS );
            configASSERT( status == SntpSuccess );

            /* Wait for server response for a maximum time of server response timeout. */
            do
            {
                /* Attempt to receive server response each time for a smaller block time
                 * than the total duration for the server response to time out. */
                status = Sntp_ReceiveTimeResponse( &clientContext, democonfigRECEIVE_SERVER_RESPONSE_BLOCK_TIME_MS );
            } while( status == SntpNoResponseReceived );

            /* Close the UDP socket irrespective of whether a server response is received. */
            closeUdpSocket( &udpContext.socket );

            /* Apply back-off delay before the next poll iteration if the demo has been configured with only
             * a single time server. */
            if( ( status == SntpRejectedResponse ) && ( numOfServers == 1 ) )
            {
                bool backoffStatus = false;

                /* Determine if this is the first back-off attempt we are making since the most recent server rejection
                 * for time request. */
                bool firstBackoffAttempt = false;

                if( backoffModeFlag == false )
                {
                    firstBackoffAttempt = true;

                    /* Set the flag to indicate we are in back-off retry mode for requesting time from the server. */
                    backoffModeFlag = true;
                }

                LogInfo( ( "The single configured time server, %s, rejected time request. Backing-off before ",
                           "next time poll....", strlen( pTimeServers[ 0 ] ) ) );

                /* Add exponential back-off to polling period. */
                backoffStatus = calculateBackoffForNextPoll( &backoffContext,
                                                             firstBackoffAttempt,
                                                             systemClock.pollPeriod,
                                                             &systemClock.pollPeriod );
                configASSERT( backoffStatus == true );

                /* Wait for the increased poll interval before retrying request for time from server. */
                vTaskDelay( pdMS_TO_TICKS( systemClock.pollPeriod * 1000 ) );
            }
            else
            {
                /* Reset flag to indicate that we are not backing-off for the next time poll. */
                backoffModeFlag = false;

                /* Wait for the poll interval period before the next iteration of time synchronization. */
                vTaskDelay( pdMS_TO_TICKS( systemClock.pollPeriod * 1000 ) );
            }
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
