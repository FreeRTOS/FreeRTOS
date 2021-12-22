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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef DEMO_CONFIG_H
#define DEMO_CONFIG_H

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Include logging header files and define logging macros in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for DEMO.
 * 3. Include the header file "logging_stack.h", if logging is enabled for DEMO.
 */

#include "logging_levels.h"

/* Logging configuration for the Demo. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "SNTPDemo"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

/* Prototype for the function used to print to console on Windows simulator
 * of FreeRTOS.
 * The function prints to the console before the network is connected;
 * then a UDP port after the network has connected. */
extern void vLoggingPrintf( const char * pcFormatString,
                            ... );

/* Map the SdkLog macro to the logging function to enable logging
 * on Windows simulator. */
#ifndef SdkLog
    #define SdkLog( message )    vLoggingPrintf message
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief The time period between consecutive time polling requests that are sent by the
 * SNTP client in the demo application.
 *
 * @note According to the SNTPv4 specification, the polling interval MUST NOT be less
 * than 15 seconds for responsible use of time servers by SNTP clients.
 * 
 * 
 * #define democonfigSNTP_CLIENT_POLLING_INTERVAL_SECONDS                  ( 16 )
 */

/**
 * @brief The set of time servers, in decreasing order of priority, for configuring the SNTP client.
 * The servers SHOULD be listed as comma-separated list of strings. For example, the following
 * can be a configuration used:
 *
 * #define democonfigLIST_OF_TIME_SERVERS          "<custom-timeserver-1>", "<custom-timeserver-2>", "pool.ntp.org"
 */

/**
 * @brief The list of 128-bit (or 16 bytes) symmetric keys for authenticating communication with the NTP/SNTP time servers
 * corresponding to the list in democonfigLIST_OF_TIME_SERVERS. A symmetric key is used for generating authentication code
 * in client request to related NTP/SNTP server as well as validating server from the time response received.
 *
 * This demo shows use of AES-128-CMAC algorithm for a mutual authentication mechanism in the SNTP communication
 * between the NTP/SNTP server and client. The demo generates a Message Authentication Code (MAC) using
 * the algorithm and appends it to the client request packet before the coreSNTP library sends it over
 * the network to the server. The server validates the client from the request from the authentication code
 * present in the request packet. Similarly, this demo validates the server from the response received on
 * the network by verifying the authentication code present in the response packet.
 *
 * It is RECOMMENDED to use an authentication mechanism for protecting devices against server spoofing
 * attacks.
 *
 * @note Even though this demo shows the use of AES-128-CMAC, a symmetric-key cryptographic based
 * solution, for authenticating SNTP communication between the demo (SNTP client) and
 * SNTP/NTP server, we instead RECOMMEND that production devices use the most secure authentication
 * mechanism alternative available with the Network Time Security (NTS) protocol, an asymmetric-key
 * cryptographic protocol. For more information, refer to the NTS specification here:
 * https://datatracker.ietf.org/doc/html/rfc8915
 *
 * @note Please provide the 128-bit keys as comma separated list of hexadecimal strings in the order matching
 * the list of time servers configured in democonfigLIST_OF_TIME_SERVERS configuration. If a time server does
 * not support authentication, then NULL should be used to indicate use of no authentication mechanism for the
 * time server.
 *
 * @note Use of the AES-128-CMAC based authentication scheme in the demo requires that the symmetric key
 * is shared safely between the time server and the client device.
 *
 * #define democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS  "<hexstring-key-1>", "<hexstring-key-2>", NULL
 */

/**
 * @brief The list of key IDs of the shared @ref democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS keys between
 * the client and the corresponding NTP/SNTP servers, in democonfigLIST_OF_TIME_SERVERS, for authenticating
 * the SNTP communication between the client and server.
 *
 * The ID for a key usually represents the ID used to reference the symmetric key in the NTP/SNTP server system.
 *
 * @note This Key IDs should be configured as a comma-separated list of integer Key IDs that match the order of
 * keys in democonfigLIST_OF_AUTHENTICATION_SYMMETRIC_KEYS. If there is a NULL (or no key) in the list of keys,
 * then -1 can be used as the corresponding key ID.
 *
 * #define democonfigLIST_OF_AUTHENTICATION_KEY_IDS    <key-ID-1>, <key-ID-2>, -1
 */

/**
 * @brief The year to bake in the demo application for initializing the system clock with.
 * The demo initializes the system clock time for the starting second of the 1st January of
 * the configured year. So for example, with a configuration of year 2021, the demo will
 * initialize the system clock time as 1st January 2021 00h:00m:00s.
 *
 * @note The coreSNTP library REQUIRES that the client system time is within ~68 years of internet
 * time. Thus, for systems that do not have an Real-Time Clock module, this demo shows how
 * a starting time can be baked in the device firmware to keep the starting time of the system
 * close to actual time on the first boot-up of device.
 * For such systems without Real-Time Clock module, all device boot ups from subsequent device resets
 * or power cycles can continue to carry close to correct time by EITHER
 *  * (RECOMMENDED) Saving the most recent time in non-volatile memory
 *     OR
 *  * Using the same firmware baked-in starting time of device for every boot-up.
 */
#define democonfigSYSTEM_START_YEAR                        ( 2021 )

/**
 * @brief The timeout (in milliseconds) for the time response to a time request made to a
 * time server.
 */
#define democonfigSERVER_RESPONSE_TIMEOUT_MS               ( 5000 )

/**
 * @brief The maximum block time (in milliseconds) for an attempt to send time request over the network
 * to a time server when through the Sntp_SendTimeRequest API.
 */
#define democonfigSEND_TIME_REQUEST_TIMEOUT_MS             ( 50 )

/**
 * @brief The maximum block time (in milliseconds) for an attempt to read server response (to a time request)
 * from the network through the Sntp_ReceiveTimeResponse API.
 *
 * @note This value MAY BE less than the server response timeout (configured in democonfigSERVER_RESPONSE_TIMEOUT_MS)
 * to support use-cases when application DOES NOT want to block for the entire server response timeout period.
 * In such a case, the Sntp_ReceiveTimeResponse API can be called multiple times (with block time duration
 * that is orders of degree shorter than the response timeout value) to check whether an expected server response
 * has been received as well as performing other application logic in the same thread context.
 */
#define democonfigRECEIVE_SERVER_RESPONSE_BLOCK_TIME_MS    ( 200 )

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE                           configMINIMAL_STACK_SIZE


#endif /* DEMO_CONFIG_H */
