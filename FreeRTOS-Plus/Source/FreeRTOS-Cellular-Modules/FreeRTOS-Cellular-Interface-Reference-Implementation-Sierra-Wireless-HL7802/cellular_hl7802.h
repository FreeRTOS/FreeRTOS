/*
 * FreeRTOS-Cellular-Interface v1.3.0
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
 */

#ifndef __CELLULAR_HL7802_H__
#define __CELLULAR_HL7802_H__

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

#define MIN_TCP_SESSION_ID          ( 1U )
#define MAX_TCP_SESSION_ID          ( 6U )
#define TCP_SESSION_TABLE_LEGNTH    ( MAX_TCP_SESSION_ID + 1 )

#define INVALID_SOCKET_INDEX        ( UINT32_MAX )
#define INVALID_SESSION_ID          ( UINT32_MAX )

/* Delay after AT+CFUN=1,1 commands. */
#ifndef CELLULAR_HL7802_RESET_DELAY_MS
    #define CELLULAR_HL7802_RESET_DELAY_MS    ( 3000U )
#endif

/* AT command recommended timeout value for HL7802. Reference HL7802 AT Commands
 * Interface Guide to setup the timeout value for each AT commands. */
#define CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS      ( 2000U )
#define CELLULAR_HL7802_AT_TIMEOUT_5_SECONDS_MS      ( 5000U )
#define CELLULAR_HL7802_AT_TIMEOUT_30_SECONDS_MS     ( 30000U )
#define CELLULAR_HL7802_AT_TIMEOUT_60_SECONDS_MS     ( 60000U )
#define CELLULAR_HL7802_AT_TIMEOUT_120_SECONDS_MS    ( 120000U )

/* Define the following timeout value since they are content dependent or no recommended value. */
#ifndef CELLULAR_HL7802_AT_KSELACQ_TIMEOUT_MS
    #define CELLULAR_HL7802_AT_KSELACQ_TIMEOUT_MS    CELLULAR_HL7802_AT_TIMEOUT_5_SECONDS_MS
#endif

#ifndef CELLULAR_HL7802_AT_KEDRXCFG_TIMEOUT_MS
    #define CELLULAR_HL7802_AT_KEDRXCFG_TIMEOUT_MS    CELLULAR_HL7802_AT_TIMEOUT_5_SECONDS_MS
#endif

#ifndef CELLULAR_HL7802_AT_KCNXUP_TIMEOUT_MS
    #define CELLULAR_HL7802_AT_KCNXUP_TIMEOUT_MS    CELLULAR_HL7802_AT_TIMEOUT_30_SECONDS_MS
#endif

#ifndef CELLULAR_HL7802_AT_KCNXDOWN_TIMEOUT_MS
    #define CELLULAR_HL7802_AT_KCNXDOWN_TIMEOUT_MS    CELLULAR_HL7802_AT_TIMEOUT_30_SECONDS_MS
#endif

/* Band configuration for HL7802. */
#ifndef CELLULAR_CONFIG_HL7802_CATM1_BAND
    /* Default enable all bands. */
    #define CELLULAR_CONFIG_HL7802_CATM1_BAND    "0002000000000F0F1B9F"
#endif

#ifndef CELLULAR_CONFIG_HL7802_NBIOT_BAND
    /* Default enable all bands. */
    #define CELLULAR_CONFIG_HL7802_NBIOT_BAND    "0002000000000B0F189F"
#endif

/*-----------------------------------------------------------*/

typedef struct cellularModuleContext
{
    uint32_t pSessionMap[ TCP_SESSION_TABLE_LEGNTH ];
} cellularModuleContext_t;

typedef enum tcpSocketState
{
    TCP_SOCKET_STATE_NOT_DEFINED = 0,
    TCP_SOCKET_STATE_DEFINED_BUT_NOT_USED = 1,
    TCP_SOCKET_STATE_OPENING_AND_CONNECTING = 2,
    TCP_SOCKET_STATE_CONNECTION_UP = 3,
    TCP_SOCKET_STATE_CONNECTION_CLOSING = 4,
    TCP_SOCKET_STATE_CLOSED = 5,
    TCP_SOCKET_STATE_MAX
} tcpSocketState_t;

typedef enum tcpConnectionFailure
{
    TCP_NOTIF_OK = -1,
    TCP_NOTIF_NETWORK_ERROR = 0,
    TCP_NOTIF_NO_MORE_SOCKETS_AVAILABLE = 1,
    TCP_NOTIF_MEMORY_PROBLEM = 2,
    TCP_NOTIF_DNS_ERROR = 3,
    TCP_NOTIF_TCP_DISCONNECTION = 4,
    TCP_NOTIF_TCP_CONNECTION_ERROR = 5,
    TCP_NOTIF_GENERIC_ERROR = 6,
    TCP_NOTIF_FAIL_TO_ACCEPT_CLIENT_REQUEST = 7,
    TCP_NOTIF_KTCPSND_WAITING_FOR_MORE_OR_LESS_CHARACTERS = 8,
    TCP_NOTIF_BAD_SESSION_ID = 9,
    TCP_NOTIF_SESSION_IS_ALREADY_RUNNING = 10,
    TCP_NOTIF_ALL_SESSIONS_ARE_USED = 11,
    TCP_NOTIF_SOCKET_CONNECTION_TIMEOUT_ERROR = 12,
    TCP_NOTIF_SSL_CONNECTION_ERROR = 13,
    TCP_NOTIF_SSL_INITIALIZATION_ERROR = 14,
    TCP_NOTIF_MAX,
} tcpConnectionFailure_t;

/*-----------------------------------------------------------*/

uint32_t _Cellular_GetSocketId( CellularContext_t * pContext,
                                uint8_t sessionId );

uint32_t _Cellular_GetSessionId( CellularContext_t * pContext,
                                 uint32_t socketIndex );

/*-----------------------------------------------------------*/

extern CellularAtParseTokenMap_t CellularUrcHandlerTable[];
extern uint32_t CellularUrcHandlerTableSize;

extern const char * CellularSrcTokenErrorTable[];
extern uint32_t CellularSrcTokenErrorTableSize;

extern const char * CellularSrcTokenSuccessTable[];
extern uint32_t CellularSrcTokenSuccessTableSize;

extern const char * CellularUrcTokenWoPrefixTable[];
extern uint32_t CellularUrcTokenWoPrefixTableSize;

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef __CELLULAR_HL7802_H__ */
