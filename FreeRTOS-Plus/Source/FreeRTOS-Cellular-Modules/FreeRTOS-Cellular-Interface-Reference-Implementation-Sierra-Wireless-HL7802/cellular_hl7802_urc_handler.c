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

#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Standard includes. */
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include "cellular_types.h"
#include "cellular_common.h"
#include "cellular_common_api.h"
#include "cellular_common_portable.h"

/* Cellular module includes. */
#include "cellular_hl7802.h"

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessKtcpInd( CellularContext_t * pContext,
                                         char * pInputLine );
static void handleTcpNotif( CellularSocketContext_t * pSocketData,
                            uint8_t tcpNotif,
                            uint32_t sessionId );
static void _cellular_UrcProcessKtcpNotif( CellularContext_t * pContext,
                                           char * pInputLine );
static void _cellular_UrcProcessKtcpData( CellularContext_t * pContext,
                                          char * pInputLine );

/*-----------------------------------------------------------*/

/* Try to Keep this map in Alphabetical order. */
/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularAtParseTokenMap_t CellularUrcHandlerTable[] =
{
    { "CEREG",      Cellular_CommonUrcProcessCereg },
    { "CREG",       Cellular_CommonUrcProcessCreg  },
    { "KTCP_DATA",  _cellular_UrcProcessKtcpData   },         /* TCP data URC. */
    { "KTCP_IND",   _cellular_UrcProcessKtcpInd    },         /* TCP status URC. */
    { "KTCP_NOTIF", _cellular_UrcProcessKtcpNotif  }          /* TCP connection failure. */
};

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
uint32_t CellularUrcHandlerTableSize = sizeof( CellularUrcHandlerTable ) / sizeof( CellularAtParseTokenMap_t );

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessKtcpInd( CellularContext_t * pContext,
                                         char * pInputLine )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pLocalInputLine = pInputLine;
    char * pToken = NULL;
    CellularSocketContext_t * pSocketData = NULL;
    uint8_t sessionId = 0;
    uint32_t socketIndex = 0;
    int32_t tempValue = 0;

    if( ( pContext != NULL ) && ( pInputLine != NULL ) )
    {
        /* The inputline is in this format +KTCP_IND: <session_id>, 1
         * This URC indicate connection success. */
        atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= MIN_TCP_SESSION_ID ) && ( tempValue <= MAX_TCP_SESSION_ID ) )
                {
                    sessionId = ( uint8_t ) tempValue;
                    socketIndex = _Cellular_GetSocketId( pContext, sessionId );
                }
                else
                {
                    LogError( ( "error parsing _cellular_UrcProcessKtcpInd session ID" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Call the callback function of this session. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( socketIndex == INVALID_SOCKET_INDEX )
            {
                LogWarn( ( "_cellular_UrcProcessKtcpInd : unknown session data received. "
                           "The session %u may not be closed properly in previous execution.", sessionId ) );
            }
            else
            {
                pSocketData = _Cellular_GetSocketData( pContext, socketIndex );

                if( pSocketData == NULL )
                {
                    LogError( ( "_cellular_UrcProcessKtcpInd : invalid socket index %u", socketIndex ) );
                }
                else if( pSocketData->openCallback == NULL )
                {
                    LogDebug( ( "_cellular_UrcProcessKtcpInd : Open callback not set!!" ) );
                }
                else
                {
                    LogDebug( ( "Notify session %d with socket opened\r\n", sessionId ) );
                    pSocketData->socketState = SOCKETSTATE_CONNECTED;
                    pSocketData->openCallback( CELLULAR_URC_SOCKET_OPENED,
                                               pSocketData, pSocketData->pOpenCallbackContext );
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/

static void handleTcpNotif( CellularSocketContext_t * pSocketData,
                            uint8_t tcpNotif,
                            uint32_t sessionId )
{
    /* Suppress warning message if log level is not debug. */
    ( void ) sessionId;

    switch( tcpNotif )
    {
        case TCP_NOTIF_TCP_DISCONNECTION: /* TCP disconnection by the server or remote client. */

            pSocketData->socketState = SOCKETSTATE_DISCONNECTED;

            if( pSocketData->closedCallback != NULL )
            {
                LogDebug( ( "Notify session %d with socket disconnected\r\n", sessionId ) );
                pSocketData->closedCallback( pSocketData, pSocketData->pClosedCallbackContext );
            }

            break;

        case TCP_NOTIF_TCP_CONNECTION_ERROR: /* TCP connection error. */

            pSocketData->socketState = SOCKETSTATE_DISCONNECTED;

            if( pSocketData->openCallback != NULL )
            {
                LogDebug( ( "Notify session %d with socket open failed\r\n", sessionId ) );
                pSocketData->openCallback( CELLULAR_URC_SOCKET_OPEN_FAILED,
                                           pSocketData, pSocketData->pOpenCallbackContext );
            }

            break;

        default:
            break;
    }
}

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessKtcpNotif( CellularContext_t * pContext,
                                           char * pInputLine )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pLocalInputLine = pInputLine;
    char * pToken = NULL;
    CellularSocketContext_t * pSocketData = NULL;
    uint8_t sessionId = 0;
    tcpConnectionFailure_t tcpNotif = TCP_NOTIF_OK;
    uint32_t socketIndex = 0;
    int32_t tempValue = 0;

    if( ( pContext != NULL ) && ( pInputLine != NULL ) )
    {
        /* The inputline is in this format +KTCP_NOTIF: <session_id>, <tcp_notif>
         * This URC indicate connection problem. */

        /* Remove leading space. */
        atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pLocalInputLine );

        /* Parse the session ID. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= MIN_TCP_SESSION_ID ) && ( tempValue <= MAX_TCP_SESSION_ID ) )
                {
                    sessionId = ( uint8_t ) tempValue;
                    socketIndex = _Cellular_GetSocketId( pContext, sessionId );
                }
                else
                {
                    LogError( ( "error parsing _cellular_UrcProcessKtcpInd session ID" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Parse the tcp notif. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= TCP_NOTIF_OK ) && ( tempValue <= TCP_NOTIF_MAX ) )
                {
                    tcpNotif = ( tcpConnectionFailure_t ) tempValue;
                }
                else
                {
                    LogError( ( "error parsing _cellular_UrcProcessKtcpInd session ID" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Call the callback function of this session. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( socketIndex == INVALID_SOCKET_INDEX )
            {
                LogWarn( ( "_cellular_UrcProcessKtcpNotif : unknown session data received. "
                           "The session %u may not be closed properly in previous execution.", sessionId ) );
            }
            else
            {
                pSocketData = _Cellular_GetSocketData( pContext, socketIndex );

                if( pSocketData == NULL )
                {
                    LogError( ( "_cellular_UrcProcessKtcpNotif : invalid socket index %u", socketIndex ) );
                }
                else
                {
                    handleTcpNotif( pSocketData, tcpNotif, sessionId );
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessKtcpData( CellularContext_t * pContext,
                                          char * pInputLine )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pLocalInputLine = pInputLine;
    char * pToken = NULL;
    CellularSocketContext_t * pSocketData = NULL;
    uint8_t sessionId = 0;
    uint32_t socketIndex = 0;
    int32_t tempValue = 0;

    if( ( pContext != NULL ) && ( pInputLine != NULL ) )
    {
        /* The inputline is in this format +KTCP_DATA: <session_id>, <bytes_received>
         * This URC indicate connection problem. */

        /* parse the session ID. */
        atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= MIN_TCP_SESSION_ID ) && ( tempValue <= MAX_TCP_SESSION_ID ) )
                {
                    sessionId = ( uint8_t ) tempValue;
                    socketIndex = _Cellular_GetSocketId( pContext, sessionId );
                }
                else
                {
                    LogError( ( "error parsing _cellular_UrcProcessKtcpData session ID" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Indicate the upper layer about the data reception. */
        /* Call the callback function of this session. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( socketIndex == INVALID_SOCKET_INDEX )
            {
                LogWarn( ( "_cellular_UrcProcessKtcpData : unknown session data received. "
                           "The session %u may not be closed properly in previous execution.", sessionId ) );
            }
            else
            {
                pSocketData = _Cellular_GetSocketData( pContext, socketIndex );

                if( pSocketData == NULL )
                {
                    LogError( ( "_cellular_UrcProcessKtcpData : invalid socket index %u", socketIndex ) );
                }
                else if( pSocketData->dataReadyCallback == NULL )
                {
                    LogDebug( ( "_cellular_UrcProcessKtcpData : Data ready callback not set!!" ) );
                }
                else
                {
                    pSocketData->dataReadyCallback( pSocketData, pSocketData->pDataReadyCallbackContext );
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/
