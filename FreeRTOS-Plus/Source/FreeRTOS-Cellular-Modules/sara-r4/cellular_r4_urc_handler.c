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

#include "cellular_platform.h"
#include "cellular_types.h"
#include "cellular_common.h"
#include "cellular_common_api.h"
#include "cellular_common_portable.h"

/* Cellular module includes. */
#include "cellular_r4.h"

/*-----------------------------------------------------------*/

/* +UUPSMR URC */
#define PSM_MODE_EXIT                  ( 0U )
#define PSM_MODE_ENTER                 ( 1U )
#define PSM_MODE_PREVENT_ENTRY         ( 2U )
#define PSM_MODE_PREVENT_DEEP_ENTRY    ( 3U )

/* +CIEV URC */
#define CIEV_POS_MIN                   ( 1U )
#define CIEV_POS_SIGNAL                ( 2U )
#define CIEV_POS_SERVICE               ( 3U )
#define CIEV_POS_CALL                  ( 6U )
#define CIEV_POS_MAX                   ( 12U )

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessUusoco( CellularContext_t * pContext,
                                        char * pInputLine );
static void _cellular_UrcProcessUusord( CellularContext_t * pContext,
                                        char * pInputLine );
static void _cellular_UrcProcessUusocl( CellularContext_t * pContext,
                                        char * pInputLine );

static void _cellular_UrcProcessUupsmr( CellularContext_t * pContext,
                                        char * pInputLine );
static void _cellular_UrcProcessCiev( CellularContext_t * pContext,
                                      char * pInputLine );
static void _Cellular_ProcessModemRdy( CellularContext_t * pContext,
                                       char * pInputLine );
static CellularPktStatus_t _parseUrcIndicationCsq( CellularContext_t * pContext,
                                                   char * pUrcStr );
static void _Cellular_UrcProcessCereg( CellularContext_t * pContext,
                                       char * pInputLine );
static void _Cellular_UrcProcessCgreg( CellularContext_t * pContext,
                                       char * pInputLine );
static void _Cellular_UrcProcessCreg( CellularContext_t * pContext,
                                      char * pInputLine );

/*-----------------------------------------------------------*/

/* Try to Keep this map in Alphabetical order. */
/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularAtParseTokenMap_t CellularUrcHandlerTable[] =
{
    { "CEREG",  _Cellular_UrcProcessCereg  },
    { "CGREG",  _Cellular_UrcProcessCgreg  },
    /*{ "CGEV",   _cellular_UrcProcessCgev     },                 / * TODO: PS event reporting URC. * / */
    { "CIEV",   _cellular_UrcProcessCiev   }, /* PS ACT/DEACT and Signal strength status change indication URC. */
    { "CREG",   _Cellular_UrcProcessCreg   },
    { "RDY",    _Cellular_ProcessModemRdy  }, /* Modem bootup indication. */
    { "UUPSMR", _cellular_UrcProcessUupsmr }, /* Power saving mode indication URC. */
    { "UUSOCL", _cellular_UrcProcessUusocl }, /* Socket close URC. */
    { "UUSOCO", _cellular_UrcProcessUusoco }, /* Socket connect URC. */
    { "UUSORD", _cellular_UrcProcessUusord } /* Socket receive URC. */
};

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
uint32_t CellularUrcHandlerTableSize = sizeof( CellularUrcHandlerTable ) / sizeof( CellularAtParseTokenMap_t );

/*-----------------------------------------------------------*/

/* Parse PS ACT/DEACT from +CIEV URC indication. */
/* This URC does not tell which context ID number is ACT/DEACT. */

static CellularPktStatus_t _parseUrcIndicationCall( const CellularContext_t * pContext,
                                                    char * pUrcStr )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    int32_t isActivated = 0;
    /* In SARA-R4, usually context 1 is used for PS. */
    uint8_t contextId = 1;

    if( ( pContext == NULL ) || ( pUrcStr == NULL ) )
    {
        atCoreStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( pUrcStr, 10, &isActivated );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( ( isActivated >= INT16_MIN ) && ( isActivated <= ( int32_t ) INT16_MAX ) )
        {
            LogDebug( ( "_parseUrcIndicationCall: PS status isActivated=[%d]", isActivated ) );

            /* Handle the callback function. */
            if( isActivated )
            {
                LogDebug( ( "_parseUrcIndicationCall: PDN activated. Context Id %d", contextId ) );
                _Cellular_PdnEventCallback( pContext, CELLULAR_URC_EVENT_PDN_ACTIVATED, contextId );
            }
            else
            {
                LogDebug( ( "_parseUrcIndicationCall: PDN deactivated. Context Id %d", contextId ) );
                _Cellular_PdnEventCallback( pContext, CELLULAR_URC_EVENT_PDN_DEACTIVATED, contextId );
            }
        }
        else
        {
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    if( atCoreStatus != CELLULAR_AT_SUCCESS )
    {
        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/* Parse signal level from +CIEV URC indication. */
/* This URC only gives bar level and not the exact RSSI value. */

static CellularPktStatus_t _parseUrcIndicationCsq( CellularContext_t * pContext,
                                                   char * pUrcStr )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    int32_t retStrtoi = 0;
    int16_t csqBarLevel = CELLULAR_INVALID_SIGNAL_BAR_VALUE;
    CellularSignalInfo_t signalInfo = { 0 };

    if( ( pContext == NULL ) || ( pUrcStr == NULL ) )
    {
        atCoreStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( pUrcStr, 10, &retStrtoi );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( ( retStrtoi >= INT16_MIN ) && ( retStrtoi <= ( int32_t ) INT16_MAX ) )
        {
            csqBarLevel = retStrtoi;
        }
        else
        {
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    /* Handle the callback function. */
    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        LogDebug( ( "_parseUrcIndicationCsq: SIGNAL Strength Bar level [%d]", csqBarLevel ) );
        signalInfo.rssi = CELLULAR_INVALID_SIGNAL_VALUE;
        signalInfo.rsrp = CELLULAR_INVALID_SIGNAL_VALUE;
        signalInfo.rsrq = CELLULAR_INVALID_SIGNAL_VALUE;
        signalInfo.ber = CELLULAR_INVALID_SIGNAL_VALUE;
        signalInfo.bars = csqBarLevel;
        _Cellular_SignalStrengthChangedCallback( pContext, CELLULAR_URC_EVENT_SIGNAL_CHANGED, &signalInfo );
    }

    if( atCoreStatus != CELLULAR_AT_SUCCESS )
    {
        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessCiev( CellularContext_t * pContext,
                                      char * pInputLine )
{
    char * pUrcStr = NULL, * pToken = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    int32_t tempValue = 0;
    uint8_t indicatorDescr = 0;

    /* Check context status. */
    if( pContext == NULL )
    {
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( pInputLine == NULL )
    {
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pUrcStr = pInputLine;
        atCoreStatus = Cellular_ATRemoveAllDoubleQuote( pUrcStr );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pUrcStr );
        }

        /* Extract indicator <descr> */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pUrcStr, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= ( ( int32_t ) CIEV_POS_MIN ) ) && ( tempValue <= ( ( int32_t ) CIEV_POS_MAX ) ) )
                {
                    indicatorDescr = ( uint8_t ) tempValue;

                    switch( indicatorDescr )
                    {
                        case CIEV_POS_SIGNAL:
                            LogDebug( ( "_cellular_UrcProcessCiev: CIEV_POS_SIGNAL" ) );
                            /* This URC only gives bar level and not the exact RSSI value. */

                            /*
                             *  o 0: < -105 dBm
                             *  o 1 : < -93 dBm
                             *  o 2 : < -81 dBm
                             *  o 3 : < -69 dBm
                             *  o 4 : < -57 dBm
                             *  o 5 : >= -57 dBm
                             */
                            /* Parse the signal Bar level from string. */
                            pktStatus = _parseUrcIndicationCsq( pContext, pUrcStr );
                            break;

                        case CIEV_POS_CALL:
                            LogDebug( ( "_cellular_UrcProcessCiev: CIEV_POS_CALL" ) );
                            /* Parse PS ACT/DEACT from +CIEV URC indication. */
                            /* This URC does not tell which context ID number is ACT/DEACT. */
                            pktStatus = _parseUrcIndicationCall( ( const CellularContext_t * ) pContext, pUrcStr );
                            break;

                        default:
                            break;
                    }
                }
                else
                {
                    LogError( ( "_cellular_UrcProcessCiev: parsing <descr> failed" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        if( atCoreStatus != CELLULAR_AT_SUCCESS )
        {
            pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
        }
    }

    if( pktStatus != CELLULAR_PKT_STATUS_OK )
    {
        LogDebug( ( "_cellular_UrcProcessCiev: Parse failure" ) );
    }
}

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessUupsmr( CellularContext_t * pContext,
                                        char * pInputLine )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pLocalInputLine = pInputLine;
    char * pToken = NULL;
    uint8_t psmState = 0;
    int32_t tempValue = 0;

    if( ( pContext != NULL ) && ( pInputLine != NULL ) )
    {
        /* The inputline is in this format +UUPSMR: <state>[,<param1>] */
        atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= ( ( int32_t ) PSM_MODE_EXIT ) ) && ( tempValue <= ( ( int32_t ) PSM_MODE_PREVENT_DEEP_ENTRY ) ) )
                {
                    psmState = ( uint8_t ) tempValue;

                    switch( psmState )
                    {
                        case PSM_MODE_EXIT:
                            LogInfo( ( "_cellular_UrcProcessUupsmr: PSM_MODE_EXIT" ) );
                            break;

                        case PSM_MODE_ENTER:
                            LogInfo( ( "_cellular_UrcProcessUupsmr: PSM_MODE_ENTER event received" ) );
                            /* Call the callback function. Indicate the upper layer about the PSM state change. */
                            _Cellular_ModemEventCallback( pContext, CELLULAR_MODEM_EVENT_PSM_ENTER );
                            break;

                        case PSM_MODE_PREVENT_ENTRY:
                            LogInfo( ( "_cellular_UrcProcessUupsmr: PSM_MODE_PREVENT_ENTRY" ) );
                            break;

                        case PSM_MODE_PREVENT_DEEP_ENTRY:
                            LogInfo( ( "_cellular_UrcProcessUupsmr: PSM_MODE_PREVENT_DEEP_ENTRY" ) );
                            break;
                    }
                }
                else
                {
                    LogError( ( "_cellular_UrcProcessUupsmr: parsing <state> failed" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessUusoco( CellularContext_t * pContext,
                                        char * pInputLine )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pLocalInputLine = pInputLine;
    char * pToken = NULL;
    CellularSocketContext_t * pSocketData = NULL;
    uint8_t sessionId = 0;
    uint8_t socketError = 0;
    uint32_t socketIndex = 0;
    int32_t tempValue = 0;

    if( ( pContext != NULL ) && ( pInputLine != NULL ) )
    {
        /* The inputline is in this format +UUSOCO: <socket>,<socket_error>
         * socket_error = 0 : no error, others : error. */
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
                    LogError( ( "parsing _cellular_UrcProcessKtcpInd session ID failed" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) && ( tempValue <= UINT8_MAX ) )
                {
                    socketError = ( uint8_t ) tempValue;
                }
                else
                {
                    LogError( ( "parsing _cellular_UrcProcessUusoco socket error failed" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Call the callback function of this session. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            pSocketData = _Cellular_GetSocketData( pContext, socketIndex );

            if( pSocketData == NULL )
            {
                LogError( ( "_cellular_UrcProcessUusoco : invalid socket index %u", socketIndex ) );
            }
            else
            {
                if( socketError == 0 )
                {
                    pSocketData->socketState = SOCKETSTATE_CONNECTED;
                    LogDebug( ( "Notify session %d with socket opened\r\n", sessionId ) );

                    if( pSocketData->openCallback != NULL )
                    {
                        pSocketData->openCallback( CELLULAR_URC_SOCKET_OPENED,
                                                   pSocketData, pSocketData->pOpenCallbackContext );
                    }
                }
                else
                {
                    if( pSocketData->openCallback != NULL )
                    {
                        pSocketData->openCallback( CELLULAR_URC_SOCKET_OPEN_FAILED,
                                                   pSocketData, pSocketData->pOpenCallbackContext );
                    }
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessUusord( CellularContext_t * pContext,
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
        /* The inputline is in this format +UUSOCO: <socket>,<data_length> */
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
                    LogError( ( "parsing _cellular_UrcProcessUusord session ID failed" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Skip data length. */

        /* Call the callback function of this session. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( socketIndex == INVALID_SOCKET_INDEX )
            {
                LogWarn( ( "_cellular_UrcProcessUusord : unknown session data received. "
                           "The session %u may not be closed properly in previous execution.", sessionId ) );
            }
            else
            {
                pSocketData = _Cellular_GetSocketData( pContext, socketIndex );

                if( pSocketData == NULL )
                {
                    LogError( ( "_cellular_UrcProcessUusord : invalid socket index %d", socketIndex ) );
                }
                else
                {
                    /* Indicate the upper layer about the data reception. */
                    if( pSocketData->dataReadyCallback != NULL )
                    {
                        pSocketData->dataReadyCallback( pSocketData, pSocketData->pDataReadyCallbackContext );
                    }
                    else
                    {
                        LogDebug( ( "_cellular_UrcProcessUusord: Data ready callback not set!!" ) );
                    }
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/

static void _cellular_UrcProcessUusocl( CellularContext_t * pContext,
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
        /* The inputline is in this format +UUSOCL: <socket> */
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
                    LogError( ( "parsing _cellular_UrcProcessUusocl session ID failed" ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Call the callback function of this session. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( socketIndex == INVALID_SOCKET_INDEX )
            {
                LogWarn( ( "_cellular_UrcProcessUusocl : unknown session closed URC received. "
                           "The session %u may not be closed properly in previous execution.", sessionId ) );
            }
            else
            {
                pSocketData = _Cellular_GetSocketData( pContext, socketIndex );

                if( pSocketData == NULL )
                {
                    LogError( ( "_cellular_UrcProcessUusocl : invalid socket index %d", socketIndex ) );
                }
                else
                {
                    /* Change the socket state to disconnected. */
                    pSocketData->socketState = SOCKETSTATE_DISCONNECTED;

                    /* Indicate the upper layer about the data reception. */
                    if( pSocketData->closedCallback != NULL )
                    {
                        pSocketData->closedCallback( pSocketData, pSocketData->pClosedCallbackContext );
                    }
                    else
                    {
                        LogDebug( ( "_cellular_UrcProcessUusord: Data ready callback not set!!" ) );
                    }
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/

/* Modem bootup indication. */

static void _Cellular_ProcessModemRdy( CellularContext_t * pContext,
                                       char * pInputLine )
{
    /* The token is the pInputLine. No need to process the pInputLine. */
    ( void ) pInputLine;

    if( pContext == NULL )
    {
        LogWarn( ( "_Cellular_ProcessModemRdy: Context not set" ) );
    }
    else
    {
        LogDebug( ( "_Cellular_ProcessModemRdy: Modem Ready event received" ) );
        _Cellular_ModemEventCallback( pContext, CELLULAR_MODEM_EVENT_BOOTUP_OR_REBOOT );
    }
}

/*-----------------------------------------------------------*/

static void _Cellular_UrcProcessCereg( CellularContext_t * pContext,
                                       char * pInputLine )
{
    ( void ) Cellular_CommonUrcProcessCereg( pContext, pInputLine );
}

/*-----------------------------------------------------------*/

static void _Cellular_UrcProcessCgreg( CellularContext_t * pContext,
                                       char * pInputLine )
{
    ( void ) Cellular_CommonUrcProcessCgreg( pContext, pInputLine );
}

/*-----------------------------------------------------------*/

static void _Cellular_UrcProcessCreg( CellularContext_t * pContext,
                                      char * pInputLine )
{
    ( void ) Cellular_CommonUrcProcessCreg( pContext, pInputLine );
}

/*-----------------------------------------------------------*/
