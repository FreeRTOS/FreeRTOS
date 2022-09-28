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

#include <stdint.h>

#include "cellular_platform.h"
#include "cellular_common.h"
#include "cellular_common_portable.h"
#include "cellular_r4.h"

/*-----------------------------------------------------------*/

#define ENBABLE_MODULE_UE_RETRY_COUNT         ( 3U )
#define ENBABLE_MODULE_UE_RETRY_TIMEOUT       ( 5000U )
#define ENBABLE_MODULE_UE_REBOOT_POLL_TIME    ( 2000U )
#define ENBABLE_MODULE_UE_REBOOT_MAX_TIME     ( 25000U )

/*-----------------------------------------------------------*/

static CellularError_t sendAtCommandWithRetryTimeout( CellularContext_t * pContext,
                                                      const CellularAtReq_t * pAtReq );

/*-----------------------------------------------------------*/

static cellularModuleContext_t cellularHl7802Context = { 0 };

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
const char * CellularSrcTokenErrorTable[] =
{ "ERROR", "BUSY", "NO CARRIER", "NO ANSWER", "NO DIALTONE", "ABORTED", "+CMS ERROR", "+CME ERROR", "SEND FAIL" };
/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
uint32_t CellularSrcTokenErrorTableSize = sizeof( CellularSrcTokenErrorTable ) / sizeof( char * );

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
const char * CellularSrcTokenSuccessTable[] =
{ "OK", "@" };
/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
uint32_t CellularSrcTokenSuccessTableSize = sizeof( CellularSrcTokenSuccessTable ) / sizeof( char * );

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
const char * CellularUrcTokenWoPrefixTable[] =
{ "RDY" };
/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
uint32_t CellularUrcTokenWoPrefixTableSize = sizeof( CellularUrcTokenWoPrefixTable ) / sizeof( char * );

/*-----------------------------------------------------------*/

static CellularError_t sendAtCommandWithRetryTimeout( CellularContext_t * pContext,
                                                      const CellularAtReq_t * pAtReq )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    uint8_t tryCount = 0;

    if( pAtReq == NULL )
    {
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        for( ; tryCount < ENBABLE_MODULE_UE_RETRY_COUNT; tryCount++ )
        {
            pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, *pAtReq, ENBABLE_MODULE_UE_RETRY_TIMEOUT );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

            if( cellularStatus == CELLULAR_SUCCESS )
            {
                break;
            }
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_ModuleInit( const CellularContext_t * pContext,
                                     void ** ppModuleContext )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    uint32_t i = 0;

    if( pContext == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else if( ppModuleContext == NULL )
    {
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Initialize the module context. */
        ( void ) memset( &cellularHl7802Context, 0, sizeof( cellularModuleContext_t ) );

        for( i = 0; i < TCP_SESSION_TABLE_LEGNTH; i++ )
        {
            cellularHl7802Context.pSessionMap[ i ] = INVALID_SOCKET_INDEX;
        }

        *ppModuleContext = ( void * ) &cellularHl7802Context;
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_ModuleCleanUp( const CellularContext_t * pContext )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    if( pContext == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* Parse AT response for current MNO profile */
static CellularPktStatus_t _Cellular_RecvFuncGetCurrentMNOProfile( CellularContext_t * pContext,
                                                                   const CellularATCommandResponse_t * pAtResp,
                                                                   void * pData,
                                                                   uint16_t dataLen )
{
    char * pInputLine = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    MNOProfileType_t * pCurrentMNOProfile = ( MNOProfileType_t * ) pData;
    char * pToken = NULL;
    int32_t tempValue = 0;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_RecvFuncGetCurrentMNOProfile: Invalid handle" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pData == NULL ) || ( dataLen != sizeof( MNOProfileType_t ) ) )
    {
        LogError( ( "_Cellular_RecvFuncGetCurrentMNOProfile: Invalid param" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "_Cellular_RecvFuncGetCurrentMNOProfile: Input Line passed is NULL" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else
    {
        pInputLine = pAtResp->pItm->pLine;

        /* Remove prefix. */
        atCoreStatus = Cellular_ATRemovePrefix( &pInputLine );

        /* Remove leading space. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pInputLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

                if( atCoreStatus == CELLULAR_AT_SUCCESS )
                {
                    if( ( tempValue >= MNO_PROFILE_SW_DEFAULT ) && ( tempValue <= MNO_PROFILE_STANDARD_EUROPE ) )
                    {
                        *pCurrentMNOProfile = tempValue;
                        LogInfo( ( "_Cellular_RecvFuncGetCurrentMNOProfile: pCurrentMNOProfile [%d]", *pCurrentMNOProfile ) );
                    }
                }
                else
                {
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/
/* Get modem's current MNO profile */
static CellularError_t _Cellular_GetCurrentMNOProfile( CellularContext_t * pContext,
                                                       MNOProfileType_t * pCurrentMNOProfile )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetCurrentMNOProfile =
    {
        "AT+UMNOPROF?",
        CELLULAR_AT_WITH_PREFIX,
        "+UMNOPROF",
        _Cellular_RecvFuncGetCurrentMNOProfile,
        NULL,
        sizeof( MNOProfileType_t ),
    };

    atReqGetCurrentMNOProfile.pData = pCurrentMNOProfile;

    /* Internal function. Callee check parameters. */
    pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetCurrentMNOProfile );
    cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* Reboot modem and wait for ready state. */

CellularError_t rebootCellularModem( CellularContext_t * pContext,
                                     bool disablePsm,
                                     bool disableEidrx )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    uint32_t count = 0;

    CellularAtReq_t atReqGetNoResult =
    {
        "AT+CFUN=15",
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0
    };

    LogInfo( ( "rebootCellularModem: Rebooting Modem." ) );
    cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
    Platform_Delay( ENBABLE_MODULE_UE_REBOOT_POLL_TIME );
    count = count + ENBABLE_MODULE_UE_REBOOT_POLL_TIME;

    /* wait for modem after reboot*/
    while( count < ENBABLE_MODULE_UE_REBOOT_MAX_TIME )
    {
        LogInfo( ( "rebootCellularModem: Use ATE0 command to test modem status." ) );

        atReqGetNoResult.pAtCmd = "ATE0";

        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqGetNoResult, ENBABLE_MODULE_UE_REBOOT_POLL_TIME );
        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            LogInfo( ( "rebootCellularModem: Modem is now available." ) );

            Platform_Delay( ENBABLE_MODULE_UE_REBOOT_POLL_TIME * 3 );

            /* Query current PSM settings. */
            atReqGetNoResult.pAtCmd = "AT+CPSMS?";
            cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );

            if( disablePsm && ( cellularStatus == CELLULAR_SUCCESS ) )
            {
                LogInfo( ( "rebootCellularModem: Disable +CPSMS setting." ) );
                atReqGetNoResult.pAtCmd = "AT+CPSMS=0";
                cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
            }

            if( disableEidrx && ( cellularStatus == CELLULAR_SUCCESS ) )
            {
                LogInfo( ( "rebootCellularModem: Disable +CEDRXS setting." ) );
                atReqGetNoResult.pAtCmd = "AT+CEDRXS=0,4";
                cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
            }

            break;
        }
        else
        {
            LogWarn( ( "rebootCellularModem: Modem is not ready. Retry sending ATE0." ) );
        }

        count = count + ENBABLE_MODULE_UE_REBOOT_POLL_TIME;
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_ModuleEnableUE( CellularContext_t * pContext )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularAtReq_t atReqGetNoResult =
    {
        NULL,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0
    };
    CellularAtReq_t atReqGetWithResult =
    {
        NULL,
        CELLULAR_AT_WO_PREFIX,
        NULL,
        NULL,
        NULL,
        0
    };
    char pAtCmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { 0 };

    if( pContext != NULL )
    {
        /* Disable echo. */
        atReqGetWithResult.pAtCmd = "ATE0";
        cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetWithResult );

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            /* Disable DTR function. */
            atReqGetNoResult.pAtCmd = "AT&D0";
            cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
        }

        #ifndef CELLULAR_CONFIG_DISABLE_FLOW_CONTROL
            if( cellularStatus == CELLULAR_SUCCESS )
            {
                /* Enable RTS/CTS hardware flow control. */
                atReqGetNoResult.pAtCmd = "AT+IFC=2,2";
                cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
            }
        #endif

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            /* Report verbose mobile termination error. */
            atReqGetNoResult.pAtCmd = "AT+CMEE=2";
            cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
        }

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            /* Setup mobile network operator profiles. */
            /* Setting +UMNOPROF profile will automatically select suitable values for +URAT and +UBANDMASK. */

            /* Check current MNO profile first to avoid unneccessary modem reboot. */
            MNOProfileType_t currentMNOProfile = MNO_PROFILE_NOT_SET;
            cellularStatus = _Cellular_GetCurrentMNOProfile( pContext, &currentMNOProfile );

            LogInfo( ( "Cellular_ModuleEnableUE: currentMNOProfile = [%d], desiredProfile = [%d]", currentMNOProfile, CELLULAR_CONFIG_SARA_R4_SET_MNO_PROFILE ) );

            if( cellularStatus == CELLULAR_SUCCESS )
            {
                /* Set MNO profile if not set already */
                if( ( currentMNOProfile != CELLULAR_CONFIG_SARA_R4_SET_MNO_PROFILE ) && ( CELLULAR_CONFIG_SARA_R4_SET_MNO_PROFILE != MNO_PROFILE_NOT_SET ) )
                {
                    atReqGetNoResult.pAtCmd = pAtCmdBuf;
                    ( void ) snprintf( ( char * ) atReqGetNoResult.pAtCmd, CELLULAR_AT_CMD_MAX_SIZE, "%s%d", "AT+COPS=2;+UMNOPROF=", CELLULAR_CONFIG_SARA_R4_SET_MNO_PROFILE );
                    cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );

                    if( cellularStatus == CELLULAR_SUCCESS )
                    {
                        cellularStatus = rebootCellularModem( pContext, true, true );
                    }
                }

                #ifdef CELLULAR_CONFIG_SARA_R4_REBOOT_ON_INIT
                    else
                    {
                        cellularStatus = rebootCellularModem( pContext, true, true );
                    }
                #endif
            }
        }

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            atReqGetNoResult.pAtCmd = "AT+COPS=0";
            cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
        }

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            atReqGetNoResult.pAtCmd = "AT+CFUN=1";
            cellularStatus = sendAtCommandWithRetryTimeout( pContext, &atReqGetNoResult );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_ModuleEnableUrc( CellularContext_t * pContext )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularAtReq_t atReqGetNoResult =
    {
        NULL,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0
    };

    atReqGetNoResult.pAtCmd = "AT+COPS=3,2";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    atReqGetNoResult.pAtCmd = "AT+CREG=2";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    atReqGetNoResult.pAtCmd = "AT+CGREG=2";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    atReqGetNoResult.pAtCmd = "AT+CEREG=2";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    atReqGetNoResult.pAtCmd = "AT+CTZR=1";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    /* TODO: +CGEV URC enable. */
    /* atReqGetNoResult.pAtCmd = "AT+CGEREP=2,0"; */
    /* (void)_Cellular_AtcmdRequestWithCallback(pContext, atReqGetNoResult); */

    /* Power saving mode URC enable. */
    atReqGetNoResult.pAtCmd = "AT+UPSMR=1";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    /* Mobile termination event reporting +CIEV URC enable. */
    atReqGetNoResult.pAtCmd = "AT+CMER=1,0,0,2,1";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    /* Enable signal level change indication via +CIEV URC. (To enable all indications, set to 4095) */
    atReqGetNoResult.pAtCmd = "AT+UCIND=2";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    /* Enable greeting message "RDY" on modem bootup. */
    atReqGetNoResult.pAtCmd = "AT+CSGT=1,\"RDY\"";
    ( void ) _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNoResult );

    return cellularStatus;
}

/*-----------------------------------------------------------*/

uint32_t _Cellular_GetSocketId( CellularContext_t * pContext,
                                uint8_t sessionId )
{
    cellularModuleContext_t * pModuleContext = NULL;
    uint32_t socketIndex = INVALID_SOCKET_INDEX;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    if( pContext != NULL )
    {
        cellularStatus = _Cellular_GetModuleContext( pContext, ( void ** ) &pModuleContext );
    }
    else
    {
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }

    if( ( cellularStatus == CELLULAR_SUCCESS ) && ( sessionId <= ( ( uint8_t ) MAX_TCP_SESSION_ID ) ) )
    {
        socketIndex = pModuleContext->pSessionMap[ sessionId ];
    }

    return socketIndex;
}

/*-----------------------------------------------------------*/

uint32_t _Cellular_GetSessionId( CellularContext_t * pContext,
                                 uint32_t socketIndex )
{
    cellularModuleContext_t * pModuleContext = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    uint32_t sessionId = INVALID_SESSION_ID;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_GetSessionId invalid cellular context" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( socketIndex == INVALID_SOCKET_INDEX )
    {
        LogError( ( "_Cellular_GetSessionId invalid socketIndex" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        cellularStatus = _Cellular_GetModuleContext( pContext, ( void ** ) &pModuleContext );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        for( sessionId = 0; sessionId < TCP_SESSION_TABLE_LEGNTH; sessionId++ )
        {
            if( pModuleContext->pSessionMap[ sessionId ] == socketIndex )
            {
                break;
            }
        }

        /* Mapping is not found in the session mapping table. */
        if( sessionId == TCP_SESSION_TABLE_LEGNTH )
        {
            sessionId = INVALID_SESSION_ID;
        }
    }
    else
    {
        sessionId = INVALID_SESSION_ID;
    }

    return sessionId;
}
