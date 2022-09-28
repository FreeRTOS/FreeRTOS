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
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* Cellular includes. */
#include "cellular_types.h"
#include "cellular_api.h"
#include "cellular_common_api.h"
#include "cellular_common.h"
#include "cellular_at_core.h"

/* Cellular module includes. */
#include "cellular_hl7802.h"

/*-----------------------------------------------------------*/

#define CELLULAR_AT_CMD_TYPICAL_MAX_SIZE              ( 32U )

#define SOCKET_END_PATTERN                            "--EOF--Pattern--"
#define SOCKET_END_PATTERN_LEN                        ( 16U )

#define SOCKET_DATA_CONNECT_TOKEN                     "CONNECT"
#define SOCKET_DATA_CONNECT_TOKEN_LEN                 ( 7U )

#define CELLULAR_CEDRXS_POS_ACT                       ( 0U )
#define CELLULAR_CEDRXS_POS_RAT                       ( 1U )
#define CELLULAR_CEDRXS_POS_REQUESTED_EDRX_VALUE      ( 2U )
#define CELLULAR_CEDRXS_POS_NW_PROVIDED_EDRX_VALUE    ( 3U )
#define CELLULAR_CEDRXS_POS_REQUESTED_PTW_VALUE       ( 4U )
#define CELLULAR_CEDRXS_POS_NW_PROVIDED_PTW_VALUE     ( 5U )

#define RAT_PRIOIRTY_LIST_LENGTH                      ( 3U )

#define SIGNAL_QUALITY_CSQ_UNKNOWN                    ( 99 )
#define SIGNAL_QUALITY_CSQ_BER_MIN                    ( 0 )
#define SIGNAL_QUALITY_CSQ_BER_MAX                    ( 7 )

#define INVALID_PDN_INDEX                             ( 0xFFU )

#define CELLULAR_PDN_STATUS_POS_CONTEXT_ID            ( 0U )
#define CELLULAR_PDN_STATUS_POS_GPRS                  ( 1U ) /* Ignored pos. */
#define CELLULAR_PDN_STATUS_POS_APN                   ( 2U ) /* Ignored pos. */
#define CELLULAR_PDN_STATUS_POS_LOGIN                 ( 3U ) /* Ignored pos. */
#define CELLULAR_PDN_STATUS_POS_PASSWORD              ( 4U ) /* Ignored pos. */
#define CELLULAR_PDN_STATUS_POS_AF                    ( 5U )
#define CELLULAR_PDN_STATUS_POS_IP                    ( 6U ) /* Ignored pos. */
#define CELLULAR_PDN_STATUS_POS_DNS1                  ( 7U ) /* Ignored pos. */
#define CELLULAR_PDN_STATUS_POS_DNS2                  ( 8U ) /* Ignored pos. */
#define CELLULAR_PDN_STATUS_POS_STATE                 ( 9U )

#define CELLULAR_PDN_STATE_DISCONNECTED               ( 0U )
#define CELLULAR_PDN_STATE_CONNECTING                 ( 1U )
#define CELLULAR_PDN_STATE_CONNECTED                  ( 2U )
#define CELLULAR_PDN_STATE_IDLE                       ( 3U )
#define CELLULAR_PDN_STATE_DISCONNECTING              ( 4U )

#define KSELACQ_RAT_CATM_CHAR                         ( '1' )
#define KSELACQ_RAT_NBIOT_CHAR                        ( '2' )
#define KSELACQ_RAT_GSM_CHAR                          ( '3' )

#define CELLULAR_PORT_NUM_CHAR_LEN                    ( 6 )

#define CELLULAR_REMOTE_IP_ADDR_MAX_LENGTH            ( 127 )

/*-----------------------------------------------------------*/

/**
 * @brief Parameters involved in receiving data through sockets
 */
typedef struct _socketDataRecv
{
    uint32_t * pDataLen;
    uint8_t * pData;
} _socketDataRecv_t;

typedef struct socketStat
{
    tcpSocketState_t status;         /* TCP socket state. */
    tcpConnectionFailure_t tcpNotif; /* 1 if socket/connection is OK, <tcp_notif> if an error has happened. */
    uint16_t remData;                /* Remaining bytes in the socket buffer, waiting to be sent. */
    uint16_t rcvData;                /* Received bytes, can be read with +KTCPRCV command. */
} socketStat_t;

/*-----------------------------------------------------------*/

static const char * _socketSendSuccesTokenTable[] = { SOCKET_DATA_CONNECT_TOKEN };
static const uint32_t _socketSendSuccesTokenTableLength = 1;

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetSocketStat( CellularContext_t * pContext,
                                                            const CellularATCommandResponse_t * pAtResp,
                                                            void * pData,
                                                            uint16_t dataLen );
static CellularError_t _Cellular_GetSocketStat( CellularHandle_t cellularHandle,
                                                CellularSocketHandle_t socketHandle,
                                                socketStat_t * pSocketStat );
static CellularPktStatus_t socketRecvDataPrefix( void * pCallbackContext,
                                                 char * pLine,
                                                 uint32_t lineLength,
                                                 char ** ppDataStart,
                                                 uint32_t * pDataLength );
static CellularATError_t getDataFromResp( const CellularATCommandResponse_t * pAtResp,
                                          const _socketDataRecv_t * pDataRecv,
                                          uint32_t outBufSize );
static CellularPktStatus_t _Cellular_RecvFuncData( CellularContext_t * pContext,
                                                   const CellularATCommandResponse_t * pAtResp,
                                                   void * pData,
                                                   uint16_t dataLen );
static CellularError_t buildSocketConfig( CellularSocketHandle_t socketHandle,
                                          char * pCmdBuf );
static CellularError_t storeAccessModeAndAddress( CellularContext_t * pContext,
                                                  CellularSocketHandle_t socketHandle,
                                                  CellularSocketAccessMode_t dataAccessMode,
                                                  const CellularSocketAddress_t * pRemoteSocketAddress );
static CellularPktStatus_t _Cellular_RecvFuncGetTcpCfgSessionId( CellularContext_t * pContext,
                                                                 const CellularATCommandResponse_t * pAtResp,
                                                                 void * pData,
                                                                 uint16_t dataLen );
static CellularError_t _Cellular_getTcpCfgSessionId( CellularHandle_t cellularHandle,
                                                     CellularSocketHandle_t socketHandle,
                                                     uint8_t * pSessionId );
static CellularATError_t parseEidrxToken( char * pToken,
                                          uint8_t tokenIndex,
                                          CellularEidrxSettingsList_t * pEidrxSettingsList,
                                          uint8_t count );
static CellularATError_t parseEidrxLine( char * pInputLine,
                                         uint8_t count,
                                         CellularEidrxSettingsList_t * pEidrxSettingsList );
static CellularPktStatus_t _Cellular_RecvFuncGetEidrxSettings( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen );
static CellularRat_t convertKselacqIndexToRat( char ratIndex );
static CellularPktStatus_t _Cellular_RecvFuncGetRatPriority( CellularContext_t * pContext,
                                                             const CellularATCommandResponse_t * pAtResp,
                                                             void * pData,
                                                             uint16_t dataLen );
static int16_t convertCesqSignalRxlev( int32_t rxlevValue );
static int16_t convertCesqSignalRsrq( int32_t rsrqValue );
static int16_t convertCesqSignalRsrp( int32_t rsrpValue );
static bool _parseSignalQuality( char * pQcsqPayload,
                                 CellularSignalInfo_t * pSignalInfo );
static CellularPktStatus_t _Cellular_RecvFuncGetSignalInfo( CellularContext_t * pContext,
                                                            const CellularATCommandResponse_t * pAtResp,
                                                            void * pData,
                                                            uint16_t dataLen );

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library types. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncGetSocketStat( CellularContext_t * pContext,
                                                            const CellularATCommandResponse_t * pAtResp,
                                                            void * pData,
                                                            uint16_t dataLen )
{
    char * pInputLine = NULL, * pToken = NULL;
    socketStat_t * pSocketStat = ( socketStat_t * ) pData;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    int32_t tempValue = 0;

    if( pContext == NULL )
    {
        LogError( ( "GetSocketStat: Invalid handle" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pSocketStat == NULL ) || ( dataLen != sizeof( socketStat_t ) ) )
    {
        LogError( ( "GetSocketStat: Bad parameters" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetSocketStat: Input Line passed is NULL" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else
    {
        /* +KTCPSTAT: <session_id>,<status>,<tcp_notif>,<rem_data>,<rcv_data>. */
        /* Remove prefix and leading space. */
        pInputLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemovePrefix( &pInputLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pInputLine );
        }

        /* Get token status. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= TCP_SOCKET_STATE_NOT_DEFINED ) && ( tempValue < TCP_SOCKET_STATE_MAX ) )
                {
                    pSocketStat->status = ( tcpSocketState_t ) tempValue;
                }
                else
                {
                    LogError( ( "GetSocketStat unknown status %d", tempValue ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Get token tcp_notif. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= TCP_NOTIF_OK ) && ( tempValue < TCP_NOTIF_MAX ) )
                {
                    pSocketStat->tcpNotif = ( tcpConnectionFailure_t ) tempValue;
                }
                else
                {
                    LogError( ( "GetSocketStat unknown tcp_notif %d", tempValue ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Get token rem_data. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) && ( tempValue < UINT16_MAX ) )
                {
                    pSocketStat->remData = ( uint16_t ) tempValue;
                }
                else
                {
                    LogError( ( "GetSocketStat unknown rem_data %d", tempValue ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        /* Get token rcv_data. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) && ( tempValue < UINT16_MAX ) )
                {
                    pSocketStat->rcvData = ( uint16_t ) tempValue;
                }
                else
                {
                    LogError( ( "GetSocketStat unknown rcvData %d", tempValue ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularError_t _Cellular_GetSocketStat( CellularHandle_t cellularHandle,
                                                CellularSocketHandle_t socketHandle,
                                                socketStat_t * pSocketStat )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    char cmdBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSocketStat =
    {
        cmdBuf,
        CELLULAR_AT_WITH_PREFIX,
        "+KTCPSTAT",
        _Cellular_RecvFuncGetSocketStat,
        pSocketStat,
        sizeof( socketStat_t ),
    };
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    uint32_t sessionId = _Cellular_GetSessionId( pContext, socketHandle->socketId );

    /* Internal function. Caller checks parameters. */
    ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_TYPICAL_MAX_SIZE, "AT+KTCPSTAT=%lu", sessionId );

    pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSocketStat,
                                                           CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS );

    cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t socketRecvDataPrefix( void * pCallbackContext,
                                                 char * pLine,
                                                 uint32_t lineLength,
                                                 char ** ppDataStart,
                                                 uint32_t * pDataLength )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    uint32_t * pRecvDataLength = ( uint32_t * ) pCallbackContext;

    if( ( pLine == NULL ) || ( ppDataStart == NULL ) || ( pDataLength == NULL ) || ( pCallbackContext == NULL ) )
    {
        LogError( ( "socketRecvData: Bad parameters" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( lineLength < ( SOCKET_DATA_CONNECT_TOKEN_LEN + 2U ) ) && ( *pRecvDataLength > 0 ) )
    {
        /* Need more data to decide the data prefix. */
        pktStatus = CELLULAR_PKT_STATUS_SIZE_MISMATCH;
    }
    else
    {
        if( strncmp( pLine, SOCKET_DATA_CONNECT_TOKEN, SOCKET_DATA_CONNECT_TOKEN_LEN ) == 0 )
        {
            /* The string length of "CONNECT\r\n". */
            *ppDataStart = ( char * ) &pLine[ SOCKET_DATA_CONNECT_TOKEN_LEN + 2 ]; /* Indicate the data start in pLine. */
            *pDataLength = *pRecvDataLength;                                       /* Return the data length from pCallbackContext. */
            *pRecvDataLength = 0;
        }
        else
        {
            /* Prefix string which is not "CONNECT" does't indicate data start. Set data length to 0.*/
            *pDataLength = 0;
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t getDataFromResp( const CellularATCommandResponse_t * pAtResp,
                                          const _socketDataRecv_t * pDataRecv,
                                          uint32_t outBufSize )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    const char * pInputLine = NULL;
    uint32_t dataLenToCopy = 0;

    /* Check if the received data size is greater than the output buffer size. */
    if( *pDataRecv->pDataLen > outBufSize )
    {
        LogError( ( "Data is turncated, received data length %d, out buffer size %d",
                    *pDataRecv->pDataLen, outBufSize ) );
        dataLenToCopy = outBufSize;
        *pDataRecv->pDataLen = outBufSize;
    }
    else
    {
        dataLenToCopy = *pDataRecv->pDataLen;
    }

    /* Data is stored in the next intermediate response. */
    if( pAtResp->pItm->pNext != NULL )
    {
        pInputLine = pAtResp->pItm->pNext->pLine;

        if( ( pInputLine != NULL ) && ( dataLenToCopy > 0U ) )
        {
            /* Copy the data to the out buffer. */
            ( void ) memcpy( ( void * ) pDataRecv->pData, ( const void * ) pInputLine, dataLenToCopy );
        }
        else
        {
            LogError( ( "Receive Data: paramerter error, data pointer %p, data to copy %d",
                        pInputLine, dataLenToCopy ) );
            atCoreStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }
    else if( *pDataRecv->pDataLen == 0U )
    {
        /* Receive command success but no data. */
        LogDebug( ( "Receive Data: no data" ) );
    }
    else
    {
        LogError( ( "Receive Data: Intermediate response empty" ) );
        atCoreStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library types. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncData( CellularContext_t * pContext,
                                                   const CellularATCommandResponse_t * pAtResp,
                                                   void * pData,
                                                   uint16_t dataLen )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char * pInputLine = NULL, * pEndPatternLine = NULL;
    const _socketDataRecv_t * pDataRecv = ( _socketDataRecv_t * ) pData;

    if( pContext == NULL )
    {
        LogError( ( "Receive Data: invalid context" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "Receive Data: response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp->pItm->pNext == NULL ) || ( pAtResp->pItm->pNext->pNext == NULL ) )
    {
        LogError( ( "Receive Data: response data or end pattern is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pDataRecv == NULL ) || ( pDataRecv->pData == NULL ) || ( pDataRecv->pDataLen == NULL ) )
    {
        LogError( ( "Receive Data: Bad parameters" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pInputLine = pAtResp->pItm->pLine;                    /* The first item is the data prefix. */
        pEndPatternLine = pAtResp->pItm->pNext->pNext->pLine; /* The third item is the end pattern. */

        /* Check the data prefix token "CONNECT". */
        if( strncmp( pInputLine, SOCKET_DATA_CONNECT_TOKEN, SOCKET_DATA_CONNECT_TOKEN_LEN ) != 0 )
        {
            LogError( ( "response item error in prefix CONNECT" ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }

        /* Check the data end pattern. */
        if( strncmp( pEndPatternLine, SOCKET_END_PATTERN, SOCKET_END_PATTERN_LEN ) != 0 )
        {
            LogError( ( "response item error in end pattern"SOCKET_END_PATTERN ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }

        /* Process the data buffer. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = getDataFromResp( pAtResp, pDataRecv, dataLen );
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularError_t buildSocketConfig( CellularSocketHandle_t socketHandle,
                                          char * pCmdBuf )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    /* +1 size in buffer for ',' */
    char portBuf[ CELLULAR_PORT_NUM_CHAR_LEN + 1 ] = { 0 };

    if( pCmdBuf == NULL )
    {
        LogDebug( ( "buildSocketConfig: Invalid command buffer" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( socketHandle->socketProtocol != CELLULAR_SOCKET_PROTOCOL_TCP )
    {
        LogError( ( "buildSocketConfig: socket protocol unsupported %d",
                    socketHandle->socketProtocol ) );
        cellularStatus = CELLULAR_UNSUPPORTED;
    }
    else if( strlen( socketHandle->remoteSocketAddress.ipAddress.ipAddress ) > CELLULAR_REMOTE_IP_ADDR_MAX_LENGTH )
    {
        /* The maximum length of domain name is 127 in HL7802. */
        LogError( ( "buildSocketConfig: the remote server's address is too long, length=%u",
                    strlen( socketHandle->remoteSocketAddress.ipAddress.ipAddress ) ) );
        cellularStatus = CELLULAR_UNSUPPORTED;
    }
    else
    {
        /* Form the AT command. */

        /* The return value of snprintf is not used.
         * The max length of the string is fixed and checked offline.
         * Reserve buffer for port setting. */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( pCmdBuf, CELLULAR_AT_CMD_MAX_SIZE - sizeof( portBuf ),
                           "AT+KTCPCFG=%u,0,\"%s\",%u",
                           socketHandle->contextId,
                           socketHandle->remoteSocketAddress.ipAddress.ipAddress,
                           socketHandle->remoteSocketAddress.port );

        /* Set the local port in the end of command buffer string if localPort is not 0. */
        if( socketHandle->localPort > 0 )
        {
            ( void ) snprintf( portBuf, sizeof( portBuf ),
                               ",%u",
                               socketHandle->localPort );

            /* Because the length of host's IP address is limited,
             * the buffer size must be enough for port setting. */
            strcat( pCmdBuf, portBuf );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularError_t storeAccessModeAndAddress( CellularContext_t * pContext,
                                                  CellularSocketHandle_t socketHandle,
                                                  CellularSocketAccessMode_t dataAccessMode,
                                                  const CellularSocketAddress_t * pRemoteSocketAddress )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else if( ( pRemoteSocketAddress == NULL ) || ( socketHandle == NULL ) )
    {
        LogDebug( ( "storeAccessModeAndAddress: Invalid socket address" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( socketHandle->socketState != SOCKETSTATE_ALLOCATED )
    {
        LogError( ( "storeAccessModeAndAddress, bad socket state %d",
                    socketHandle->socketState ) );
        cellularStatus = CELLULAR_INTERNAL_FAILURE;
    }
    else if( dataAccessMode != CELLULAR_ACCESSMODE_BUFFER )
    {
        LogError( ( "storeAccessModeAndAddress, Access mode not supported %d",
                    dataAccessMode ) );
        cellularStatus = CELLULAR_UNSUPPORTED;
    }
    else
    {
        socketHandle->remoteSocketAddress.port = pRemoteSocketAddress->port;
        socketHandle->dataMode = dataAccessMode;
        socketHandle->remoteSocketAddress.ipAddress.ipAddressType =
            pRemoteSocketAddress->ipAddress.ipAddressType;
        ( void ) strncpy( socketHandle->remoteSocketAddress.ipAddress.ipAddress,
                          pRemoteSocketAddress->ipAddress.ipAddress,
                          CELLULAR_IP_ADDRESS_MAX_SIZE + 1U );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library types. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncGetTcpCfgSessionId( CellularContext_t * pContext,
                                                                 const CellularATCommandResponse_t * pAtResp,
                                                                 void * pData,
                                                                 uint16_t dataLen )
{
    char * pInputLine = NULL;
    uint8_t * pSessionId = pData;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    int32_t tempValue = 0;

    if( pContext == NULL )
    {
        LogError( ( "GetTcpCfgSessionId: Invalid handle" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pSessionId == NULL ) || ( dataLen != sizeof( uint8_t ) ) )
    {
        LogError( ( "GetTcpCfgSessionId: Bad parameters" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetTcpCfgSessionId: Input Line passed is NULL" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else
    {
        pInputLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemovePrefix( &pInputLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pInputLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATStrtoi( pInputLine, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= MIN_TCP_SESSION_ID ) && ( tempValue <= MAX_TCP_SESSION_ID ) )
                {
                    *pSessionId = ( uint8_t ) tempValue;
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

static CellularError_t _Cellular_getTcpCfgSessionId( CellularHandle_t cellularHandle,
                                                     CellularSocketHandle_t socketHandle,
                                                     uint8_t * pSessionId )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSocketConnect =
    {
        cmdBuf,
        CELLULAR_AT_WITH_PREFIX,
        "+KTCPCFG",
        _Cellular_RecvFuncGetTcpCfgSessionId,
        pSessionId,
        sizeof( uint8_t ),
    };

    /* Internal function. Caller checks parameters. */
    cellularStatus = buildSocketConfig( socketHandle, cmdBuf );

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSocketConnect,
                                                               CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_SocketConnect: Socket connect failed, cmdBuf:%s, PktRet: %d", cmdBuf, pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseEidrxToken( char * pToken,
                                          uint8_t tokenIndex,
                                          CellularEidrxSettingsList_t * pEidrxSettingsList,
                                          uint8_t count )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    switch( tokenIndex )
    {
        case CELLULAR_CEDRXS_POS_ACT:
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) &&
                    ( tempValue <= ( int32_t ) UINT8_MAX ) )
                {
                    pEidrxSettingsList->eidrxList[ count ].mode = ( uint8_t ) tempValue;
                }
                else
                {
                    LogError( ( "Error in processing mode value. Token %s", pToken ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }

            break;

        case CELLULAR_CEDRXS_POS_RAT:
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) &&
                    ( tempValue <= ( int32_t ) UINT8_MAX ) )
                {
                    pEidrxSettingsList->eidrxList[ count ].rat = ( uint8_t ) tempValue;
                }
                else
                {
                    LogError( ( "Error in processing Requested rat value. Token %s", pToken ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }

            break;


        case CELLULAR_CEDRXS_POS_REQUESTED_EDRX_VALUE:
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) &&
                    ( tempValue <= ( int32_t ) UINT8_MAX ) )
                {
                    pEidrxSettingsList->eidrxList[ count ].requestedEdrxVaue = ( uint8_t ) tempValue;
                }
                else
                {
                    LogError( ( "Error in processing Requested Edrx value. Token %s", pToken ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }

            break;

        case CELLULAR_CEDRXS_POS_NW_PROVIDED_EDRX_VALUE:
            /* Unused value. */
            break;

        case CELLULAR_CEDRXS_POS_REQUESTED_PTW_VALUE:
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) &&
                    ( tempValue <= ( int32_t ) UINT8_MAX ) )
                {
                    pEidrxSettingsList->eidrxList[ count ].pagingTimeWindow = ( uint8_t ) tempValue;
                }
                else
                {
                    LogError( ( "Error in processing Requested paging time window value. Token %s", pToken ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }

            break;

        case CELLULAR_CEDRXS_POS_NW_PROVIDED_PTW_VALUE:
            /* Unused value. */
            break;

        default:
            LogDebug( ( "Unknown Parameter Position %u in AT+CEDRXS Response", tokenIndex ) );
            atCoreStatus = CELLULAR_AT_ERROR;
            break;
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseEidrxLine( char * pInputLine,
                                         uint8_t count,
                                         CellularEidrxSettingsList_t * pEidrxSettingsList )
{
    char * pToken = NULL;
    char * pLocalInputLine = pInputLine;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    uint8_t tokenIndex = 0;

    atCoreStatus = Cellular_ATRemovePrefix( &pLocalInputLine );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATRemoveAllDoubleQuote( pLocalInputLine );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        tokenIndex = 0;

        while( pToken != NULL )
        {
            if( parseEidrxToken( pToken, tokenIndex, pEidrxSettingsList, count ) != CELLULAR_AT_SUCCESS )
            {
                LogInfo( ( "parseEidrxToken %s index %d failed", pToken, tokenIndex ) );
            }

            tokenIndex++;

            if( Cellular_ATGetNextTok( &pLocalInputLine, &pToken ) != CELLULAR_AT_SUCCESS )
            {
                break;
            }
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library prototype. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncGetEidrxSettings( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen )
{
    char * pInputLine = NULL;
    uint8_t count = 0;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularEidrxSettingsList_t * pEidrxSettingsList = NULL;
    const CellularATCommandLine_t * pCommnadItem = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetEidrxSettings: Invalid context" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp == NULL ) ||
             ( pAtResp->pItm == NULL ) ||
             ( pAtResp->pItm->pLine == NULL ) ||
             ( pData == NULL ) ||
             ( dataLen != CELLULAR_EDRX_LIST_MAX_SIZE ) )
    {
        LogError( ( "GetEidrxSettings: Invalid param" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pEidrxSettingsList = ( CellularEidrxSettingsList_t * ) pData;
        pCommnadItem = pAtResp->pItm;

        while( pCommnadItem != NULL )
        {
            pInputLine = pCommnadItem->pLine;
            atCoreStatus = parseEidrxLine( pInputLine, count, pEidrxSettingsList );
            pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );

            if( pktStatus != CELLULAR_PKT_STATUS_OK )
            {
                LogError( ( "GetEidrx: Parsing Error encountered, atCoreStatus: %d", atCoreStatus ) );
            }
            else
            {
                LogDebug( ( "GetEidrx setting[%d]: RAT: %d, Value: 0x%x",
                            count, pEidrxSettingsList->eidrxList[ count ].rat, pEidrxSettingsList->eidrxList[ count ].requestedEdrxVaue ) );
            }

            pCommnadItem = pCommnadItem->pNext;
            count++;
            pEidrxSettingsList->count = count;
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularRat_t convertKselacqIndexToRat( char ratIndex )
{
    CellularRat_t rat = CELLULAR_RAT_INVALID;

    switch( ratIndex )
    {
        case KSELACQ_RAT_CATM_CHAR:
            rat = CELLULAR_RAT_CATM1;
            break;

        case KSELACQ_RAT_NBIOT_CHAR:
            rat = CELLULAR_RAT_NBIOT;
            break;

        case KSELACQ_RAT_GSM_CHAR:
            rat = CELLULAR_RAT_GSM;
            break;

        default:
            break;
    }

    return rat;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library types. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncGetRatPriority( CellularContext_t * pContext,
                                                             const CellularATCommandResponse_t * pAtResp,
                                                             void * pData,
                                                             uint16_t dataLen )
{
    char * pInputLine = NULL, * pToken = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularRat_t * pRatPriorities = NULL;
    uint32_t ratIndex = 0;
    uint32_t maxRatPriorityLength = ( dataLen > RAT_PRIOIRTY_LIST_LENGTH ? RAT_PRIOIRTY_LIST_LENGTH : dataLen );

    if( pContext == NULL )
    {
        LogError( ( "GetRatPriority: Invalid context" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) ||
             ( pAtResp->pItm->pLine == NULL ) || ( pData == NULL ) || ( dataLen == 0U ) )
    {
        LogError( ( "GetRatPriority: Invalid param" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pInputLine = pAtResp->pItm->pLine;
        pRatPriorities = ( CellularRat_t * ) pData;

        /* Response string "+KSELACQ: 1,2,3". */
        atCoreStatus = Cellular_ATRemovePrefix( &pInputLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            for( ratIndex = 0; ratIndex < maxRatPriorityLength; ratIndex++ )
            {
                atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );

                if( atCoreStatus == CELLULAR_AT_SUCCESS )
                {
                    atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pToken );
                }

                if( ( atCoreStatus == CELLULAR_AT_SUCCESS ) && ( strlen( pToken ) == 1 ) )
                {
                    pRatPriorities[ ratIndex ] = convertKselacqIndexToRat( pToken[ 0 ] );
                }
                else
                {
                    pRatPriorities[ ratIndex ] = CELLULAR_RAT_INVALID;
                }
            }
        }

        for( ; ratIndex < dataLen; ratIndex++ )
        {
            pRatPriorities[ ratIndex ] = CELLULAR_RAT_INVALID;
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/* Received signal strength level (see 3GPP TS 45.008 [20] subclause 8.1.4)
 * 0 rssi < -110 dBm : assume -111 dBm to indicate the signal is detectable but fairly week.
 * 1 -110 dBm <= rssi < -109 dBm
 * 2 -109 dBm <= rssi < -108 dBm
 * ...
 * 61 -50 dBm <= rssi < -49 dBm
 * 62 -49 dBm <= rssi < -48 dBm
 * 63 -48 dBm <= rssi
 * 99 not known or not detectable */
static int16_t convertCesqSignalRxlev( int32_t rxlevValue )
{
    int16_t rssidBm = 0;

    if( ( rxlevValue >= 0 ) && ( rxlevValue <= 63 ) )
    {
        rssidBm = ( int16_t ) ( ( -111 ) + ( rxlevValue ) );
    }
    else
    {
        rssidBm = CELLULAR_INVALID_SIGNAL_VALUE;
    }

    return rssidBm;
}

/*-----------------------------------------------------------*/

/* 0 rsrq < -19.5 dB
 * 1 -19.5 dB <= rsrq < -19 dB
 * 2 -19 dB <= rsrq < -18.5 dB
 * ...
 * 32 -4  dB <= rsrq < -3.5 dB
 * 33 -3.5 dB <= rsrq < -3 dB
 * 34 -3  dB <= rsrq
 * 255 Not known or not detectable. */
static int16_t convertCesqSignalRsrq( int32_t rsrqValue )
{
    int16_t rsrqDb = 0;

    if( ( rsrqValue >= 0 ) && ( rsrqValue <= 34 ) )
    {
        rsrqDb = ( int16_t ) ( ( -20 ) + ( rsrqValue * 0.5 ) );
    }
    else
    {
        rsrqDb = CELLULAR_INVALID_SIGNAL_VALUE;
    }

    return rsrqDb;
}

/*-----------------------------------------------------------*/

/* 0 rsrp < -140 dBm
 * 1 -140 dBm <= rsrp < -139 dBm
 * 2 -139 dBm <= rsrp < -138 dBm
 * ...
 * 95 -46 dBm <= rsrp < -45 dBm
 * 96 -45 dBm <= rsrp < -44 dBm
 * 97 -44 dBm <= rsrp
 * 255 Not known or not detectable. */
static int16_t convertCesqSignalRsrp( int32_t rsrpValue )
{
    int16_t rsrpDb = 0;

    if( ( rsrpValue >= 0 ) && ( rsrpValue <= 97 ) )
    {
        rsrpDb = ( int16_t ) ( ( -141 ) + ( rsrpValue ) );
    }
    else
    {
        rsrpDb = CELLULAR_INVALID_SIGNAL_VALUE;
    }

    return rsrpDb;
}

/*-----------------------------------------------------------*/

static bool _parseSignalQuality( char * pQcsqPayload,
                                 CellularSignalInfo_t * pSignalInfo )
{
    char * pToken = NULL, * pTmpQcsqPayload = pQcsqPayload;
    int32_t tempValue = 0;
    int16_t berValue = 0;
    bool parseStatus = true;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* The cesq payload format is <rxlev>,<ber>,<rscp>,<ecno>,<rsrq>,<rsrp>. */

    /* rxlev. */
    atCoreStatus = Cellular_ATGetNextTok( &pTmpQcsqPayload, &pToken );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            pSignalInfo->rssi = convertCesqSignalRxlev( tempValue );
        }
        else
        {
            LogError( ( "_parseSignalQuality: Error in processing RXLEV. Token %s", pToken ) );
            parseStatus = false;
        }
    }

    /* ber. */
    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTmpQcsqPayload, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

        if( ( atCoreStatus == CELLULAR_AT_SUCCESS ) && ( tempValue <= INT16_MAX ) && ( tempValue >= INT16_MIN ) )
        {
            /* As RXQUAL values in the table in 3GPP TS 45.008 [20] subclause 8.2.4.
             * The CESQ ber signal value has the same scale with the AT+CSQ ber signal value. */
            cellularStatus = _Cellular_ConvertCsqSignalBer( ( int16_t ) tempValue, &berValue );

            if( cellularStatus == CELLULAR_SUCCESS )
            {
                pSignalInfo->ber = berValue;
            }
            else
            {
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }
        else
        {
            LogError( ( "_parseSignalQuality: Error in processing BER. Token %s", pToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    /* Skip rscp. */
    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTmpQcsqPayload, &pToken );
    }

    /* Skip ecno. */
    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTmpQcsqPayload, &pToken );
    }

    /* rsrq. */
    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTmpQcsqPayload, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            pSignalInfo->rsrq = convertCesqSignalRsrq( tempValue );
        }
        else
        {
            LogError( ( "_parseSignalQuality: Error in processing RSRQ. Token %s", pToken ) );
            parseStatus = false;
        }
    }

    /* rsrp. */
    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTmpQcsqPayload, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            pSignalInfo->rsrp = convertCesqSignalRsrp( tempValue );
        }
        else
        {
            LogError( ( "_parseSignalQuality: Error in processing RSRP. Token %s", pToken ) );
            parseStatus = false;
        }
    }

    return parseStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library types. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncGetSignalInfo( CellularContext_t * pContext,
                                                            const CellularATCommandResponse_t * pAtResp,
                                                            void * pData,
                                                            uint16_t dataLen )
{
    char * pInputLine = NULL;
    CellularSignalInfo_t * pSignalInfo = ( CellularSignalInfo_t * ) pData;
    bool parseStatus = true;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    if( pContext == NULL )
    {
        LogError( ( "GetSignalInfo: Invalid handle" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pSignalInfo == NULL ) || ( dataLen != sizeof( CellularSignalInfo_t ) ) )
    {
        LogError( ( "GetSignalInfo: Invalid param" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetSignalInfo: Input Line passed is NULL" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else
    {
        pInputLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemovePrefix( &pInputLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pInputLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            parseStatus = _parseSignalQuality( pInputLine, pSignalInfo );
        }

        if( parseStatus != true )
        {
            pSignalInfo->rssi = CELLULAR_INVALID_SIGNAL_VALUE;
            pSignalInfo->rsrp = CELLULAR_INVALID_SIGNAL_VALUE;
            pSignalInfo->rsrq = CELLULAR_INVALID_SIGNAL_VALUE;
            pSignalInfo->ber = CELLULAR_INVALID_SIGNAL_VALUE;
            pSignalInfo->bars = CELLULAR_INVALID_SIGNAL_BAR_VALUE;
            pktStatus = CELLULAR_PKT_STATUS_FAILURE;
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SetDns( CellularHandle_t cellularHandle,
                                 uint8_t contextId,
                                 const char * pDnsServerAddress )
{
    ( void ) cellularHandle;
    ( void ) contextId;
    ( void ) pDnsServerAddress;

    /* Modem use dynamic DNS addresses. Return unsupported. */
    return CELLULAR_UNSUPPORTED;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
CellularError_t Cellular_SocketRecv( CellularHandle_t cellularHandle,
                                     CellularSocketHandle_t socketHandle,
                                     /* coverity[misra_c_2012_rule_8_13_violation] */
                                     uint8_t * pBuffer,
                                     uint32_t bufferLength,
                                     /* coverity[misra_c_2012_rule_8_13_violation] */
                                     uint32_t * pReceivedDataLength )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t recvTimeout = CELLULAR_HL7802_AT_TIMEOUT_60_SECONDS_MS;
    uint32_t recvLen = bufferLength;
    _socketDataRecv_t dataRecv =
    {
        pReceivedDataLength,
        pBuffer
    };
    CellularAtReq_t atReqSocketRecv =
    {
        cmdBuf,
        CELLULAR_AT_MULTI_DATA_WO_PREFIX,
        "CONNECT",
        _Cellular_RecvFuncData,
        ( void * ) &dataRecv,
        bufferLength,
    };
    socketStat_t socketStat = { 0 };
    uint32_t socktCmdDataLength = 0;
    uint32_t sessionId = 0;

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed." ) );
    }
    else if( socketHandle == NULL )
    {
        LogError( ( "_Cellular_RecvData: Invalid socket handle." ) );
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else if( ( pBuffer == NULL ) || ( pReceivedDataLength == NULL ) || ( bufferLength == 0U ) )
    {
        LogError( ( "_Cellular_RecvData: Bad input Param." ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( ( socketHandle->socketState != SOCKETSTATE_CONNECTED ) && ( socketHandle->socketState != SOCKETSTATE_DISCONNECTED ) )
    {
        /* Check the socket connection state. */
        /* For SOCKETSTATE_DISCONNECTED, there may be packets that can be read even though socket is disconnected by remote. */
        LogInfo( ( "Cellular_SocketRecv: socket state %d is not connected.", socketHandle->socketState ) );

        if( ( socketHandle->socketState == SOCKETSTATE_ALLOCATED ) || ( socketHandle->socketState == SOCKETSTATE_CONNECTING ) )
        {
            cellularStatus = CELLULAR_SOCKET_NOT_CONNECTED;
        }
        else
        {
            cellularStatus = CELLULAR_SOCKET_CLOSED;
        }
    }
    else
    {
        sessionId = _Cellular_GetSessionId( pContext, socketHandle->socketId );

        if( sessionId == INVALID_SESSION_ID )
        {
            LogError( ( "Cellular_SocketRecv : invalid session ID for socket index %u",
                        socketHandle->socketId ) );
            cellularStatus = CELLULAR_INVALID_HANDLE;
        }
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Calculate the read length. */
        cellularStatus = _Cellular_GetSocketStat( cellularHandle, socketHandle, &socketStat );

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            socktCmdDataLength = socketStat.rcvData;
        }
        else
        {
            socktCmdDataLength = 0;
        }

        /* Update recvLen to maximum module length. */
        if( CELLULAR_MAX_RECV_DATA_LEN <= bufferLength )
        {
            recvLen = ( uint32_t ) CELLULAR_MAX_RECV_DATA_LEN;
        }

        /* Update the recvLen to available data length in cellular module. */
        if( recvLen > socktCmdDataLength )
        {
            recvLen = socktCmdDataLength;
        }

        *pReceivedDataLength = recvLen;
        socktCmdDataLength = recvLen;

        /* Update receive timeout to default timeout if not set with setsocketopt. */
        if( recvLen > 0 )
        {
            if( socketHandle->recvTimeoutMs != 0U )
            {
                recvTimeout = socketHandle->recvTimeoutMs;
            }

            /* The return value of snprintf is not used.
             * The max length of the string is fixed and checked offline. */
            /* coverity[misra_c_2012_rule_21_6_violation]. */
            ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
                               "%s%u,%u", "AT+KTCPRCV=", sessionId, recvLen );
            pktStatus = _Cellular_TimeoutAtcmdDataRecvRequestWithCallback( pContext,
                                                                           atReqSocketRecv, recvTimeout, socketRecvDataPrefix, &socktCmdDataLength );

            if( pktStatus != CELLULAR_PKT_STATUS_OK )
            {
                /* Reset data handling parameters. */
                LogError( ( "Cellular_SocketRecv: Data Receive fail, pktStatus: %d", pktStatus ) );
                cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
            }
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
CellularError_t Cellular_SocketSend( CellularHandle_t cellularHandle,
                                     CellularSocketHandle_t socketHandle,
                                     const uint8_t * pData,
                                     uint32_t dataLength,
                                     /* coverity[misra_c_2012_rule_8_13_violation] */
                                     uint32_t * pSentDataLength )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    uint32_t sendTimeout = CELLULAR_HL7802_AT_TIMEOUT_60_SECONDS_MS;
    char cmdBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSocketSend =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };
    CellularAtDataReq_t atDataReqSocketSend =
    {
        pData,
        dataLength,
        pSentDataLength,
        ( const uint8_t * ) SOCKET_END_PATTERN,
        SOCKET_END_PATTERN_LEN
    };
    uint32_t sessionId = 0;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed." ) );
    }
    else if( socketHandle == NULL )
    {
        LogError( ( "Cellular_SocketSend: Invalid socket handle." ) );
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else if( ( pData == NULL ) || ( pSentDataLength == NULL ) || ( dataLength == 0U ) )
    {
        LogError( ( "Cellular_SocketSend: Invalid parameter." ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( socketHandle->socketState != SOCKETSTATE_CONNECTED )
    {
        /* Check the socket connection state. */
        LogInfo( ( "Cellular_SocketSend: socket state %d is not connected.", socketHandle->socketState ) );

        if( ( socketHandle->socketState == SOCKETSTATE_ALLOCATED ) || ( socketHandle->socketState == SOCKETSTATE_CONNECTING ) )
        {
            cellularStatus = CELLULAR_SOCKET_NOT_CONNECTED;
        }
        else
        {
            cellularStatus = CELLULAR_SOCKET_CLOSED;
        }
    }
    else
    {
        sessionId = _Cellular_GetSessionId( pContext, socketHandle->socketId );

        if( sessionId == INVALID_SESSION_ID )
        {
            LogError( ( "Cellular_SocketSend : invalid session ID for socket index %u",
                        socketHandle->socketId ) );
            cellularStatus = CELLULAR_INVALID_HANDLE;
        }
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Send data length check. */
        if( dataLength > ( uint32_t ) CELLULAR_MAX_SEND_DATA_LEN )
        {
            atDataReqSocketSend.dataLen = ( uint32_t ) CELLULAR_MAX_SEND_DATA_LEN;
        }

        /* Check send timeout. If not set by setsockopt, use default value. */
        if( socketHandle->sendTimeoutMs != 0U )
        {
            sendTimeout = socketHandle->sendTimeoutMs;
        }

        /* Form the AT command. */

        /* The return value of snprintf is not used.
         * The max length of the string is fixed and checked offline. */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_TYPICAL_MAX_SIZE, "%s%u,%u",
                           "AT+KTCPSND=", sessionId, atDataReqSocketSend.dataLen );

        pktStatus = _Cellular_TimeoutAtcmdDataSendSuccessToken( pContext, atReqSocketSend, atDataReqSocketSend,
                                                                CELLULAR_HL7802_AT_TIMEOUT_60_SECONDS_MS, sendTimeout,
                                                                _socketSendSuccesTokenTable, _socketSendSuccesTokenTableLength );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            if( socketHandle->socketState == SOCKETSTATE_DISCONNECTED )
            {
                LogWarn( ( "Cellular_SocketSend: Data send fail. Socket is closed during the send operation." ) );
                cellularStatus = CELLULAR_SOCKET_CLOSED;
            }
            else
            {
                LogError( ( "Cellular_SocketSend: Data send fail, PktRet: %d", pktStatus ) );
                cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
            }
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SocketClose( CellularHandle_t cellularHandle,
                                      CellularSocketHandle_t socketHandle )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSocketClose =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };
    uint32_t sessionId = 0U;
    cellularModuleContext_t * pModuleContext = NULL;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( socketHandle == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else
    {
        if( socketHandle->socketState == SOCKETSTATE_CONNECTING )
        {
            LogWarn( ( "Cellular_SocketClose: Socket state is SOCKETSTATE_CONNECTING." ) );
        }

        cellularStatus = _Cellular_GetModuleContext( pContext, ( void ** ) &pModuleContext );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        sessionId = _Cellular_GetSessionId( pContext, socketHandle->socketId );

        if( sessionId == INVALID_SESSION_ID )
        {
            LogError( ( "Cellular_SocketSend : invalid session ID for socket index %u",
                        socketHandle->socketId ) );
            cellularStatus = CELLULAR_INVALID_HANDLE;
        }
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Remove the mapping. */
        pModuleContext->pSessionMap[ sessionId ] = INVALID_SOCKET_INDEX;

        /* Close the socket. */
        if( socketHandle->socketState == SOCKETSTATE_CONNECTED )
        {
            ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_TYPICAL_MAX_SIZE, "%s%lu,1",
                               "AT+KTCPCLOSE=", sessionId );
            pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSocketClose,
                                                                   CELLULAR_HL7802_AT_TIMEOUT_60_SECONDS_MS );

            /* Delete the socket config. */
            if( pktStatus != CELLULAR_PKT_STATUS_OK )
            {
                LogWarn( ( "Cellular_SocketClose: AT+KTCPCLOSE fail, PktRet: %d", pktStatus ) );
            }
        }

        if( ( socketHandle->socketState == SOCKETSTATE_CONNECTED ) ||
            ( socketHandle->socketState == SOCKETSTATE_CONNECTING ) ||
            ( socketHandle->socketState == SOCKETSTATE_DISCONNECTED ) )
        {
            ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_TYPICAL_MAX_SIZE, "%s%lu",
                               "AT+KTCPDEL=", sessionId );
            pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSocketClose,
                                                                   CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS );

            if( pktStatus != CELLULAR_PKT_STATUS_OK )
            {
                LogError( ( "Cellular_SocketClose: AT+KTCPDEL fail, PktRet: %d", pktStatus ) );
            }
        }

        /* Ignore the result from the info, and force to remove the socket. */
        cellularStatus = _Cellular_RemoveSocketData( pContext, socketHandle );
    }

    return CELLULAR_SUCCESS;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SocketConnect( CellularHandle_t cellularHandle,
                                        CellularSocketHandle_t socketHandle,
                                        CellularSocketAccessMode_t dataAccessMode,
                                        const CellularSocketAddress_t * pRemoteSocketAddress )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    uint8_t sessionId = 0;
    CellularAtReq_t atReqSocketConnect =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };
    cellularModuleContext_t * pModuleContext = NULL;

    /* Make sure the library is open. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed." ) );
    }
    else if( pRemoteSocketAddress == NULL )
    {
        LogError( ( "Cellular_SocketConnect: Invalid socket address." ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( socketHandle == NULL )
    {
        LogError( ( "Cellular_SocketConnect: Invalid socket handle." ) );
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else if( ( socketHandle->socketState == SOCKETSTATE_CONNECTED ) || ( socketHandle->socketState == SOCKETSTATE_CONNECTING ) )
    {
        LogError( ( "Cellular_SocketConnect: Not allowed in state %d.", socketHandle->socketState ) );
        cellularStatus = CELLULAR_NOT_ALLOWED;
    }
    else
    {
        cellularStatus = storeAccessModeAndAddress( pContext, socketHandle, dataAccessMode, pRemoteSocketAddress );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        cellularStatus = _Cellular_GetModuleContext( pContext, ( void ** ) &pModuleContext );
    }

    /* Set socket config and get session id. The session id is defined by the modem. */
    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Builds the Socket connect command. */
        cellularStatus = _Cellular_getTcpCfgSessionId( pContext, socketHandle, &sessionId );

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            /* Create the reverse table to store the socketIndex to sessionId. */
            pModuleContext->pSessionMap[ sessionId ] = socketHandle->socketId;
        }
    }

    /* Start the tcp connection. */
    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Set the socket state to connecting state. If cellular modem returns error,
         * revert the state to allocated state. */
        socketHandle->socketState = SOCKETSTATE_CONNECTING;

        /* The return value of snprintf is not used.
         * The max length of the string is fixed and checked offline. */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE,
                           "AT+KTCPCNX=%u", sessionId );

        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSocketConnect,
                                                               CELLULAR_HL7802_AT_TIMEOUT_30_SECONDS_MS );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_SocketConnect: Socket connect failed, cmdBuf:%s, PktRet: %d", cmdBuf, pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

            /* Revert the state to allocated state. */
            socketHandle->socketState = SOCKETSTATE_ALLOCATED;
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetSimCardStatus( CellularHandle_t cellularHandle,
                                           CellularSimCardStatus_t * pSimCardStatus )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Parameters are checked in this API. */
    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, pSimCardStatus );

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, pSimCardStatus );

        if( ( cellularStatus == CELLULAR_SUCCESS ) &&
            ( pSimCardStatus->simCardLockState != CELLULAR_SIM_CARD_INVALID ) &&
            ( pSimCardStatus->simCardLockState != CELLULAR_SIM_CARD_LOCK_UNKNOWN ) )
        {
            pSimCardStatus->simCardState = CELLULAR_SIM_CARD_INSERTED;
        }
        else
        {
            pSimCardStatus->simCardState = CELLULAR_SIM_CARD_UNKNOWN;
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_RegisterUrcSignalStrengthChangedCallback( CellularHandle_t cellularHandle,
                                                                   CellularUrcSignalStrengthChangedCallback_t signalStrengthChangedCallback,
                                                                   void * pCallbackContext )
{
    ( void ) cellularHandle;
    ( void ) signalStrengthChangedCallback;
    ( void ) pCallbackContext;
    return CELLULAR_UNSUPPORTED;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetHostByName( CellularHandle_t cellularHandle,
                                        uint8_t contextId,
                                        const char * pcHostName,
                                        char * pResolvedAddress )
{
    ( void ) cellularHandle;
    ( void ) contextId;
    ( void ) pcHostName;
    ( void ) pResolvedAddress;
    return CELLULAR_UNSUPPORTED;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_DeactivatePdn( CellularHandle_t cellularHandle,
                                        uint8_t contextId )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };

    CellularAtReq_t atReqDeactPdn =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };

    cellularStatus = _Cellular_IsValidPdn( contextId );

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Make sure the library is open. */
        cellularStatus = _Cellular_CheckLibraryStatus( pContext );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "%s=%u", "AT+KCNXDOWN", contextId );
        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqDeactPdn,
                                                               CELLULAR_HL7802_AT_KCNXDOWN_TIMEOUT_MS );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_DeactivatePdn: can't deactivate PDN, PktRet: %d", pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library prototype. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncPacketSwitchStatus( CellularContext_t * pContext,
                                                                 const CellularATCommandResponse_t * pAtResp,
                                                                 void * pData,
                                                                 uint16_t dataLen )
{
    char * pInputLine = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    bool * pPacketSwitchStatus = ( bool * ) pData;

    if( pContext == NULL )
    {
        LogError( ( "PacketSwitchStatus: Invalid handle" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pData == NULL ) || ( dataLen != sizeof( bool ) ) )
    {
        LogError( ( "GetPacketSwitchStatus: Invalid param" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetPacketSwitchStatus: Input Line passed is NULL" ) );
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
            if( *pInputLine == '0' )
            {
                *pPacketSwitchStatus = false;
            }
            else if( *pInputLine == '1' )
            {
                *pPacketSwitchStatus = true;
            }
            else
            {
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularError_t _Cellular_GetPacketSwitchStatus( CellularHandle_t cellularHandle,
                                                        bool * pPacketSwitchStatus )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqPacketSwitchStatus =
    {
        "AT+CGATT?",
        CELLULAR_AT_WITH_PREFIX,
        "+CGATT",
        _Cellular_RecvFuncPacketSwitchStatus,
        pPacketSwitchStatus,
        sizeof( bool ),
    };

    /* Internal function. Callee check parameters. */
    pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqPacketSwitchStatus,
                                                           CELLULAR_HL7802_AT_TIMEOUT_60_SECONDS_MS );
    cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_ActivatePdn( CellularHandle_t cellularHandle,
                                      uint8_t contextId )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    bool packetSwitchStatus = false;

    CellularAtReq_t atReqActPdn =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };

    cellularStatus = _Cellular_IsValidPdn( contextId );

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Make sure the library is open. */
        cellularStatus = _Cellular_CheckLibraryStatus( pContext );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Check packet switch attach first. If not attached, attach packet switch first. */
        cellularStatus = _Cellular_GetPacketSwitchStatus( cellularHandle, &packetSwitchStatus );

        if( ( cellularStatus == CELLULAR_SUCCESS ) && ( packetSwitchStatus == false ) )
        {
            LogError( ( "Activate Packet switch" ) );
            ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "%s", "AT+CGATT=1" );
            pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqActPdn,
                                                                   CELLULAR_HL7802_AT_TIMEOUT_60_SECONDS_MS );
        }
        else if( cellularStatus != CELLULAR_SUCCESS )
        {
            LogError( ( "Packet switch query failed" ) );
            pktStatus = CELLULAR_PKT_STATUS_FAILURE;
        }
        else
        {
            LogInfo( ( "Packet switch attached" ) );
        }

        /* Check the current attach status. If not activated, activate the PDN context ID. */
        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "%s=%u", "AT+KCNXUP", contextId );
            pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqActPdn,
                                                                   CELLULAR_HL7802_AT_KCNXUP_TIMEOUT_MS );
        }

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_ActivatePdn: can't activate PDN, PktRet: %d", pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parsePdnStatusContextId( char * pToken,
                                                  CellularPdnStatus_t * pPdnStatusBuffers )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( ( tempValue >= ( int32_t ) CELLULAR_PDN_CONTEXT_ID_MIN ) &&
            ( tempValue <= ( int32_t ) CELLULAR_PDN_CONTEXT_ID_MAX ) )
        {
            pPdnStatusBuffers->contextId = ( uint8_t ) tempValue;
        }
        else
        {
            LogError( ( "Error in Processing Context Id. Token %s", pToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parsePdnStatusContextState( char * pToken,
                                                     CellularPdnStatus_t * pPdnStatusBuffers )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( ( tempValue >= 0 ) &&
            ( tempValue <= ( int32_t ) UINT8_MAX ) )
        {
            /* Remap the status. */
            switch( tempValue )
            {
                case CELLULAR_PDN_STATE_CONNECTED:
                    pPdnStatusBuffers->state = 1;
                    break;

                case CELLULAR_PDN_STATE_DISCONNECTED:
                case CELLULAR_PDN_STATE_CONNECTING:
                case CELLULAR_PDN_STATE_IDLE:
                case CELLULAR_PDN_STATE_DISCONNECTING:
                    pPdnStatusBuffers->state = 0;
                    break;

                default:
                    LogError( ( "parsePdnStatusContextState unknown status : %d", tempValue ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                    break;
            }
        }
        else
        {
            LogError( ( "Error in processing PDN Status Buffer state. Token %s", pToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parsePdnStatusContextType( char * pToken,
                                                    CellularPdnStatus_t * pPdnStatusBuffers )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    if( strcmp( pToken, "IPV4" ) == 0 )
    {
        pPdnStatusBuffers->pdnContextType = CELLULAR_PDN_CONTEXT_IPV4;
        pPdnStatusBuffers->ipAddress.ipAddressType = CELLULAR_IP_ADDRESS_V4;
    }
    else if( strcmp( pToken, "IPV6" ) == 0 )
    {
        pPdnStatusBuffers->pdnContextType = CELLULAR_PDN_CONTEXT_IPV6;
        pPdnStatusBuffers->ipAddress.ipAddressType = CELLULAR_IP_ADDRESS_V6;
    }
    else if( strcmp( pToken, "IPV4V6" ) == 0 )
    {
        pPdnStatusBuffers->pdnContextType = CELLULAR_PDN_CONTEXT_IPV4V6;
        /* The IP address depends on the format returned. */
    }
    else
    {
        LogError( ( "parsePdnStatusContextType : unknown token %s", pToken ) );
        atCoreStatus = CELLULAR_AT_ERROR;
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t getPdnStatusParseToken( char * pToken,
                                                 uint8_t tokenIndex,
                                                 CellularPdnStatus_t * pPdnStatusBuffers )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    switch( tokenIndex )
    {
        case ( CELLULAR_PDN_STATUS_POS_CONTEXT_ID ):
            LogDebug( ( "CELLULAR_PDN_STATUS_POS_CONTEXT_ID: %s", pToken ) );
            atCoreStatus = parsePdnStatusContextId( pToken, pPdnStatusBuffers );
            break;

        case ( CELLULAR_PDN_STATUS_POS_AF ):
            LogDebug( ( "CELLULAR_PDN_STATUS_POS_AF: %s", pToken ) );
            atCoreStatus = parsePdnStatusContextType( pToken, pPdnStatusBuffers );
            break;

        case ( CELLULAR_PDN_STATUS_POS_STATE ):
            LogDebug( ( "CELLULAR_PDN_STATUS_POS_STATE: %s", pToken ) );
            atCoreStatus = parsePdnStatusContextState( pToken, pPdnStatusBuffers );
            break;

        case ( CELLULAR_PDN_STATUS_POS_APN ):
        case ( CELLULAR_PDN_STATUS_POS_LOGIN ):
        case ( CELLULAR_PDN_STATUS_POS_PASSWORD ):
        case ( CELLULAR_PDN_STATUS_POS_IP ):
        case ( CELLULAR_PDN_STATUS_POS_GPRS ):
        case ( CELLULAR_PDN_STATUS_POS_DNS1 ):
        case ( CELLULAR_PDN_STATUS_POS_DNS2 ):
            LogDebug( ( "CELLULAR_PDN_STATUS Ignored index %d : %s", tokenIndex, pToken ) );
            atCoreStatus = CELLULAR_AT_SUCCESS;
            break;

        default:
            LogError( ( "Unknown token in getPdnStatusParseToken %s %d",
                        pToken, tokenIndex ) );
            atCoreStatus = CELLULAR_AT_ERROR;
            break;
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t getPdnStatusParseLine( char * pRespLine,
                                                CellularPdnStatus_t * pPdnStatusBuffers )
{
    char * pToken = NULL;
    char * pLocalRespLine = pRespLine;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    uint8_t tokenIndex = 0;

    atCoreStatus = Cellular_ATRemovePrefix( &pLocalRespLine );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATRemoveAllDoubleQuote( pLocalRespLine );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pLocalRespLine, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        tokenIndex = 0;

        while( ( pToken != NULL ) && ( atCoreStatus == CELLULAR_AT_SUCCESS ) )
        {
            atCoreStatus = getPdnStatusParseToken( pToken, tokenIndex, pPdnStatusBuffers );

            if( atCoreStatus != CELLULAR_AT_SUCCESS )
            {
                LogError( ( "getPdnStatusParseToken %s index %d failed", pToken, tokenIndex ) );
            }

            tokenIndex++;

            if( pLocalRespLine[ 0 ] == ',' )
            {
                pToken = pLocalRespLine;
                pLocalRespLine[ 0 ] = '\0';
                pLocalRespLine = &pLocalRespLine[ 1 ];
            }
            else
            {
                if( Cellular_ATGetNextTok( &pLocalRespLine, &pToken ) != CELLULAR_AT_SUCCESS )
                {
                    break;
                }
            }
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library types. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static CellularPktStatus_t _Cellular_RecvFuncGetPdnStatus( CellularContext_t * pContext,
                                                           const CellularATCommandResponse_t * pAtResp,
                                                           void * pData,
                                                           uint16_t dataLen )
{
    char * pRespLine = NULL;
    CellularPdnStatus_t * pPdnStatusBuffers = ( CellularPdnStatus_t * ) pData;
    uint8_t numStatusBuffers = ( uint8_t ) dataLen;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    const CellularATCommandLine_t * pCommnadItem = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetPdnStatus: invalid context" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp == NULL ) )
    {
        LogError( ( "GetPdnStatus: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pPdnStatusBuffers == NULL ) || ( numStatusBuffers < 1U ) )
    {
        LogError( ( "GetPdnStatus: PDN Status bad parameters" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetPdnStatus: no activated PDN" ) );
        pPdnStatusBuffers[ 0 ].contextId = INVALID_PDN_INDEX;
        pktStatus = CELLULAR_PKT_STATUS_OK;
    }
    else
    {
        pRespLine = pAtResp->pItm->pLine;

        pCommnadItem = pAtResp->pItm;

        while( ( numStatusBuffers != 0U ) && ( pCommnadItem != NULL ) )
        {
            pRespLine = pCommnadItem->pLine;
            atCoreStatus = getPdnStatusParseLine( pRespLine, pPdnStatusBuffers );
            pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );

            if( pktStatus != CELLULAR_PKT_STATUS_OK )
            {
                LogError( ( "getPdnStatusParseLine parse %s failed", pRespLine ) );
                break;
            }

            pPdnStatusBuffers++;
            numStatusBuffers--;
            pCommnadItem = pCommnadItem->pNext;
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
CellularError_t Cellular_GetPdnStatus( CellularHandle_t cellularHandle,
                                       CellularPdnStatus_t * pPdnStatusBuffers,
                                       uint8_t numStatusBuffers,
                                       uint8_t * pNumStatus )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    const CellularPdnStatus_t * pTempPdnStatusBuffer = pPdnStatusBuffers;
    uint8_t numBuffers = 0;
    CellularAtReq_t atReqGetPdnStatus =
    {
        "AT+KCNXCFG?",
        CELLULAR_AT_WITH_PREFIX,
        "+KCNXCFG",
        _Cellular_RecvFuncGetPdnStatus,
        pPdnStatusBuffers,
        numStatusBuffers,
    };

    /* Make sure the library is open. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( ( pTempPdnStatusBuffer == NULL ) || ( pNumStatus == NULL ) || ( numStatusBuffers < 1u ) )
    {
        LogDebug( ( "_Cellular_GetPdnStatus: Bad input Parameter " ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqGetPdnStatus,
                                                               CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS );
        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Populate the Valid number of statuses. */
        *pNumStatus = 0;
        numBuffers = numStatusBuffers;

        while( numBuffers != 0U )
        {
            /* Check if the PDN state is valid. The context ID of the first
             * invalid PDN status is set to FF. */
            if( pTempPdnStatusBuffer->contextId <= CELLULAR_PDN_CONTEXT_ID_MAX )
            {
                ( *pNumStatus ) += 1U;
            }
            else
            {
                break;
            }

            numBuffers--;
            pTempPdnStatusBuffer++;
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetEidrxSettings( CellularHandle_t cellularHandle,
                                           CellularEidrxSettingsList_t * pEidrxSettingsList )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetEidrx =
    {
        "AT+KEDRXCFG?",
        CELLULAR_AT_MULTI_WITH_PREFIX,
        "+KEDRXCFG",
        _Cellular_RecvFuncGetEidrxSettings,
        pEidrxSettingsList,
        CELLULAR_EDRX_LIST_MAX_SIZE,
    };

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pEidrxSettingsList == NULL )
    {
        LogDebug( ( "Cellular_GetEidrxSettings : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        ( void ) memset( pEidrxSettingsList, 0, sizeof( CellularEidrxSettingsList_t ) );
        /* Query the pEidrxSettings from the network. */
        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqGetEidrx,
                                                               CELLULAR_HL7802_AT_KEDRXCFG_TIMEOUT_MS );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_GetEidrxSettings: couldn't retrieve Eidrx settings" ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SetEidrxSettings( CellularHandle_t cellularHandle,
                                           const CellularEidrxSettings_t * pEidrxSettings )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSetEidrx =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pEidrxSettings == NULL )
    {
        LogDebug( ( "Cellular_SetEidrxSettings : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Form the AT command. */

        /* The return value of snprintf is not used.
         * The max length of the string is fixed and checked offline. */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "%s%u,%u,%u,%u",
                           "AT+KEDRXCFG=",
                           pEidrxSettings->mode,
                           pEidrxSettings->rat,
                           pEidrxSettings->requestedEdrxVaue,
                           pEidrxSettings->pagingTimeWindow );
        LogDebug( ( "Eidrx setting: %s ", cmdBuf ) );
        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSetEidrx,
                                                               CELLULAR_HL7802_AT_KEDRXCFG_TIMEOUT_MS );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "_Cellular_SetEidrxSettings: couldn't set Eidrx settings" ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SetRatPriority( CellularHandle_t cellularHandle,
                                         const CellularRat_t * pRatPriorities,
                                         uint8_t ratPrioritiesLength )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    uint8_t i = 0;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSetRatPriority =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( ( pRatPriorities == NULL ) || ( ratPrioritiesLength == 0U ) ||
             ( ratPrioritiesLength > ( uint8_t ) CELLULAR_MAX_RAT_PRIORITY_COUNT ) )
    {
        LogDebug( ( "Cellular_SetRatPriority : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Reboot is required for this command. */
        ( void ) strcpy( cmdBuf, "AT+KSELACQ=0," );

        for( i = 0; i < ratPrioritiesLength; i++ )
        {
            if( pRatPriorities[ i ] == CELLULAR_RAT_CATM1 )
            {
                ( void ) strcat( cmdBuf, "1" );
            }
            else if( pRatPriorities[ i ] == CELLULAR_RAT_NBIOT )
            {
                ( void ) strcat( cmdBuf, "2" );
            }
            else if( pRatPriorities[ i ] == CELLULAR_RAT_GSM )
            {
                ( void ) strcat( cmdBuf, "3" );
            }
            else
            {
                LogDebug( ( "Cellular_SetRatPriority : unsupported mode %d", pRatPriorities[ i ] ) );
                cellularStatus = CELLULAR_BAD_PARAMETER;
                break;
            }

            if( i != ( ratPrioritiesLength - 1 ) )
            {
                ( void ) strcat( cmdBuf, "," );
            }
        }

        LogError( ( " setRatPriority cmdbuf %s", cmdBuf ) );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSetRatPriority,
                                                               CELLULAR_HL7802_AT_KSELACQ_TIMEOUT_MS );
        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetRatPriority( CellularHandle_t cellularHandle,
                                         CellularRat_t * pRatPriorities,
                                         uint8_t ratPrioritiesLength,
                                         uint8_t * pReceiveRatPrioritesLength )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    uint32_t ratIndex = 0;

    CellularAtReq_t atReqSetRatPriority =
    {
        "AT+KSELACQ?",
        CELLULAR_AT_WITH_PREFIX,
        "+KSELACQ",
        _Cellular_RecvFuncGetRatPriority,
        pRatPriorities,
        ( uint16_t ) ratPrioritiesLength,
    };

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( ( pRatPriorities == NULL ) || ( ratPrioritiesLength == 0U ) ||
             ( ratPrioritiesLength > ( uint8_t ) CELLULAR_MAX_RAT_PRIORITY_COUNT ) ||
             ( pReceiveRatPrioritesLength == NULL ) )
    {
        LogDebug( ( "Cellular_GetRatPriority : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqSetRatPriority,
                                                               CELLULAR_HL7802_AT_KSELACQ_TIMEOUT_MS );

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            for( ratIndex = 0; ratIndex < ratPrioritiesLength; ratIndex++ )
            {
                if( pRatPriorities[ ratIndex ] == CELLULAR_RAT_INVALID )
                {
                    break;
                }
            }

            *pReceiveRatPrioritesLength = ratIndex;
        }

        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetSignalInfo( CellularHandle_t cellularHandle,
                                        CellularSignalInfo_t * pSignalInfo )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularRat_t rat = CELLULAR_RAT_INVALID;
    CellularAtReq_t atReqQuerySignalInfo =
    {
        "AT+CESQ",
        CELLULAR_AT_WITH_PREFIX,
        "+CESQ",
        _Cellular_RecvFuncGetSignalInfo,
        pSignalInfo,
        sizeof( CellularSignalInfo_t ),
    };

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pSignalInfo == NULL )
    {
        LogDebug( ( "Cellular_GetSignalInfo : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        cellularStatus = _Cellular_GetCurrentRat( pContext, &rat );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Init the signal value. */
        pSignalInfo->rssi = CELLULAR_INVALID_SIGNAL_VALUE;
        pSignalInfo->rsrp = CELLULAR_INVALID_SIGNAL_VALUE;
        pSignalInfo->rsrq = CELLULAR_INVALID_SIGNAL_VALUE;
        pSignalInfo->ber = CELLULAR_INVALID_SIGNAL_VALUE;
        pSignalInfo->bars = CELLULAR_INVALID_SIGNAL_BAR_VALUE;

        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atReqQuerySignalInfo,
                                                               CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS );

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            /* If the convert failed, the API will return CELLULAR_INVALID_SIGNAL_BAR_VALUE in bars field. */
            ( void ) _Cellular_ComputeSignalBars( rat, pSignalInfo );
        }

        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SetPdnConfig( CellularHandle_t cellularHandle,
                                       uint8_t contextId,
                                       const CellularPdnConfig_t * pPdnConfig )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atGprsConnectionConfighReq =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };

    /* Parameters are also checked in Cellular_CommonSetPdnConfig. */
    cellularStatus = Cellular_CommonSetPdnConfig( cellularHandle, contextId, pPdnConfig );

    /* Set the GPRS connection configuration. */
    if( cellularStatus == CELLULAR_SUCCESS )
    {
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "AT+KCNXCFG=%u,\"GPRS\",\"%s\"",
                           contextId, pPdnConfig->apnName );
        LogDebug( ( "cmd %s", cmdBuf ) );

        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atGprsConnectionConfighReq,
                                                               CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_PacketSwitchAttach: failed, PktRet: %d", pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SetPsmSettings( CellularHandle_t cellularHandle,
                                         const CellularPsmSettings_t * pPsmSettings )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atKsleepReq =
    {
        cmdBuf,
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };

    /* Parameters are checked in this function. */
    cellularStatus = Cellular_CommonSetPsmSettings( cellularHandle, pPsmSettings );

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Sleep mode driven by a HW signal (DTR). Sleep level is hibernate.
         * Can be woken up by WAKE_UP signal or T3412 timer expiration. */
        if( pPsmSettings->mode == 1 )
        {
            ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "AT+KSLEEP=0,2,30" );
        }
        else
        {
            ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "AT+KSLEEP=2" );
        }

        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext, atKsleepReq,
                                                               CELLULAR_HL7802_AT_TIMEOUT_2_SECONDS_MS );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_PacketSwitchAttach: failed, PktRet: %d", pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_Init( CellularHandle_t * pCellularHandle,
                               const CellularCommInterface_t * pCommInterface )
{
    CellularTokenTable_t cellularTokenTable =
    {
        .pCellularUrcHandlerTable              = CellularUrcHandlerTable,
        .cellularPrefixToParserMapSize         = CellularUrcHandlerTableSize,
        .pCellularSrcTokenErrorTable           = CellularSrcTokenErrorTable,
        .cellularSrcTokenErrorTableSize        = CellularSrcTokenErrorTableSize,
        .pCellularSrcTokenSuccessTable         = CellularSrcTokenSuccessTable,
        .cellularSrcTokenSuccessTableSize      = CellularSrcTokenSuccessTableSize,
        .pCellularUrcTokenWoPrefixTable        = CellularUrcTokenWoPrefixTable,
        .cellularUrcTokenWoPrefixTableSize     = CellularUrcTokenWoPrefixTableSize,
        .pCellularSrcExtraTokenSuccessTable    = NULL,
        .cellularSrcExtraTokenSuccessTableSize = 0
    };

    return Cellular_CommonInit( pCellularHandle, pCommInterface, &cellularTokenTable );
}

/*-----------------------------------------------------------*/
