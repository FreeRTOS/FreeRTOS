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

#ifndef __CELLULAR_R4_H__
#define __CELLULAR_R4_H__

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/*-----------------------------------------------------------*/

#define MIN_TCP_SESSION_ID          ( 0 )
#define MAX_TCP_SESSION_ID          ( 6 )
#define TCP_SESSION_TABLE_LEGNTH    ( MAX_TCP_SESSION_ID + 1 )

#define INVALID_SOCKET_INDEX        ( UINT32_MAX )
#define INVALID_SESSION_ID          ( UINT32_MAX )

/*-----------------------------------------------------------*/

typedef struct cellularModuleContext
{
    uint32_t pSessionMap[ TCP_SESSION_TABLE_LEGNTH ];
} cellularModuleContext_t;

/*-----------------------------------------------------------*/

uint32_t _Cellular_GetSocketId( CellularContext_t * pContext,
                                uint8_t sessionId );

uint32_t _Cellular_GetSessionId( CellularContext_t * pContext,
                                 uint32_t socketIndex );

CellularError_t rebootCellularModem( CellularContext_t * pContext,
                                     bool disablePsm,
                                     bool disableEidrx );

/*-----------------------------------------------------------*/

/**
 * @brief Cellular MNO profiles.
 */
typedef enum MNOProfileType
{
    MNO_PROFILE_SW_DEFAULT = 0,
    MNO_PROFILE_SIM_ICCID_IMSI_SELECT = 1,
    MNO_PROFILE_ATT = 2,
    MNO_PROFILE_VERIZON = 3,
    MNO_PROFILE_TELSTRA = 4,
    MNO_PROFILE_TMOBILE = 5,
    MNO_PROFILE_CHINA_TELECOM = 6,
    MNO_PROFILE_SPRINT = 8,
    MNO_PROFILE_VODAFONE = 19,
    MNO_PROFILE_GLOBAL = 90,
    MNO_PROFILE_STANDARD_EUROPE = 100,
    MNO_PROFILE_NOT_SET = 999
} MNOProfileType_t;

/*-----------------------------------------------------------*/

/* Select network MNO profile. Default value is MNO_PROFILE_NOT_SET */
#ifndef CELLULAR_CONFIG_SARA_R4_SET_MNO_PROFILE
    #define CELLULAR_CONFIG_SARA_R4_SET_MNO_PROFILE    ( MNO_PROFILE_NOT_SET )
#endif

/*
 * By default socket is closed in normal mode i.e. <async_close> flag is 0.
 * In normal mode, +USOCL can take time to close socket (Max timeout is 120 sec).
 * To avoid wait, socket can be closed in async mode via <async_close> flag.
 * In <async_close> mode, socket close will be notified via +UUSOCL URC.
 * Drawback of <async_close> mode is that if try to deactivate context (e.g. AT+CGACT=0,1).
 * prior to socket close URC, AT command will result in ERROR.
 */
#define CELLULAR_CONFIG_SET_SOCKET_CLOSE_ASYNC_MODE    ( 0U )

/*-----------------------------------------------------------*/

/* MAX valid PDP contexts */
#define MAX_PDP_CONTEXTS                     ( 4U )

#define DEFAULT_BEARER_CONTEXT_ID            ( 1U )        /* SARA-R4 default bearer context */

#define CELULAR_PDN_CONTEXT_TYPE_MAX_SIZE    ( 7U )        /* The length of IP type e.g. IPV4V6. */

/*-----------------------------------------------------------*/

/* +CGDCONT PDN context definition tokens */
#define CELLULAR_PDN_STATUS_POS_CONTEXT_ID           ( 0U )
#define CELLULAR_PDN_STATUS_POS_CONTEXT_TYPE         ( 1U )
#define CELLULAR_PDN_STATUS_POS_APN_NAME             ( 2U )
#define CELLULAR_PDN_STATUS_POS_IP_ADDRESS           ( 3U )

/* +CGACT PDN context activation tokens */
#define CELLULAR_PDN_ACT_STATUS_POS_CONTEXT_ID       ( 0U )
#define CELLULAR_PDN_ACT_STATUS_POS_CONTEXT_STATE    ( 1U )

/**
 * @brief Context info from +CGDCONT (Context IP type, APN name, IP Address)
 */
typedef struct CellularPdnContextInfo
{
    bool contextsPresent[ MAX_PDP_CONTEXTS ];                             /**< Context present in +CGDCONT response or not. */
    char ipType[ MAX_PDP_CONTEXTS ][ CELULAR_PDN_CONTEXT_TYPE_MAX_SIZE ]; /**< PDN Context type. */
    char apnName[ MAX_PDP_CONTEXTS ][ CELLULAR_APN_MAX_SIZE ];            /**< APN name. */
    char ipAddress[ MAX_PDP_CONTEXTS ][ CELLULAR_IP_ADDRESS_MAX_SIZE ];   /**< IP address. */
} CellularPdnContextInfo_t;

/**
 * @brief Context <Act> state from +CGACT
 */
typedef struct CellularPdnContextActInfo
{
    bool contextsPresent[ MAX_PDP_CONTEXTS ]; /**< Context present in +CGACT response or not. */
    bool contextActState[ MAX_PDP_CONTEXTS ]; /**< Context active state from +CGACT response. */
} CellularPdnContextActInfo_t;

/*-----------------------------------------------------------*/

extern CellularAtParseTokenMap_t CellularUrcHandlerTable[];
extern uint32_t CellularUrcHandlerTableSize;

extern const char * CellularSrcTokenErrorTable[];
extern uint32_t CellularSrcTokenErrorTableSize;

extern const char * CellularSrcTokenSuccessTable[];
extern uint32_t CellularSrcTokenSuccessTableSize;

extern const char * CellularUrcTokenWoPrefixTable[];
extern uint32_t CellularUrcTokenWoPrefixTableSize;

/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef __CELLULAR_R4_H__ */
