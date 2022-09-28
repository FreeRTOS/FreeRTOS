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

/* The config header is always included first. */
#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Standard includes. */
#include <stdio.h>
#include <string.h>

#include "cellular_platform.h"
#include "cellular_types.h"
#include "cellular_api.h"
#include "cellular_common.h"
#include "cellular_common_api.h"

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_Cleanup( CellularHandle_t cellularHandle )
{
    return Cellular_CommonCleanup( cellularHandle );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_RegisterUrcNetworkRegistrationEventCallback( CellularHandle_t cellularHandle,
                                                                      CellularUrcNetworkRegistrationCallback_t networkRegistrationCallback,
                                                                      void * pCallbackContext )
{
    return Cellular_CommonRegisterUrcNetworkRegistrationEventCallback( cellularHandle, networkRegistrationCallback, pCallbackContext );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_RegisterUrcPdnEventCallback( CellularHandle_t cellularHandle,
                                                      CellularUrcPdnEventCallback_t pdnEventCallback,
                                                      void * pCallbackContext )
{
    return Cellular_CommonRegisterUrcPdnEventCallback( cellularHandle, pdnEventCallback, pCallbackContext );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_RegisterUrcGenericCallback( CellularHandle_t cellularHandle,
                                                     CellularUrcGenericCallback_t genericCallback,
                                                     void * pCallbackContext )
{
    return Cellular_CommonRegisterUrcGenericCallback( cellularHandle, genericCallback, pCallbackContext );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_RegisterModemEventCallback( CellularHandle_t cellularHandle,
                                                     CellularModemEventCallback_t modemEventCallback,
                                                     void * pCallbackContext )
{
    return Cellular_CommonRegisterModemEventCallback( cellularHandle, modemEventCallback, pCallbackContext );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_ATCommandRaw( CellularHandle_t cellularHandle,
                                       const char * pATCommandPrefix,
                                       const char * pATCommandPayload,
                                       CellularATCommandType_t atCommandType,
                                       CellularATCommandResponseReceivedCallback_t responseReceivedCallback,
                                       void * pData,
                                       uint16_t dataLen )
{
    return Cellular_CommonATCommandRaw( cellularHandle, pATCommandPrefix, pATCommandPayload, atCommandType,
                                        responseReceivedCallback, pData, dataLen );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_CreateSocket( CellularHandle_t cellularHandle,
                                       uint8_t pdnContextId,
                                       CellularSocketDomain_t socketDomain,
                                       CellularSocketType_t socketType,
                                       CellularSocketProtocol_t socketProtocol,
                                       CellularSocketHandle_t * pSocketHandle )
{
    return Cellular_CommonCreateSocket( cellularHandle, pdnContextId, socketDomain, socketType,
                                        socketProtocol, pSocketHandle );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SocketSetSockOpt( CellularHandle_t cellularHandle,
                                           CellularSocketHandle_t socketHandle,
                                           CellularSocketOptionLevel_t optionLevel,
                                           CellularSocketOption_t option,
                                           const uint8_t * pOptionValue,
                                           uint32_t optionValueLength )
{
    return Cellular_CommonSocketSetSockOpt( cellularHandle, socketHandle, optionLevel, option,
                                            pOptionValue, optionValueLength );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SocketRegisterDataReadyCallback( CellularHandle_t cellularHandle,
                                                          CellularSocketHandle_t socketHandle,
                                                          CellularSocketDataReadyCallback_t dataReadyCallback,
                                                          void * pCallbackContext )
{
    return Cellular_CommonSocketRegisterDataReadyCallback( cellularHandle, socketHandle,
                                                           dataReadyCallback, pCallbackContext );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SocketRegisterSocketOpenCallback( CellularHandle_t cellularHandle,
                                                           CellularSocketHandle_t socketHandle,
                                                           CellularSocketOpenCallback_t socketOpenCallback,
                                                           void * pCallbackContext )
{
    return Cellular_CommonSocketRegisterSocketOpenCallback( cellularHandle, socketHandle,
                                                            socketOpenCallback, pCallbackContext );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_SocketRegisterClosedCallback( CellularHandle_t cellularHandle,
                                                       CellularSocketHandle_t socketHandle,
                                                       CellularSocketClosedCallback_t closedCallback,
                                                       void * pCallbackContext )
{
    return Cellular_CommonSocketRegisterClosedCallback( cellularHandle, socketHandle,
                                                        closedCallback, pCallbackContext );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_RfOn( CellularHandle_t cellularHandle )
{
    return Cellular_CommonRfOn( cellularHandle );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_RfOff( CellularHandle_t cellularHandle )
{
    return Cellular_CommonRfOff( cellularHandle );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetIPAddress( CellularHandle_t cellularHandle,
                                       uint8_t contextId,
                                       char * pBuffer,
                                       uint32_t bufferLength )
{
    return Cellular_CommonGetIPAddress( cellularHandle, contextId, pBuffer, bufferLength );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetModemInfo( CellularHandle_t cellularHandle,
                                       CellularModemInfo_t * pModemInfo )
{
    return Cellular_CommonGetModemInfo( cellularHandle, pModemInfo );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetRegisteredNetwork( CellularHandle_t cellularHandle,
                                               CellularPlmnInfo_t * pNetworkInfo )
{
    return Cellular_CommonGetRegisteredNetwork( cellularHandle, pNetworkInfo );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetNetworkTime( CellularHandle_t cellularHandle,
                                         CellularTime_t * pNetworkTime )
{
    return Cellular_CommonGetNetworkTime( cellularHandle, pNetworkTime );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetServiceStatus( CellularHandle_t cellularHandle,
                                           CellularServiceStatus_t * pServiceStatus )
{
    return Cellular_CommonGetServiceStatus( cellularHandle, pServiceStatus );
}

/*-----------------------------------------------------------*/

/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetSimCardInfo( CellularHandle_t cellularHandle,
                                         CellularSimCardInfo_t * pSimCardInfo )
{
    return Cellular_CommonGetSimCardInfo( cellularHandle, pSimCardInfo );
}

/*-----------------------------------------------------------*/


/* FreeRTOS Cellular Library API. */
/* coverity[misra_c_2012_rule_8_7_violation] */
CellularError_t Cellular_GetPsmSettings( CellularHandle_t cellularHandle,
                                         CellularPsmSettings_t * pPsmSettings )
{
    return Cellular_CommonGetPsmSettings( cellularHandle, pPsmSettings );
}

/*-----------------------------------------------------------*/
