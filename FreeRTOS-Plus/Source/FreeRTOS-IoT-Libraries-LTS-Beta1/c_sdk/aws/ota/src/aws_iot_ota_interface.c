/*
 * FreeRTOS OTA V1.2.0
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file aws_iot_ota_interface.c
 * @brief .
 */

/* Standard library includes. */
#include <string.h>

/* OTA inteface includes. */
#include "aws_iot_ota_interface.h"

/* OTA transport inteface includes. */

#if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) || ( configENABLED_CONTROL_PROTOCOL & OTA_CONTROL_OVER_MQTT )
    #include "mqtt/aws_iot_ota_mqtt.h"
#endif

#if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP )
    #include "http/aws_iot_ota_http.h"
#endif

/* Check if primary protocol is enabled in aws_iot_ota_agent_config.h. */

#if !( configENABLED_DATA_PROTOCOLS & configOTA_PRIMARY_DATA_PROTOCOL )
    #error "Primary data protocol must be enabled in aws_iot_ota_agent_config.h"
#endif

/*
 * Primary data protocol will be the protocol used for file download if more
 * than one protocol is selected while creating OTA job.
 */
#if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_MQTT )
    static const char * pcProtocolPriority[ OTA_DATA_NUM_PROTOCOLS ] =
    {
        "MQTT",
        "HTTP"
    };
#elif ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_HTTP )
    static const char * pcProtocolPriority[ OTA_DATA_NUM_PROTOCOLS ] =
    {
        "HTTP",
        "MQTT"
    };
#endif /* if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_MQTT ) */


void prvSetControlInterface( OTA_ControlInterface_t * pxControlInterface )
{
    #if ( configENABLED_CONTROL_PROTOCOL == OTA_CONTROL_OVER_MQTT )
        pxControlInterface->prvRequestJob = prvRequestJob_Mqtt;
        pxControlInterface->prvUpdateJobStatus = prvUpdateJobStatus_Mqtt;
    #else
    #error "Enable MQTT control as control operations are only supported over MQTT."
    #endif
}

OTA_Err_t prvSetDataInterface( OTA_DataInterface_t * pxDataInterface,
                               const uint8_t * pucProtocol )
{
    DEFINE_OTA_METHOD_NAME( "prvSetDataInterface" );

    OTA_Err_t xErr = kOTA_Err_InvalidDataProtocol;
    uint32_t i;

    for( i = 0; i < OTA_DATA_NUM_PROTOCOLS; i++ )
    {
        if( NULL != strstr( ( const char * ) pucProtocol, pcProtocolPriority[ i ] ) )
        {
            #if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT )
                if( strcmp( pcProtocolPriority[ i ], "MQTT" ) == 0 )
                {
                    pxDataInterface->prvInitFileTransfer = prvInitFileTransfer_Mqtt;
                    pxDataInterface->prvRequestFileBlock = prvRequestFileBlock_Mqtt;
                    pxDataInterface->prvDecodeFileBlock = prvDecodeFileBlock_Mqtt;
                    pxDataInterface->prvCleanup = prvCleanup_Mqtt;

                    OTA_LOG_L1( "[%s] Data interface is set to MQTT.\r\n", OTA_METHOD_NAME );

                    xErr = kOTA_Err_None;
                    break;
                }
            #endif /* if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) */

            #if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP )
                if( strcmp( pcProtocolPriority[ i ], "HTTP" ) == 0 )
                {
                    pxDataInterface->prvInitFileTransfer = _AwsIotOTA_InitFileTransfer_HTTP;
                    pxDataInterface->prvRequestFileBlock = _AwsIotOTA_RequestDataBlock_HTTP;
                    pxDataInterface->prvDecodeFileBlock = _AwsIotOTA_DecodeFileBlock_HTTP;
                    pxDataInterface->prvCleanup = _AwsIotOTA_Cleanup_HTTP;

                    OTA_LOG_L1( "[%s] Data interface is set to HTTP.\r\n", OTA_METHOD_NAME );

                    xErr = kOTA_Err_None;
                    break;
                }
            #endif /* if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) */
        }
    }

    return xErr;
}
