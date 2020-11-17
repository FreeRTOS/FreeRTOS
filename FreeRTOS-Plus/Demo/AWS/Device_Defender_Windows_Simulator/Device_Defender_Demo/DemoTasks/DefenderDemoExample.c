/*
 * FreeRTOS Kernel V10.3.0
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
 */

/* Standard includes. */
#include <stdlib.h>
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* JSON Library. */
#include "core_json.h"

/* Device Defender Client Library. */
#include "defender.h"

/* MQTT operations. */
#include "mqtt_demo_helpers.h"

/* Metrics collector. */
#include "metrics_collector.h"

/* Report builder. */
#include "report_builder.h"

/* Demo config. */
#include "demo_config.h"

/**
 * democonfigTHING_NAME is required. Throw compilation error if it is not defined.
 */
#ifndef democonfigTHING_NAME
    #error "Please define democonfigTHING_NAME to the thing name registered with AWS IoT Core in demo_config.h."
#endif

/**
 * @brief The length of #democonfigTHING_NAME.
 */
#define THING_NAME_LENGTH                 ( ( uint16_t ) ( sizeof( democonfigTHING_NAME ) - 1 ) )

/**
 * @brief Number of seconds to wait for the response from AWS IoT Device
 * Defender service.
 */
#define DEFENDER_RESPONSE_WAIT_SECONDS    ( 2 )

/**
 * @brief Status values of the device defender report.
 */
typedef enum
{
    ReportStatusNotReceived,
    ReportStatusAccepted,
    ReportStatusRejected
} ReportStatus_t;
/*-----------------------------------------------------------*/

/**
 * @brief The MQTT context used for MQTT operation.
 */
static MQTTContext_t xMqttContext;

/**
 * @brief The network context used for mbedTLS operation.
 */
static NetworkContext_t xNetworkContext;

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static uint8_t ucSharedBuffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static MQTTFixedBuffer_t xBuffer =
{
    .pBuffer = ucSharedBuffer,
    .size    = democonfigNETWORK_BUFFER_SIZE
};

/**
 * @brief Network Stats.
 */
static NetworkStats_t xNetworkStats;

/**
 * @brief Open TCP ports array.
 */
static uint16_t pusOpenTcpPorts[ democonfigOPEN_TCP_PORTS_ARRAY_SIZE ];

/**
 * @brief Open UDP ports array.
 */
static uint16_t pusOpenUdpPorts[ democonfigOPEN_UDP_PORTS_ARRAY_SIZE ];

/**
 * @brief Established connections array.
 */
static Connection_t pxEstablishedConnections[ democonfigESTABLISHED_CONNECTIONS_ARRAY_SIZE ];

/**
 * @brief All the metrics sent in the device defender report.
 */
static ReportMetrics_t xDeviceMetrics;

/**
 * @brief Report xStatus.
 */
static ReportStatus_t xReportStatus;

/**
 * @brief Buffer for generating the device defender report.
 */
static char pcDeviceMetricsJsonReport[ democonfigDEVICE_METRICS_REPORT_BUFFER_SIZE ];

/**
 * @brief Report Id sent in the defender report.
 */
static uint32_t ulReportId = 0;
/*-----------------------------------------------------------*/

/**
 * @brief Callback to receive the incoming publish messages from the MQTT broker.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] usPacketIdentifier Packet identifier of the incoming publish.
 */
static void prvPublishCallback( MQTTContext_t * pMqttContext,
                                MQTTPacketInfo_t * pPacketInfo,
                                MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Collect all the metrics to be sent in the device defender report.
 *
 * @return true if all the metrics are successfully collected;
 * false otherwise.
 */
static bool prvCollectDeviceMetrics( void );

/**
 * @brief Generate the device defender report.
 *
 * @param[out] pulOutReportLength Length of the device defender report.
 *
 * @return true if the report is generated successfully;
 * false otherwise.
 */
static bool prvGenerateDeviceMetricsReport( uint32_t * pulOutReportLength );

/**
 * @brief Subscribe to the device defender topics.
 *
 * @return true if the subscribe is successful;
 * false otherwise.
 */
static bool prvSubscribeToDefenderTopics( void );

/**
 * @brief Unsubscribe from the device defender topics.
 *
 * @return true if the unsubscribe is successful;
 * false otherwise.
 */
static bool prvUnsubscribeFromDefenderTopics( void );

/**
 * @brief Publish the generated device defender report.
 *
 * @param[in] ulReportLength Length of the device defender report.
 *
 * @return true if the report is published successfully;
 * false otherwise.
 */
static bool prvPublishDeviceMetricsReport( uint32_t ulReportLength );

/**
 * @brief Validate the response received from the AWS IoT Device Defender Service.
 *
 * This functions checks that a valid JSON is received and the value of ulReportId
 * is same as was sent in the published report.
 *
 * @param[in] pcDefenderResponse The defender response to validate.
 * @param[in] ulDefenderResponseLength Length of the defender response.
 *
 * @return true if the response is valid;
 * false otherwise.
 */
static bool prvValidateDefenderResponse( const char * pcDefenderResponse,
                                         uint32_t ulDefenderResponseLength );

/**
 * @brief The task used to demonstrate the Defender API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvDefenderDemoTask( void * pvParameters );

/*-----------------------------------------------------------*/

static bool prvValidateDefenderResponse( const char * pcDefenderResponse,
                                         uint32_t ulDefenderResponseLength )
{
    bool xStatus = false;
    JSONStatus_t eJsonResult = JSONSuccess;
    char * ucReportIdString = 0;
    size_t xReportIdStringLength;
    uint32_t ulReportIdInResponse;

    /* Is the response a valid JSON? */
    eJsonResult = JSON_Validate( pcDefenderResponse, ulDefenderResponseLength );

    if( eJsonResult != JSONSuccess )
    {
        LogError( ( "Invalid response from AWS IoT Device Defender Service: %.*s.",
                    ( int ) ulDefenderResponseLength,
                    pcDefenderResponse ) );
    }

    if( eJsonResult == JSONSuccess )
    {
        /* Search the ulReportId key in the response. */
        eJsonResult = JSON_Search( ( char * ) pcDefenderResponse,
                                   ulDefenderResponseLength,
                                   "ulReportId",
                                   sizeof( "ulReportId" ) - 1,
                                   &( ucReportIdString ),
                                   &( xReportIdStringLength ) );

        if( eJsonResult != JSONSuccess )
        {
            LogError( ( "ulReportId key not found in the response from the"
                        "AWS IoT Device Defender Service: %.*s.",
                        ( int ) ulDefenderResponseLength,
                        pcDefenderResponse ) );
        }
    }

    if( eJsonResult == JSONSuccess )
    {
        ulReportIdInResponse = ( uint32_t ) strtoul( ucReportIdString, NULL, 10 );

        /* Is the ulReportId present in the response same as was sent in the
         * published report? */
        if( ulReportIdInResponse == ulReportId )
        {
            LogInfo( ( "A valid reponse with ulReportId %u received from the "
                       "AWS IoT Device Defender Service.", ulReportId ) );
            xStatus = true;
        }
        else
        {
            LogError( ( "Unexpected ulReportId found in the response from the AWS"
                        "IoT Device Defender Service. Expected: %u, Found: %u, "
                        "Complete Response: %.*s.",
                        ulReportIdInResponse,
                        ulReportId,
                        ( int ) ulDefenderResponseLength,
                        pcDefenderResponse ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static void prvPublishCallback( MQTTContext_t * pxMqttContext,
                                MQTTPacketInfo_t * pxPacketInfo,
                                MQTTDeserializedInfo_t * pxDeserializedInfo )
{
    uint16_t usPacketIdentifier;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pxPacketInfo != NULL );
    configASSERT( pxDeserializedInfo != NULL );

    /* Suppress the unused parameter warning when asserts are disabled in
     * build. */
    ( void ) pxMqttContext;

    usPacketIdentifier = pxDeserializedInfo->packetIdentifier;

    /* Handle an incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pxPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        configASSERT( pxDeserializedInfo->pPublishInfo != NULL );

        /* Invoke the application callback for incoming publishes. */
        DefenderStatus_t status;
        DefenderTopic_t api;
        bool validationResult;
        MQTTPublishInfo_t * pPublishInfo = pxDeserializedInfo->pPublishInfo;

        /* Silence compiler warnings about unused variables. */
        ( void ) usPacketIdentifier;

        status = Defender_MatchTopic( pPublishInfo->pTopicName,
                                      pPublishInfo->topicNameLength,
                                      &( api ),
                                      NULL,
                                      NULL );

        if( status == DefenderSuccess )
        {
            if( api == DefenderJsonReportAccepted )
            {
                /* Check if the response is valid and is for the report we published. */
                validationResult = prvValidateDefenderResponse( pPublishInfo->pPayload,
                                                                pPublishInfo->payloadLength );

                if( validationResult == true )
                {
                    LogInfo( ( "The defender report was accepted by the service. Response: %.*s.",
                               ( int ) pPublishInfo->payloadLength,
                               ( const char * ) pPublishInfo->pPayload ) );
                    xReportStatus = ReportStatusAccepted;
                }
            }
            else if( api == DefenderJsonReportRejected )
            {
                /* Check if the response is valid and is for the report we published. */
                validationResult = prvValidateDefenderResponse( pPublishInfo->pPayload,
                                                                pPublishInfo->payloadLength );

                if( validationResult == true )
                {
                    LogError( ( "The defender report was rejected by the service. Response: %.*s.",
                                ( int ) pPublishInfo->payloadLength,
                                ( const char * ) pPublishInfo->pPayload ) );
                    xReportStatus = ReportStatusRejected;
                }
            }
            else
            {
                LogError( ( "Unexpected defender API : %d.", api ) );
            }
        }
        else
        {
            LogError( ( "Unexpected publish message received. Topic: %.*s, Payload: %.*s.",
                        ( int ) pPublishInfo->topicNameLength,
                        ( const char * ) pPublishInfo->pTopicName,
                        ( int ) pPublishInfo->payloadLength,
                        ( const char * ) ( pPublishInfo->pPayload ) ) );
        }
    }
    else
    {
        vHandleOtherIncomingPacket( pxPacketInfo, usPacketIdentifier );
    }
}
/*-----------------------------------------------------------*/

static bool prvCollectDeviceMetrics( void )
{
    bool xStatus = false;
    MetricsCollectorStatus_t eMetricsCollectorStatus;
    uint32_t ulNumOpenTcpPorts = 0, ulNumOpenUdpPorts = 0, ulNumEstablishedConnections = 0;

    /* Collect bytes and packets sent and received. */
    eMetricsCollectorStatus = xGetNetworkStats( &( xNetworkStats ) );

    if( eMetricsCollectorStatus != MetricsCollectorSuccess )
    {
        LogError( ( "xGetNetworkStats failed. Status: %d.",
                    eMetricsCollectorStatus ) );
    }

    /* Collect a list of open TCP ports. */
    if( eMetricsCollectorStatus == MetricsCollectorSuccess )
    {
        eMetricsCollectorStatus = xGetOpenTcpPorts( &( pusOpenTcpPorts[ 0 ] ),
                                                    democonfigOPEN_TCP_PORTS_ARRAY_SIZE,
                                                    &( ulNumOpenTcpPorts ) );

        if( eMetricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "xGetOpenTcpPorts failed. Status: %d.",
                        eMetricsCollectorStatus ) );
        }
    }

    /* Collect a list of open UDP ports. */
    if( eMetricsCollectorStatus == MetricsCollectorSuccess )
    {
        eMetricsCollectorStatus = xGetOpenUdpPorts( &( pusOpenUdpPorts[ 0 ] ),
                                                    democonfigOPEN_UDP_PORTS_ARRAY_SIZE,
                                                    &( ulNumOpenUdpPorts ) );

        if( eMetricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "xGetOpenUdpPorts failed. Status: %d.",
                        eMetricsCollectorStatus ) );
        }
    }

    /* Collect a list of established connections. */
    if( eMetricsCollectorStatus == MetricsCollectorSuccess )
    {
        eMetricsCollectorStatus = GetEstablishedConnections( &( pxEstablishedConnections[ 0 ] ),
                                                             democonfigESTABLISHED_CONNECTIONS_ARRAY_SIZE,
                                                             &( ulNumEstablishedConnections ) );

        if( eMetricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetEstablishedConnections failed. Status: %d.",
                        eMetricsCollectorStatus ) );
        }
    }

    /* Populate device metrics. */
    if( eMetricsCollectorStatus == MetricsCollectorSuccess )
    {
        xStatus = true;
        xDeviceMetrics.pxNetworkStats = &( xNetworkStats );
        xDeviceMetrics.pusOpenTcpPortsArray = &( pusOpenTcpPorts[ 0 ] );
        xDeviceMetrics.ulOpenTcpPortsArrayLength = ulNumOpenTcpPorts;
        xDeviceMetrics.pusOpenUdpPortsArray = &( pusOpenUdpPorts[ 0 ] );
        xDeviceMetrics.ulOpenUdpPortsArrayLength = ulNumOpenUdpPorts;
        xDeviceMetrics.pxEstablishedConnectionsArray = &( pxEstablishedConnections[ 0 ] );
        xDeviceMetrics.ulEstablishedConnectionsArrayLength = ulNumEstablishedConnections;
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvGenerateDeviceMetricsReport( uint32_t * pulOutReportLength )
{
    bool xStatus = false;
    ReportBuilderStatus_t eReportBuilderStatus;

    /* Generate the metrics report in the format expected by the AWS IoT Device
     * Defender Service. */
    eReportBuilderStatus = xGenerateJsonReport( &( pcDeviceMetricsJsonReport[ 0 ] ),
                                                democonfigDEVICE_METRICS_REPORT_BUFFER_SIZE,
                                                &( xDeviceMetrics ),
                                                democonfigDEVICE_METRICS_REPORT_MAJOR_VERSION,
                                                democonfigDEVICE_METRICS_REPORT_MINOR_VERSION,
                                                ulReportId,
                                                pulOutReportLength );

    if( eReportBuilderStatus != ReportBuilderSuccess )
    {
        LogError( ( "GenerateJsonReport failed. Status: %d.",
                    eReportBuilderStatus ) );
    }
    else
    {
        LogDebug( ( "Generated Report: %.*s.",
                    *pulOutReportLength,
                    &( pcDeviceMetricsJsonReport[ 0 ] ) ) );
        xStatus = true;
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvSubscribeToDefenderTopics( void )
{
    bool xStatus = false;

    xStatus = xSubscribeToTopic( &xMqttContext,
                                 DEFENDER_API_JSON_ACCEPTED( democonfigTHING_NAME ),
                                 DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ) );

    if( xStatus == true )
    {
        xStatus = xSubscribeToTopic( &xMqttContext,
                                     DEFENDER_API_JSON_REJECTED( democonfigTHING_NAME ),
                                     DEFENDER_API_LENGTH_JSON_REJECTED( THING_NAME_LENGTH ) );
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvUnsubscribeFromDefenderTopics( void )
{
    bool xStatus = false;

    xStatus = xUnsubscribeFromTopic( &xMqttContext,
                                     DEFENDER_API_JSON_ACCEPTED( democonfigTHING_NAME ),
                                     DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ) );

    if( xStatus == true )
    {
        xStatus = xUnsubscribeFromTopic( &xMqttContext,
                                         DEFENDER_API_JSON_REJECTED( democonfigTHING_NAME ),
                                         DEFENDER_API_LENGTH_JSON_REJECTED( THING_NAME_LENGTH ) );
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvPublishDeviceMetricsReport( uint32_t reportLength )
{
    return xPublishToTopic( &xMqttContext,
                            DEFENDER_API_JSON_PUBLISH( democonfigTHING_NAME ),
                            DEFENDER_API_LENGTH_JSON_PUBLISH( THING_NAME_LENGTH ),
                            &( pcDeviceMetricsJsonReport[ 0 ] ),
                            reportLength );
}
/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the Device Defender library API via a
 * MQTT mutually authenticated network connection with the AWS IoT broker.
 */
void vStartDefenderDemo( void )
{
    /* This example uses a single application task, which shows that how to
     * use Device Defender library to generate and validate AWS IoT Device Defender
     * MQTT topics, and use the coreMQTT library to communicate with the AWS IoT
     * Device Defender service. */
    xTaskCreate( prvDefenderDemoTask,      /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

void prvDefenderDemoTask( void * pvParameters )
{
    bool xStatus = false;
    BaseType_t xExitStatus = EXIT_FAILURE;
    uint32_t ulReportLength = 0, i, ulMqttSessionEstablished = 0;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Start with report not received. */
    xReportStatus = ReportStatusNotReceived;

    /* Set a report Id to be used. */
    ulReportId = 1;

    LogInfo( ( "Establishing MQTT session..." ) );
    xStatus = xEstablishMqttSession( &xMqttContext,
                                     &xNetworkContext,
                                     &xBuffer,
                                     prvPublishCallback );

    if( xStatus != true )
    {
        LogError( ( "Failed to establish MQTT session." ) );
    }
    else
    {
        ulMqttSessionEstablished = 1;
    }

    if( xStatus == true )
    {
        LogInfo( ( "Subscribing to defender topics..." ) );
        xStatus = prvSubscribeToDefenderTopics();

        if( xStatus != true )
        {
            LogError( ( "Failed to subscribe to defender topics." ) );
        }
    }

    if( xStatus == true )
    {
        LogInfo( ( "Collecting device metrics..." ) );
        xStatus = prvCollectDeviceMetrics();

        if( xStatus != true )
        {
            LogError( ( "Failed to collect device metrics." ) );
        }
    }

    if( xStatus == true )
    {
        LogInfo( ( "Generating device defender report..." ) );
        xStatus = prvGenerateDeviceMetricsReport( &( ulReportLength ) );

        if( xStatus != true )
        {
            LogError( ( "Failed to generate device defender report." ) );
        }
    }

    if( xStatus == true )
    {
        LogInfo( ( "Publishing device defender report..." ) );
        xStatus = prvPublishDeviceMetricsReport( ulReportLength );

        if( xStatus != true )
        {
            LogError( ( "Failed to publish device defender report." ) );
        }
    }

    if( xStatus == true )
    {
        for( i = 0; i < DEFENDER_RESPONSE_WAIT_SECONDS; i++ )
        {
            ( void ) xProcessLoop( &xMqttContext );

            /* xReportStatus is updated in the prvPublishCallback. */
            if( xReportStatus != ReportStatusNotReceived )
            {
                break;
            }

            /* Wait for sometime between consecutive executions of ProcessLoop. */
            vTaskDelay( 1000 / portTICK_PERIOD_MS );
        }
    }

    if( xReportStatus == ReportStatusNotReceived )
    {
        LogError( ( "Failed to receive response from AWS IoT Device Defender Service." ) );
        xStatus = false;
    }

    /* Unsubscribe and disconnect if MQTT session was established. Per the MQTT
     * protocol spec, it is okay to send UNSUBSCRIBE even if no corresponding
     * subscription exists on the broker. Therefore, it is okay to attempt
     * unsubscribe even if one more subscribe failed earlier. */
    if( ulMqttSessionEstablished == 1 )
    {
        LogInfo( ( "Unsubscribing from defender topics..." ) );
        xStatus = prvUnsubscribeFromDefenderTopics();

        if( xStatus != true )
        {
            LogError( ( "Failed to unsubscribe from defender topics." ) );
        }

        LogInfo( ( "Closing MQTT session..." ) );
        ( void ) xDisconnectMqttSession( &xMqttContext,
                                         &xNetworkContext );
    }

    if( ( xStatus == true ) && ( xReportStatus == ReportStatusAccepted ) )
    {
        xExitStatus = EXIT_SUCCESS;
        LogInfo( ( "Demo completed successfully." ) );
    }
    else
    {
        LogError( ( "Demo failed." ) );
    }

    /* Delete this task. */
    LogInfo( ( "Deleting Defender Demo task." ) );
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/
