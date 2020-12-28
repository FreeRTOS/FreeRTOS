/*
 * FreeRTOS V202012.00
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
 *
 */

/*
 * Demo for showing how to use the Device Defender library's APIs. The Device
 * Defender library provides macros and helper functions for assembling MQTT
 * topics strings, and for determining whether an incoming MQTT message is
 * related to device defender. The Device Defender library does not depend on
 * any particular MQTT library, therefore the code for MQTT operations is
 * placed in another file (mqtt_demo_helpers.c). This demo uses the coreMQTT
 * library. If needed, mqtt_demo_helpers.c can be modified to replace coreMQTT
 * with another MQTT library. This demo requires using the AWS IoT broker as
 * Device Defender is an AWS service.
 *
 * This demo connects to the AWS IoT broker and subscribes to the device
 * defender topics. It then collects metrics for the open ports and sockets on
 * the device using FreeRTOS+TCP, and generates a device defender report. The
 * report is then published, and the demo waits for a response from the device
 * defender service. Upon receiving the response or timing out, the demo
 * finishes.
 *
 * This demo sets the report ID to xTaskGetTickCount(), which may collide if
 * the device is reset. Reports for a Thing with a previously used report ID
 * will be assumed to be duplicates and discarded by the Device Defender
 * service. The report ID needs to be unique per report sent with a given
 * Thing. We recommend using an increasing unique id such as the current
 * timestamp.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo config. */
#include "demo_config.h"

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

/**
 * democonfigTHING_NAME is required. Throw compilation error if it is not defined.
 */
#ifndef democonfigTHING_NAME
    #error "Please define democonfigTHING_NAME to the thing name registered with AWS IoT Core in demo_config.h."
#endif

/**
 * @brief The length of #democonfigTHING_NAME.
 */
#define THING_NAME_LENGTH                           ( ( uint16_t ) ( sizeof( democonfigTHING_NAME ) - 1 ) )

/**
 * @brief Number of seconds to wait for the response from AWS IoT Device
 * Defender service.
 */
#define DEFENDER_RESPONSE_WAIT_SECONDS              ( 2 )

/**
 * @brief Name of the report id field in the response from the AWS IoT Device
 * Defender service.
 */
#define DEFENDER_RESPONSE_REPORT_ID_FIELD           "reportId"

/**
 * @brief The length of #DEFENDER_RESPONSE_REPORT_ID_FIELD.
 */
#define DEFENDER_RESPONSE_REPORT_ID_FIELD_LENGTH    ( sizeof( DEFENDER_RESPONSE_REPORT_ID_FIELD ) - 1 )

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef DEFENDER_MAX_DEMO_LOOP_COUNT
    #define DEFENDER_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in ticks to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_TICKS    ( pdMS_TO_TICKS( 5000U ) )

/**
 * @brief Status values of the device defender report.
 */
typedef enum
{
    ReportStatusNotReceived,
    ReportStatusAccepted,
    ReportStatusRejected
} ReportStatus_t;

/** 
 * @brief Each compilation unit that consumes the NetworkContext must define it. 
 * It should contain a single pointer to the type of your desired transport.
 * When using multiple transports in the same compilation unit, define this pointer as void *.
 *
 * @note Transport stacks are defined in FreeRTOS-Plus/Source/Application-Protocols/network_transport.
 */
struct NetworkContext
{
    TlsTransportParams_t * pParams;
};
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
 * @brief The parameters for the network context using mbedTLS operation.
 */
static TlsTransportParams_t xTlsTransportParams;

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static uint8_t ucSharedBuffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static MQTTFixedBuffer_t xBuffer =
{
    ucSharedBuffer,
    democonfigNETWORK_BUFFER_SIZE
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
 * @brief Report status.
 */
static ReportStatus_t xReportStatus;

/**
 * @brief Buffer for generating the device defender report.
 */
static char pcDeviceMetricsJsonReport[ democonfigDEVICE_METRICS_REPORT_BUFFER_SIZE ];

/**
 * @brief Report Id sent in the defender report.
 */
static uint32_t ulReportId = 0UL;
/*-----------------------------------------------------------*/

/**
 * @brief Callback to receive the incoming publish messages from the MQTT broker.
 *
 * @param[in] pxMqttContext The MQTT context for the MQTT connection.
 * @param[in] pxPacketInfo Pointer to publish info of the incoming publish.
 * @param[in] pxDeserializedInfo Deserialized information from the incoming publish.
 */
static void prvPublishCallback( MQTTContext_t * pxMqttContext,
                                MQTTPacketInfo_t * pxPacketInfo,
                                MQTTDeserializedInfo_t * pxDeserializedInfo );

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
 * This functions checks that a valid JSON is received and the report ID
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
 * This task collects metrics from the device using the functions in
 * metrics_collector.h and uses them to build a defender report using functions
 * in report_builder.h. Metrics include the number for bytes written and read
 * over the network, open TCP and UDP ports, and open TCP sockets. The
 * generated report is then published to the AWS IoT Device Defender service.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation.
 * Not used in this example.
 */
static void prvDefenderDemoTask( void * pvParameters );

/*-----------------------------------------------------------*/

static bool prvValidateDefenderResponse( const char * pcDefenderResponse,
                                         uint32_t ulDefenderResponseLength )
{
    bool xStatus = false;
    JSONStatus_t eJsonResult = JSONSuccess;
    char * ucReportIdString = NULL;
    size_t xReportIdStringLength;
    uint32_t ulReportIdInResponse;

    configASSERT( pcDefenderResponse != NULL );

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
        /* Search the ReportId key in the response. */
        eJsonResult = JSON_Search( ( char * ) pcDefenderResponse,
                                   ulDefenderResponseLength,
                                   DEFENDER_RESPONSE_REPORT_ID_FIELD,
                                   DEFENDER_RESPONSE_REPORT_ID_FIELD_LENGTH,
                                   &( ucReportIdString ),
                                   &( xReportIdStringLength ) );

        if( eJsonResult != JSONSuccess )
        {
            LogError( ( "%s key not found in the response from the"
                        "AWS IoT Device Defender Service: %.*s.",
                        DEFENDER_RESPONSE_REPORT_ID_FIELD,
                        ( int ) ulDefenderResponseLength,
                        pcDefenderResponse ) );
        }
    }

    if( eJsonResult == JSONSuccess )
    {
        ulReportIdInResponse = ( uint32_t ) strtoul( ucReportIdString, NULL, 10 );

        /* Is the report ID present in the response same as was sent in the
         * published report? */
        if( ulReportIdInResponse == ulReportId )
        {
            LogInfo( ( "A valid response with report ID %u received from the "
                       "AWS IoT Device Defender Service.", ulReportId ) );
            xStatus = true;
        }
        else
        {
            LogError( ( "Unexpected %s found in the response from the AWS"
                        "IoT Device Defender Service. Expected: %u, Found: %u, "
                        "Complete Response: %.*s.",
                        DEFENDER_RESPONSE_REPORT_ID_FIELD,
                        ulReportId,
                        ulReportIdInResponse,
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
    DefenderStatus_t xStatus;
    DefenderTopic_t xApi;
    bool xValidationResult;
    MQTTPublishInfo_t * pxPublishInfo;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pxPacketInfo != NULL );
    configASSERT( pxDeserializedInfo != NULL );

    /* Suppress the unused parameter warning when asserts are disabled in
     * build. */
    ( void ) pxMqttContext;

    /* Handle an incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pxPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        configASSERT( pxDeserializedInfo->pPublishInfo != NULL );

        pxPublishInfo = pxDeserializedInfo->pPublishInfo;

        /* Verify that the publish is for device defender, and if so get which
         * defender API it is for */
        xStatus = Defender_MatchTopic( pxPublishInfo->pTopicName,
                                       pxPublishInfo->topicNameLength,
                                       &( xApi ),
                                       NULL,
                                       NULL );

        if( xStatus == DefenderSuccess )
        {
            if( xApi == DefenderJsonReportAccepted )
            {
                /* Check if the response is valid and is for the report we
                 * published. If so, report was accepted. */
                xValidationResult = prvValidateDefenderResponse( pxPublishInfo->pPayload,
                                                                 pxPublishInfo->payloadLength );

                if( xValidationResult == true )
                {
                    LogInfo( ( "The defender report was accepted by the service. Response: %.*s.",
                               ( int ) pxPublishInfo->payloadLength,
                               ( const char * ) pxPublishInfo->pPayload ) );
                    xReportStatus = ReportStatusAccepted;
                }
            }
            else if( xApi == DefenderJsonReportRejected )
            {
                /* Check if the response is valid and is for the report we
                 * published. If so, report was rejected. */
                xValidationResult = prvValidateDefenderResponse( pxPublishInfo->pPayload,
                                                                 pxPublishInfo->payloadLength );

                if( xValidationResult == true )
                {
                    LogError( ( "The defender report was rejected by the service. Response: %.*s.",
                                ( int ) pxPublishInfo->payloadLength,
                                ( const char * ) pxPublishInfo->pPayload ) );
                    xReportStatus = ReportStatusRejected;
                }
            }
            else
            {
                LogError( ( "Unexpected defender API : %d.", xApi ) );
            }
        }
        else
        {
            LogError( ( "Unexpected publish message received. Topic: %.*s, Payload: %.*s.",
                        ( int ) pxPublishInfo->topicNameLength,
                        ( const char * ) pxPublishInfo->pTopicName,
                        ( int ) pxPublishInfo->payloadLength,
                        ( const char * ) ( pxPublishInfo->pPayload ) ) );
        }
    }
    else
    {
        vHandleOtherIncomingPacket( pxPacketInfo, pxDeserializedInfo->packetIdentifier );
    }
}
/*-----------------------------------------------------------*/

static bool prvCollectDeviceMetrics( void )
{
    bool xStatus = false;
    eMetricsCollectorStatus eMetricsCollectorStatus;
    uint32_t ulNumOpenTcpPorts = 0UL, ulNumOpenUdpPorts = 0UL, ulNumEstablishedConnections = 0UL;

    /* Collect bytes and packets sent and received. */
    eMetricsCollectorStatus = eGetNetworkStats( &( xNetworkStats ) );

    if( eMetricsCollectorStatus != eMetricsCollectorSuccess )
    {
        LogError( ( "xGetNetworkStats failed. Status: %d.",
                    eMetricsCollectorStatus ) );
    }

    /* Collect a list of open TCP ports. */
    if( eMetricsCollectorStatus == eMetricsCollectorSuccess )
    {
        eMetricsCollectorStatus = eGetOpenTcpPorts( &( pusOpenTcpPorts[ 0 ] ),
                                                    democonfigOPEN_TCP_PORTS_ARRAY_SIZE,
                                                    &( ulNumOpenTcpPorts ) );

        if( eMetricsCollectorStatus != eMetricsCollectorSuccess )
        {
            LogError( ( "xGetOpenTcpPorts failed. Status: %d.",
                        eMetricsCollectorStatus ) );
        }
    }

    /* Collect a list of open UDP ports. */
    if( eMetricsCollectorStatus == eMetricsCollectorSuccess )
    {
        eMetricsCollectorStatus = eGetOpenUdpPorts( &( pusOpenUdpPorts[ 0 ] ),
                                                    democonfigOPEN_UDP_PORTS_ARRAY_SIZE,
                                                    &( ulNumOpenUdpPorts ) );

        if( eMetricsCollectorStatus != eMetricsCollectorSuccess )
        {
            LogError( ( "xGetOpenUdpPorts failed. Status: %d.",
                        eMetricsCollectorStatus ) );
        }
    }

    /* Collect a list of established connections. */
    if( eMetricsCollectorStatus == eMetricsCollectorSuccess )
    {
        eMetricsCollectorStatus = eGetEstablishedConnections( &( pxEstablishedConnections[ 0 ] ),
                                                              democonfigESTABLISHED_CONNECTIONS_ARRAY_SIZE,
                                                              &( ulNumEstablishedConnections ) );

        if( eMetricsCollectorStatus != eMetricsCollectorSuccess )
        {
            LogError( ( "GetEstablishedConnections failed. Status: %d.",
                        eMetricsCollectorStatus ) );
        }
    }

    /* Populate device metrics. */
    if( eMetricsCollectorStatus == eMetricsCollectorSuccess )
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
    eReportBuilderStatus eReportBuilderStatus;

    /* Generate the metrics report in the format expected by the AWS IoT Device
     * Defender Service. */
    eReportBuilderStatus = eGenerateJsonReport( &( pcDeviceMetricsJsonReport[ 0 ] ),
                                                democonfigDEVICE_METRICS_REPORT_BUFFER_SIZE,
                                                &( xDeviceMetrics ),
                                                democonfigDEVICE_METRICS_REPORT_MAJOR_VERSION,
                                                democonfigDEVICE_METRICS_REPORT_MINOR_VERSION,
                                                ulReportId,
                                                pulOutReportLength );

    if( eReportBuilderStatus != eReportBuilderSuccess )
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

    /* Subscribe to defender topic for responses for accepted reports. */
    xStatus = xSubscribeToTopic( &xMqttContext,
                                 DEFENDER_API_JSON_ACCEPTED( democonfigTHING_NAME ),
                                 DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ) );

    if( xStatus == false )
    {
        LogError( ( "Failed to subscribe to defender topic: %.*s.",
                    DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ),
                    DEFENDER_API_JSON_ACCEPTED( democonfigTHING_NAME ) ) );
    }

    if( xStatus == true )
    {
        /* Subscribe to defender topic for responses for rejected reports. */
        xStatus = xSubscribeToTopic( &xMqttContext,
                                     DEFENDER_API_JSON_REJECTED( democonfigTHING_NAME ),
                                     DEFENDER_API_LENGTH_JSON_REJECTED( THING_NAME_LENGTH ) );

        if( xStatus == false )
        {
            LogError( ( "Failed to subscribe to defender topic: %.*s.",
                        DEFENDER_API_LENGTH_JSON_REJECTED( THING_NAME_LENGTH ),
                        DEFENDER_API_JSON_REJECTED( democonfigTHING_NAME ) ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvUnsubscribeFromDefenderTopics( void )
{
    bool xStatus = false;

    /* Unsubscribe from defender accepted topic. */
    xStatus = xUnsubscribeFromTopic( &xMqttContext,
                                     DEFENDER_API_JSON_ACCEPTED( democonfigTHING_NAME ),
                                     DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ) );

    if( xStatus == true )
    {
        /* Unsubscribe from defender rejected topic. */
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

/**
 * @brief Create the task that demonstrates the Device Defender library API via
 * a mutually authenticated MQTT connection with the AWS IoT broker.
 */
void vStartDefenderDemo( void )
{
    /* This example uses a single application task, which shows that how to use
     * Device Defender library to generate and validate AWS IoT Device Defender
     * MQTT topics, and use the coreMQTT library to communicate with the AWS
     * IoT Device Defender service. */
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
    uint32_t ulReportLength = 0UL, i, ulMqttSessionEstablished = 0UL;
    UBaseType_t uxDemoRunCount = 0UL;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pParams = &xTlsTransportParams;

    /* Start with report not received. */
    xReportStatus = ReportStatusNotReceived;

    /* This demo runs a single loop unless there are failures in the demo execution.
     * In case of failures in the demo execution, demo loop will be retried for up to
     * DEFENDER_MAX_DEMO_LOOP_COUNT times. */
    do
    {
        /* Set a report Id to be used.
         *
         * !!!NOTE!!!
         * This demo sets the report ID to xTaskGetTickCount(), which may collide
         * if the device is reset. Reports for a Thing with a previously used
         * report ID will be assumed to be duplicates and discarded by the Device
         * Defender service. The report ID needs to be unique per report sent with
         * a given Thing. We recommend using an increasing unique id such as the
         * current timestamp. */
        ulReportId = ( uint32_t ) xTaskGetTickCount();

        /****************************** Connect. ******************************/

        /* Attempts to connect to the AWS IoT MQTT broker over TCP. If the
         * connection fails, retries after a timeout. Timeout value will
         * exponentially increase until maximum attempts are reached. */
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

        /******************** Subscribe to Defender topics. *******************/

        /* Attempt to subscribe to the AWS IoT Device Defender topics.
         * Since this demo is using JSON, in prvSubscribeToDefenderTopics() we
         * subscribe to the topics to which accepted and rejected responses are
         * received from after publishing a JSON report.
         *
         * This demo uses a constant #democonfigTHING_NAME known at compile time
         * therefore we use macros to assemble defender topic strings.
         * If the thing name is known at run time, then we could use the API
         * #Defender_GetTopic instead.
         *
         * For example, for the JSON accepted responses topic:
         *
         * #define TOPIC_BUFFER_LENGTH      ( 256U )
         *
         * // Every device should have a unique thing name registered with AWS IoT Core.
         * // This example assumes that the device has a unique serial number which is
         * // registered as the thing name with AWS IoT Core.
         * const char * pThingName = GetDeviceSerialNumber();
         * uint16_t thingNameLength = ( uint16_t )strlen( pThingname );
         * char topicBuffer[ TOPIC_BUFFER_LENGTH ] = { 0 };
         * uint16_t topicLength = 0;
         * DefenderStatus_t status = DefenderSuccess;
         *
         * status = Defender_GetTopic( &( topicBuffer[ 0 ] ),
         *                             TOPIC_BUFFER_LENGTH,
         *                             pThingName,
         *                             thingNameLength,
         *                             DefenderJsonReportAccepted,
         *                             &( topicLength ) );
         */
        if( xStatus == true )
        {
            LogInfo( ( "Subscribing to defender topics..." ) );
            xStatus = prvSubscribeToDefenderTopics();

            if( xStatus != true )
            {
                LogError( ( "Failed to subscribe to defender topics." ) );
            }
        }

        /*********************** Collect device metrics. **********************/

        /* We then need to collect the metrics that will be sent to the AWS IoT
         * Device Defender service. This demo uses the functions declared in
         * in metrics_collector.h to collect network metrics. For this demo, the
         * implementation of these functions are in metrics_collector.c and
         * collects metrics using tcp_netstat utility for FreeRTOS+TCP. */
        if( xStatus == true )
        {
            LogInfo( ( "Collecting device metrics..." ) );
            xStatus = prvCollectDeviceMetrics();

            if( xStatus != true )
            {
                LogError( ( "Failed to collect device metrics." ) );
            }
        }

        /********************** Generate defender report. *********************/

        /* The data needs to be incorporated into a JSON formatted report,
         * which follows the format expected by the Device Defender service.
         * This format is documented here:
         * https://docs.aws.amazon.com/iot/latest/developerguide/detect-device-side-metrics.html
         */
        if( xStatus == true )
        {
            LogInfo( ( "Generating device defender report..." ) );
            xStatus = prvGenerateDeviceMetricsReport( &( ulReportLength ) );

            if( xStatus != true )
            {
                LogError( ( "Failed to generate device defender report." ) );
            }
        }

        /********************** Publish defender report. **********************/

        /* The report is then published to the Device Defender service. This report
         * is published to the MQTT topic for publishing JSON reports. As before,
         * we use the defender library macros to create the topic string, though
         * #Defender_GetTopic could be used if the Thing name is acquired at
         * run time */
        if( xStatus == true )
        {
            LogInfo( ( "Publishing device defender report..." ) );
            xStatus = prvPublishDeviceMetricsReport( ulReportLength );

            if( xStatus != true )
            {
                LogError( ( "Failed to publish device defender report." ) );
            }
        }

        /* Wait for the response to our report. Response will be handled by the
         * callback passed to xEstablishMqttSession() earlier.
         * The callback will verify that the MQTT messages received are from the
         * defender service's topic. Based on whether the response comes from
         * the accepted or rejected topics, it updates xReportStatus. */
        if( xStatus == true )
        {
            for( i = 0; i < DEFENDER_RESPONSE_WAIT_SECONDS; i++ )
            {
                ( void ) xProcessLoop( &xMqttContext, 1000 );

                /* xReportStatus is updated in the prvPublishCallback. */
                if( xReportStatus != ReportStatusNotReceived )
                {
                    break;
                }
            }
        }

        if( xReportStatus == ReportStatusNotReceived )
        {
            LogError( ( "Failed to receive response from AWS IoT Device Defender Service." ) );
            xStatus = false;
        }

        /**************************** Disconnect. *****************************/

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
        }

        /*********************** Retry in case of failure. ************************/

        /* Increment the demo run count. */
        uxDemoRunCount++;

        if( xExitStatus == EXIT_SUCCESS )
        {
            LogInfo( ( "Demo iteration %lu is successful.", uxDemoRunCount ) );
        }
        /* Attempt to retry a failed iteration of demo for up to #DEFENDER_MAX_DEMO_LOOP_COUNT times. */
        else if( uxDemoRunCount < DEFENDER_MAX_DEMO_LOOP_COUNT )
        {
            LogWarn( ( "Demo iteration %lu failed. Retrying...", uxDemoRunCount ) );
            vTaskDelay( DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_TICKS );
        }
        /* Failed all #DEFENDER_MAX_DEMO_LOOP_COUNT demo iterations. */
        else
        {
            LogError( ( "All %d demo iterations failed.", DEFENDER_MAX_DEMO_LOOP_COUNT ) );
            break;
        }
    } while( xExitStatus != EXIT_SUCCESS );

    /****************************** Finish. ******************************/

    if( xExitStatus == EXIT_SUCCESS )
    {
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
