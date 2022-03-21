/*
 * FreeRTOS V202112.00
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

/**
 * @file OtaOverMqttDemoExample.c
 * @brief Over The Air Update demo using coreMQTT Agent.
 *
 * The file demonstrates how to perform Over The Air update using OTA agent and coreMQTT Agent
 * library. It creates an OTA agent task which manages the OTA firmware update
 * for the device. The example also provides implementations to subscribe, publish,
 * and receive data from an MQTT broker. The implementation uses coreMQTT agent which manages
 * thread safety of the MQTT operations and allows OTA agent to share the same MQTT
 * broker connection with other tasks. OTA agent invokes the callback implementations to
 * publish job related control information, as well as receive chunks
 * of pre-signed firmware image from the MQTT broker.
 *
 * See https://freertos.org/mqtt/mqtt-agent-demo.html
 * See https://freertos.org/ota/ota-mqtt-agent-demo.html
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo config includes. */
#include "demo_config.h"

/* Library config includes. */
#include "ota_config.h"

/* MQTT library includes. */
#include "core_mqtt_agent.h"

/* MQTT Agent ports. */
#include "freertos_agent_message.h"
#include "freertos_command_pool.h"

/* Subscription manager header include. */
#include "subscription_manager.h"

/* Exponential backoff retry include. */
#include "backoff_algorithm.h"

/* mbedTLS transport interface header.*/
#include "using_mbedtls.h"

/* OTA Library include. */
#include "ota.h"

/* OTA Library Interface include. */
#include "ota_os_freertos.h"
#include "ota_mqtt_interface.h"
#include "ota_platform_interface.h"

/* Include firmware version struct definition. */
#include "ota_appversion32.h"

/* Include platform abstraction header. */
#include "ota_pal.h"

/*------------- Demo configurations -------------------------*/

/**
 * @brief The maximum size of the file paths used in the demo.
 */
#define otaexampleMAX_FILE_PATH_SIZE      ( 260 )

/**
 * @brief The maximum size of the stream name required for downloading update file
 * from streaming service.
 */
#define otaexampleMAX_STREAM_NAME_SIZE    ( 128 )

/**
 * @brief The delay used in the OTA demo task to periodically output the OTA
 * statistics like number of packets received, dropped, processed and queued per connection.
 */
#define otaexampleTASK_DELAY_MS           ( 1000U )

/**
 * @brief The maximum time for which OTA demo waits for an MQTT operation to be complete.
 * This involves receiving an acknowledgment for broker for SUBSCRIBE, UNSUBSCRIBE and non
 * QOS0 publishes.
 */
#define otaexampleMQTT_TIMEOUT_MS         ( 5000U )

/**
 * @brief The common prefix for all OTA topics.
 *
 * Thing name is substituted with a wildcard symbol `+`. OTA agent
 * registers with MQTT broker with the thing name in the topic. This topic
 * filter is used to match incoming packet received and route them to OTA.
 * Thing name is not needed for this matching.
 */
#define OTA_TOPIC_PREFIX                                 "$aws/things/+/"

/**
 * @brief Wildcard topic filter for job notification.
 * The filter is used to match the constructed job notify topic filter from OTA agent and register
 * appropriate callback for it.
 */
#define OTA_JOB_NOTIFY_TOPIC_FILTER                      OTA_TOPIC_PREFIX "jobs/notify-next"

/**
 * @brief Length of job notification topic filter.
 */
#define OTA_JOB_NOTIFY_TOPIC_FILTER_LENGTH               ( ( uint16_t ) ( sizeof( OTA_JOB_NOTIFY_TOPIC_FILTER ) - 1 ) )

/**
 * @brief Wildcard topic filter for matching job response messages.
 * This topic filter is used to match the responses from OTA service for OTA agent job requests. THe
 * topic filter is a reserved topic which is not subscribed with MQTT broker.
 *
 */
#define OTA_JOB_ACCEPTED_RESPONSE_TOPIC_FILTER           OTA_TOPIC_PREFIX "jobs/$next/get/accepted"

/**
 * @brief Length of job accepted response topic filter.
 */
#define OTA_JOB_ACCEPTED_RESPONSE_TOPIC_FILTER_LENGTH    ( ( uint16_t ) ( sizeof( OTA_JOB_ACCEPTED_RESPONSE_TOPIC_FILTER ) - 1 ) )


/**
 * @brief Wildcard topic filter for matching OTA data packets.
 *  The filter is used to match the constructed data stream topic filter from OTA agent and register
 * appropriate callback for it.
 */
#define OTA_DATA_STREAM_TOPIC_FILTER           OTA_TOPIC_PREFIX  "streams/#"

/**
 * @brief Length of data stream topic filter.
 */
#define OTA_DATA_STREAM_TOPIC_FILTER_LENGTH    ( ( uint16_t ) ( sizeof( OTA_DATA_STREAM_TOPIC_FILTER ) - 1 ) )


/**
 * @brief Starting index of client identifier within OTA topic.
 */
#define OTA_TOPIC_CLIENT_IDENTIFIER_START_IDX    ( 12U )

 /**
  * @brief Default topic filter for OTA.
  * This is used to route all the packets for OTA reserved topics which OTA agent has not subscribed for.
  */
#define OTA_DEFAULT_TOPIC_FILTER              OTA_TOPIC_PREFIX "jobs/#"

  /**
   * @brief Length of default topic filter.
   */
#define OTA_DEFAULT_TOPIC_FILTER_LENGTH       ( ( uint16_t ) ( sizeof( OTA_DEFAULT_TOPIC_FILTER ) - 1 ) )

/**
 * @brief Used to clear bits in a task's notification value.
 */
#define otaexampleMAX_UINT32                     ( 0xffffffff )

 /**
  * @brief Dimensions the buffer used to serialize and deserialize MQTT packets.
  * @note Specified in bytes.  Must be large enough to hold the maximum
  * anticipated MQTT payload.
  */
#ifndef MQTT_AGENT_NETWORK_BUFFER_SIZE
#define MQTT_AGENT_NETWORK_BUFFER_SIZE    ( 10240 )
#endif

  /**
   * @brief The length of the queue used to hold commands for the agent.
   */
#ifndef MQTT_AGENT_COMMAND_QUEUE_LENGTH
#define MQTT_AGENT_COMMAND_QUEUE_LENGTH    ( 10 )
#endif

/**
 * @brief The maximum amount of time in milliseconds to wait for the commands
 * to be posted to the MQTT agent should the MQTT agent's command queue be full.
 * Tasks wait in the Blocked state, so don't use any CPU time.
 */
#define MQTT_AGENT_SEND_BLOCK_TIME_MS                ( 200U )

 /**
  * @brief This demo uses task notifications to signal tasks from MQTT callback
  * functions.  mqttexampleMS_TO_WAIT_FOR_NOTIFICATION defines the time, in ticks,
  * to wait for such a callback.
  */
#define MQTT_AGENT_MS_TO_WAIT_FOR_NOTIFICATION       ( 5000U )

/**
 * @brief The maximum number of retries for network operation with server.
 */
#define RETRY_MAX_ATTEMPTS                           ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying failed operation
 *  with server.
 */
#define RETRY_MAX_BACKOFF_DELAY_MS                   ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for network operation retry
 * attempts.
 */
#define RETRY_BACKOFF_BASE_MS                        ( 500U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 *  between two Control Packets.
 *
 *  It is the responsibility of the Client to ensure that the interval between
 *  Control Packets being sent does not exceed the this Keep Alive value. In the
 *  absence of sending any other Control Packets, the Client MUST send a
 *  PINGREQ Packet.
 */
#define otaexampleKEEP_ALIVE_INTERVAL_SECONDS       ( 60U )

/**
 * @brief Socket send and receive timeouts to use.  Specified in milliseconds.
 */
#define otaexampleTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 750 )

 /**
  * @brief Timeout for receiving CONNACK after sending an MQTT CONNECT packet.
  * Defined in milliseconds.
  */
#define otaexampleCONNACK_RECV_TIMEOUT_MS    ( 1000U )

/**
 * @brief Stack size required for MQTT agent task.
 * MQTT agent task takes care of TLS connection and reconnection, keeping task stack size
 * to high enough required for TLS connection.
 */
#define MQTT_AGENT_TASK_STACK_SIZE                   ( 6000U )

/**
 * @brief Priority required for OTA statistics task.
 */
#define MQTT_AGENT_TASK_PRIORITY                     ( tskIDLE_PRIORITY )

/**
 * @brief Stack size required for OTA agent task.
 */
#define OTA_AGENT_TASK_STACK_SIZE                    ( 5000U )

/**
 * @brief Priority required for OTA agent task.
 */
#define OTA_AGENT_TASK_PRIORITY                      ( tskIDLE_PRIORITY )

/**
 * @brief Used to convert times to/from ticks and milliseconds.
 */
#define otaexampleMILLISECONDS_PER_SECOND           ( 1000U )
#define otaexampleMILLISECONDS_PER_TICK             ( otaexampleMILLISECONDS_PER_SECOND / configTICK_RATE_HZ )

 /**
  * @brief The timeout for waiting for the agent to get suspended after closing the
  * connection.
  *
  * Timeout value should be large enough for OTA agent to finish any pending MQTT operations
  * and suspend itself.
  *
  */
#define OTA_SUSPEND_TIMEOUT_MS                   ( 10000U )

/*---------------------------------------------------------*/

/**
 * @brief Structure used to store the topic filter to ota callback mappings.
 */
typedef struct OtaTopicFilterCallback
{
    const char * pTopicFilter;
    uint16_t topicFilterLength;
    IncomingPubCallback_t callback;
} OtaTopicFilterCallback_t;

/**
 * @brief Defines the structure to use as the command callback context in this
 * demo.
 */
struct MQTTAgentCommandContext
{
    MQTTStatus_t xReturnStatus;
    TaskHandle_t xTaskToNotify;
    void * pArgs;
};

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


/*---------------------------------------------------------*/

/**
 * @brief Global entry time into the application to use as a reference timestamp
 * in the #prvGetTimeMs function. #prvGetTimeMs will always return the difference
 * between the current time and the global entry time. This will reduce the chances
 * of overflow for the 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t ulGlobalEntryTimeMs;

/**
 * @brief The buffer is used to hold the serialized packets for transmission to and from
 * the transport interface.
 */
static uint8_t xNetworkBuffer[ MQTT_AGENT_NETWORK_BUFFER_SIZE ];

/**
 * @brief FreeRTOS blocking queue to be used as MQTT Agent context.
 */
static MQTTAgentMessageContext_t xCommandQueue;

/**
 * @brief The network context used by the MQTT library transport interface.
 * See https://www.freertos.org/network-interface.html
 */
static NetworkContext_t xNetworkContextMqtt;

/**
 * @brief The parameters for the network context using a TLS channel.
 */
static TlsTransportParams_t xTlsTransportParams;

/**
 * @brief The global array of subscription elements.
 *
 * @note No thread safety is required to this array, since the updates the array
 * elements are done only from one task at a time. The subscription manager
 * implementation expects that the array of the subscription elements used for
 * storing subscriptions to be initialized to 0. As this is a global array, it
 * will be initialized to 0 by default.
 */
static SubscriptionElement_t xGlobalSubscriptionList[ SUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS ];

/**
 * @brief Buffer used to store the firmware image file path.
 * Buffer is passed to the OTA agent during initialization.
 */
static uint8_t updateFilePath[ otaexampleMAX_FILE_PATH_SIZE ];

/**
 * @brief Buffer used to store the code signing certificate file path.
 * Buffer is passed to the OTA agent during initialization.
 */
static uint8_t certFilePath[ otaexampleMAX_FILE_PATH_SIZE ];

/**
 * @brief Buffer used to store the name of the data stream.
 * Buffer is passed to the OTA agent during initialization.
 */
static uint8_t streamName[ otaexampleMAX_STREAM_NAME_SIZE ];

/**
 * @brief Buffer used decode the CBOR message from the MQTT payload.
 * Buffer is passed to the OTA agent during initialization.
 */
static uint8_t decodeMem[ ( 1U << otaconfigLOG2_FILE_BLOCK_SIZE ) ];

/**
 * @brief Application buffer used to store the bitmap for requesting firmware image
 * chunks from MQTT broker. Buffer is passed to the OTA agent during initialization.
 */
static uint8_t bitmap[ OTA_MAX_BLOCK_BITMAP_SIZE ];

/**
 * @brief A statically allocated array of event buffers used by the OTA agent.
 * Maximum number of buffers are determined by how many chunks are requested
 * by OTA agent at a time along with an extra buffer to handle control message.
 * The size of each buffer is determined by the maximum size of firmware image
 * chunk, and other metadata send along with the chunk.
 */
static OtaEventData_t eventBuffer[ otaconfigMAX_NUM_OTA_DATA_BUFFERS ] = { 0 };

/*
 * @brief Mutex used to manage thread safe access of OTA event buffers.
 */
static SemaphoreHandle_t xBufferSemaphore;

/**
 * @brief Static handle used for MQTT agent context.
 */
static MQTTAgentContext_t xGlobalMqttAgentContext;

/*---------------------------------------------------------*/

/**
 * @brief Task for MQTT agent.
 * Task runs MQTT agent command loop, which returns only when the user disconnects
 * MQTT, terminates agent, or the mqtt connection is broken. If the mqtt connection is broken, the task
 * suspends OTA agent reconnects to the broker and then resumes OTA agent.
 *
 * @param[in] pParam Can be used to pass down functionality to the agent task
 */
static void prvMQTTAgentTask(void* pParam);

/**
 * @brief Function used by OTA agent to publish control messages to the MQTT broker.
 *
 * The implementation uses MQTT agent to queue a publish request. It then waits
 * for the request complete notification from the agent. The notification along with result of the
 * operation is sent back to the caller task using xTaksNotify API. For publishes involving QOS 1 and
 * QOS2 the operation is complete once an acknowledgment (PUBACK) is received. OTA agent uses this function
 * to fetch new job, provide status update and send other control related messages to the MQTT broker.
 *
 * @param[in] pacTopic Topic to publish the control packet to.
 * @param[in] topicLen Length of the topic string.
 * @param[in] pMsg Message to publish.
 * @param[in] msgSize Size of the message to publish.
 * @param[in] qos Qos for the publish.
 * @return OtaMqttSuccess if successful. Appropriate error code otherwise.
 */
static OtaMqttStatus_t prvMQTTPublish( const char * const pacTopic,
                                       uint16_t topicLen,
                                       const char * pMsg,
                                       uint32_t msgSize,
                                       uint8_t qos );

/**
 * @brief Function used by OTA agent to subscribe for a control or data packet from the MQTT broker.
 *
 * The implementation queues a SUBSCRIBE request for the topic filter with the MQTT agent. It then waits for
 * a notification of the request completion. Notification will be sent back to caller task,
 * using xTaskNotify APIs. MQTT agent also stores a callback provided by this function with
 * the associated topic filter. The callback will be used to
 * route any data received on the matching topic to the OTA agent. OTA agent uses this function
 * to subscribe to all topic filters necessary for receiving job related control messages as
 * well as firmware image chunks from MQTT broker.
 *
 * @param[in] pTopicFilter The topic filter used to subscribe for packets.
 * @param[in] topicFilterLength Length of the topic filter string.
 * @param[in] ucQoS Intended qos value for the messages received on this topic.
 * @return OtaMqttSuccess if successful. Appropriate error code otherwise.
 */
static OtaMqttStatus_t prvMQTTSubscribe( const char * pTopicFilter,
                                         uint16_t topicFilterLength,
                                         uint8_t ucQoS );

/**
 * @brief Function is used by OTA agent to unsubscribe a topicfilter from MQTT broker.
 *
 * The implementation queues an UNSUBSCRIBE request for the topic filter with the MQTT agent. It then waits
 * for a successful completion of the request from the agent. Notification along with results of
 * operation is sent using xTaskNotify API to the caller task. MQTT agent also removes the topic filter
 * subscription from its memory so any future
 * packets on this topic will not be routed to the OTA agent.
 *
 * @param[in] pTopicFilter Topic filter to be unsubscribed.
 * @param[in] topicFilterLength Length of the topic filter.
 * @param[in] ucQos Qos value for the topic.
 * @return OtaMqttSuccess if successful. Appropriate error code otherwise.
 *
 */
static OtaMqttStatus_t prvMQTTUnsubscribe( const char * pTopicFilter,
                                           uint16_t topicFilterLength,
                                           uint8_t ucQoS );

/**
 * @brief Fetch an unused OTA event buffer from the pool.
 *
 * Demo uses a simple statically allocated array of fixed size event buffers. The
 * number of event buffers is configured by the param otaconfigMAX_NUM_OTA_DATA_BUFFERS
 * within ota_config.h. This function is used to fetch a free buffer from the pool for processing
 * by the OTA agent task. It uses a mutex for thread safe access to the pool.
 *
 * @return A pointer to an unusued buffer. NULL if there are no buffers available.
 */
static OtaEventData_t * prvOTAEventBufferGet( void );

/**
 * @brief Free an event buffer back to pool
 *
 * OTA demo uses a statically allocated array of fixed size event buffers . The
 * number of event buffers is configured by the param otaconfigMAX_NUM_OTA_DATA_BUFFERS
 * within ota_config.h. The function is used by the OTA application callback to free a buffer,
 * after OTA agent has completed processing with the event. The access to the pool is made thread safe
 * using a mutex.
 *
 * @param[in] pxBuffer Pointer to the buffer to be freed.
 */
static void prvOTAEventBufferFree( OtaEventData_t * const pxBuffer );

/**
 * @brief The function which runs the OTA agent task.
 *
 * The function runs the OTA Agent Event processing loop, which waits for
 * any events for OTA agent and process them. The loop never returns until the OTA agent
 * is shutdown. The tasks exits gracefully by freeing up all resources in the event of an
 *  OTA agent shutdown.
 *
 * @param[in] pvParam Any parameters to be passed to OTA agent task.
 */
static void prvOTAAgentTask( void * pvParam );


/**
 * @brief The function which runs the OTA demo task.
 *
 * The demo task initializes the OTA agent an loops until OTA agent is shutdown.
 * It reports OTA update statistics (which includes number of blocks received, processed and dropped),
 * at regular intervals.
 * 
 * @param[in] pvParam Any parameters to be passed to OTA Demo task.
 */
static void vOtaDemoTask( void* pvParam );

/**
 * @brief The function which implements the flow for OTA demo.
 *
 * @return pdPASS if success or pdFAIL.
 */
static BaseType_t prvRunOTADemo(void);

/**
 * @brief Callback registered with the OTA library that notifies the OTA agent
 * of an incoming PUBLISH containing a job document.
 *
 * @param[in] pContext MQTT context which stores the connection.
 * @param[in] pPublishInfo MQTT packet information which stores details of the
 * job document.
 */
static void prvMqttJobCallback( void * pContext,
                                MQTTPublishInfo_t * pPublish );


/**
 * @brief Callback that notifies the OTA library when a data block is received.
 *
 * @param[in] pContext MQTT context which stores the connection.
 * @param[in] pPublishInfo MQTT packet that stores the information of the file block.
 */
static void prvMqttDataCallback( void * pContext,
                                 MQTTPublishInfo_t * pPublish );

/**
 * @brief Default callback used to receive unsolicited messages for OTA.
 *
 * The callback is not subscribed with MQTT broker, but only with local subscription manager.
 * A wildcard OTA job topic is used for subscription so that all unsolicited messages related to OTA is
 * forwarded to this callback for filteration. Right now the callback is used to filter responses to job requests
 * from the OTA service.
 *
 * @param[in] pvIncomingPublishCallbackContext MQTT context which stores the connection.
 * @param[in] pPublishInfo MQTT packet that stores the information of the file block.
 */
static void prvMqttDefaultCallback( void * pvIncomingPublishCallbackContext,
                                    MQTTPublishInfo_t * pxPublishInfo );


/**
 * @brief Attempt to connect to the MQTT broker.
 *
 */
static void prvConnectToMQTTBroker(void);

/**
 * @brief Retry logic to establish a connection to the MQTT broker.
 *
 * If the connection fails, keep retrying with exponentially increasing
 * timeout value, until max retries, max timeout or successful connect.
 *
 * @param[in] pNetworkContext Network context to connect on.
 * @return int pdFALSE if connection failed after retries.
 */
static BaseType_t prvSocketConnect(NetworkContext_t* pNetworkContext);

/**
 * @brief Disconnects from the MQTT broker.
 * Initiates an MQTT disconnect and then teardown underlying TCP connection.
 *
 */
static void prvDisconnectFromMQTTBroker(void);

/**
 * @brief Initializes an MQTT context, including transport interface and
 * network buffer.
 *
 * @return `MQTTSuccess` if the initialization succeeds, else `MQTTBadParameter`.
 */
static MQTTStatus_t prvMqttInit(void);

/**
 * @brief Sends an MQTT Connect packet over the already connected TCP socket.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 * @param[in] xCleanSession If a clean session should be established.
 *
 * @return `MQTTSuccess` if connection succeeds, else appropriate error code
 * from MQTT_Connect.
 */
static MQTTStatus_t prvMQTTConnect( bool xCleanSession );

/**
 * @brief Register OTA callbacks with the subscription manager.
 *
 * @param[in] pTopicFilter The topic filter for which a  callback needs to be registered for.
 * @param[in] topicFilterLength length of the topic filter.
 *
 */
static void prvRegisterOTACallback(const char* pTopicFilter,
    uint16_t topicFilterLength);

/**
 * @brief Suspend OTA demo.
 *
 * @return   pPASS or pdFAIL.
 */
static BaseType_t prvSuspendOTA(void);

/**
 * @brief Resume OTA demo.
 *
 * @return   pPASS or pdFAIL.
 */
static BaseType_t prvResumeOTA(void);

/**
 * @brief Set OTA interfaces.
 *
 * @param[in]  pOtaInterfaces pointer to OTA interface structure.
 *
 * @return   None.
 */
static void setOtaInterfaces(OtaInterfaces_t* pOtaInterfaces);

/**
 * @brief Structure containing all application allocated buffers used by the OTA agent.
 * Structure is passed to the OTA agent during initialization.
 */
static OtaAppBuffer_t otaBuffer =
{
    .pUpdateFilePath    = updateFilePath,
    .updateFilePathsize = otaexampleMAX_FILE_PATH_SIZE,
    .pCertFilePath      = certFilePath,
    .certFilePathSize   = otaexampleMAX_FILE_PATH_SIZE,
    .pStreamName        = streamName,
    .streamNameSize     = otaexampleMAX_STREAM_NAME_SIZE,
    .pDecodeMemory      = decodeMem,
    .decodeMemorySize   = ( 1U << otaconfigLOG2_FILE_BLOCK_SIZE ),
    .pFileBitmap        = bitmap,
    .fileBitmapSize     = OTA_MAX_BLOCK_BITMAP_SIZE
};

/**
 * @brief Structure used for encoding firmware version.
 */
const AppVersion32_t appFirmwareVersion =
{
    .u.x.major = APP_VERSION_MAJOR,
    .u.x.minor = APP_VERSION_MINOR,
    .u.x.build = APP_VERSION_BUILD,
};

/**
 * @brief Registry for all  mqtt topic filters to their corresponding callbacks for OTA.
 */
static OtaTopicFilterCallback_t otaTopicFilterCallbacks[] =
{
    {
        .pTopicFilter = OTA_JOB_NOTIFY_TOPIC_FILTER,
        .topicFilterLength = OTA_JOB_NOTIFY_TOPIC_FILTER_LENGTH,
        .callback = prvMqttJobCallback
    },
    {
        .pTopicFilter = OTA_DATA_STREAM_TOPIC_FILTER,
        .topicFilterLength = OTA_DATA_STREAM_TOPIC_FILTER_LENGTH,
        .callback = prvMqttDataCallback
    },
    {
        .pTopicFilter = OTA_DEFAULT_TOPIC_FILTER,
        .topicFilterLength = OTA_DEFAULT_TOPIC_FILTER_LENGTH,
        .callback = prvMqttDefaultCallback
    }
};

/*-----------------------------------------------------------*/

static void prvOTAEventBufferFree( OtaEventData_t * const pxBuffer )
{
    if( xSemaphoreTake( xBufferSemaphore, portMAX_DELAY ) == pdTRUE )
    {
        pxBuffer->bufferUsed = false;
        ( void ) xSemaphoreGive( xBufferSemaphore );
    }
}

/*-----------------------------------------------------------*/

static OtaEventData_t * prvOTAEventBufferGet( void )
{
    uint32_t ulIndex = 0;
    OtaEventData_t * pFreeBuffer = NULL;

    if( xSemaphoreTake( xBufferSemaphore, portMAX_DELAY ) == pdTRUE )
    {
        for( ulIndex = 0; ulIndex < otaconfigMAX_NUM_OTA_DATA_BUFFERS; ulIndex++ )
        {
            if( eventBuffer[ ulIndex ].bufferUsed == false )
            {
                eventBuffer[ ulIndex ].bufferUsed = true;
                pFreeBuffer = &eventBuffer[ ulIndex ];
                break;
            }
        }

        ( void ) xSemaphoreGive( xBufferSemaphore );
    }

    return pFreeBuffer;
}

/*-----------------------------------------------------------*/

/**
 * @brief The OTA agent has completed the update job or it is in
 * self test mode. If it was accepted, we want to activate the new image.
 * This typically means we should reset the device to run the new firmware.
 * If now is not a good time to reset the device, it may be activated later
 * by your user code. If the update was rejected, just return without doing
 * anything and we will wait for another job. If it reported that we should
 * start test mode, normally we would perform some kind of system checks to
 * make sure our new firmware does the basic things we think it should do
 * but we will just go ahead and set the image as accepted for demo purposes.
 * The accept function varies depending on your platform. Refer to the OTA
 * PAL implementation for your platform in ota_pal.c to see what it
 * does for you.
 *
 * @param[in] event Specify if this demo is running with the AWS IoT
 * MQTT server. Set this to `false` if using another MQTT server.
 * @param[in] pData Data associated with the event.
 * @return None.
 */
static void otaAppCallback( OtaJobEvent_t event,
                            const void * pData )
{
    OtaErr_t err = OtaErrUninitialized;

    switch( event )
    {
        case OtaJobEventActivate:
            LogInfo( ( "Received OtaJobEventActivate callback from OTA Agent." ) );

            /**
             * Activate the new firmware image immediately. Applications can choose to postpone
             * the activation to a later stage if needed.
             */
            err = OTA_ActivateNewImage();

            /**
             * Activation of the new image failed. This indicates an error that requires a follow
             * up through manual activation by resetting the device. The demo reports the error
             * and shuts down the OTA agent.
             */
            LogError( ( "New image activation failed." ) );

            /* Shutdown OTA Agent, if it is required that the unsubscribe operations are not
             * performed while shutting down please set the second parameter to 0 instead of 1. */
            OTA_Shutdown( 0, 1 );


            break;

        case OtaJobEventFail:

            /**
             * No user action is needed here. OTA agent handles the job failure event.
             */
            LogInfo( ( "Received an OtaJobEventFail notification from OTA Agent." ) );

            break;

        case OtaJobEventStartTest:

            /* This demo just accepts the image since it was a good OTA update and networking
             * and services are all working (or we would not have made it this far). If this
             * were some custom device that wants to test other things before validating new
             * image, this would be the place to kick off those tests before calling
             * OTA_SetImageState() with the final result of either accepted or rejected. */

            LogInfo( ( "Received OtaJobEventStartTest callback from OTA Agent." ) );

            err = OTA_SetImageState( OtaImageStateAccepted );

            if( err == OtaErrNone )
            {
                LogInfo( ( "New image validation succeeded in self test mode." ) );
            }
            else
            {
                LogError( ( "Failed to set image state as accepted with error %d.", err ) );
            }

            break;

        case OtaJobEventProcessed:

            LogDebug( ( "OTA Event processing completed. Freeing the event buffer to pool." ) );
            configASSERT( pData != NULL );
            prvOTAEventBufferFree( ( OtaEventData_t * ) pData );

            break;

        case OtaJobEventSelfTestFailed:
            LogDebug( ( "Received OtaJobEventSelfTestFailed callback from OTA Agent." ) );

            /* Requires manual activation of previous image as self-test for
             * new image downloaded failed.*/
            LogError( ( "OTA Self-test failed for new image. shutting down OTA Agent." ) );

            /* Shutdown OTA Agent, if it is required that the unsubscribe operations are not
             * performed while shutting down please set the second parameter to 0 instead of 1. */
            OTA_Shutdown( 0, 1 );

            break;

        default:
            LogWarn( ( "Received an unhandled callback event from OTA Agent, event = %d", event ) );

            break;
    }
}

static void prvMqttJobCallback( void * pvIncomingPublishCallbackContext,
                                MQTTPublishInfo_t * pxPublishInfo )
{
    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };

    configASSERT( pxPublishInfo != NULL );
    ( void ) pvIncomingPublishCallbackContext;

    LogInfo( ( "Received job message callback, size %ld.\n\n", pxPublishInfo->payloadLength ) );

    pData = prvOTAEventBufferGet();

    if( pData != NULL )
    {
        memcpy( pData->data, pxPublishInfo->pPayload, pxPublishInfo->payloadLength );
        pData->dataLength = pxPublishInfo->payloadLength;
        eventMsg.eventId = OtaAgentEventReceivedJobDocument;
        eventMsg.pEventData = pData;

        /* Send job document received event. */
        OTA_SignalEvent( &eventMsg );
    }
    else
    {
        LogError( ( "Error: No OTA data buffers available.\r\n" ) );
    }
}

/*-----------------------------------------------------------*/
static void prvMqttDefaultCallback( void * pvIncomingPublishCallbackContext,
                                    MQTTPublishInfo_t * pxPublishInfo )
{
    bool isMatch = false;

    ( void ) MQTT_MatchTopic( pxPublishInfo->pTopicName,
                              pxPublishInfo->topicNameLength,
                              OTA_JOB_ACCEPTED_RESPONSE_TOPIC_FILTER,
                              OTA_JOB_ACCEPTED_RESPONSE_TOPIC_FILTER_LENGTH,
                              &isMatch );

    if( isMatch == true )
    {
        prvMqttJobCallback( pvIncomingPublishCallbackContext, pxPublishInfo );
    }
}

/*-----------------------------------------------------------*/
static void prvMqttDataCallback( void * pvIncomingPublishCallbackContext,
                                 MQTTPublishInfo_t * pxPublishInfo )
{
    OtaEventData_t * pxData;
    OtaEventMsg_t eventMsg = { 0 };

    configASSERT( pxPublishInfo != NULL );
    ( void ) pvIncomingPublishCallbackContext;

    LogInfo( ( "Received data message callback, size %zu.\n\n", pxPublishInfo->payloadLength ) );

    pxData = prvOTAEventBufferGet();

    if(pxData != NULL )
    {
        memcpy(pxData->data, pxPublishInfo->pPayload, pxPublishInfo->payloadLength );
        pxData->dataLength = pxPublishInfo->payloadLength;
        eventMsg.eventId = OtaAgentEventReceivedFileBlock;
        eventMsg.pEventData = pxData;

        /* Send job document received event. */
        OTA_SignalEvent( &eventMsg );
    }
    else
    {
        LogError( ( "Error: No OTA data buffers available.\r\n" ) );
    }
}

/*-----------------------------------------------------------*/

static void prvCommandCallback( MQTTAgentCommandContext_t * pxCommandContext,
                                MQTTAgentReturnInfo_t * pxReturnInfo )
{
    pxCommandContext->xReturnStatus = pxReturnInfo->returnCode;

    if( pxCommandContext->xTaskToNotify != NULL )
    {
        xTaskNotify( pxCommandContext->xTaskToNotify, ( uint32_t ) ( pxReturnInfo->returnCode ), eSetValueWithOverwrite );
    }
}

static void prvMQTTSubscribeCompleteCallback( MQTTAgentCommandContext_t* pxCommandContext,
    MQTTAgentReturnInfo_t* pxReturnInfo )
{
    MQTTAgentSubscribeArgs_t* pSubsribeArgs;

    if (pxReturnInfo->returnCode == MQTTSuccess)
    {
        pSubsribeArgs = (MQTTAgentSubscribeArgs_t*)(pxCommandContext->pArgs);
        prvRegisterOTACallback(pSubsribeArgs->pSubscribeInfo->pTopicFilter, pSubsribeArgs->pSubscribeInfo->topicFilterLength);
    }

    /* Store the result in the application defined context so the task that
     * initiated the publish can check the operation's status. */
    pxCommandContext->xReturnStatus = pxReturnInfo->returnCode;

    if (pxCommandContext->xTaskToNotify != NULL)
    {
        /* Send the context's ulNotificationValue as the notification value so
         * the receiving task can check the value it set in the context matches
         * the value it receives in the notification. */
        xTaskNotify(pxCommandContext->xTaskToNotify, (uint32_t)(pxReturnInfo->returnCode), eSetValueWithOverwrite);
    }
}

/*-----------------------------------------------------------*/

static void prvMQTTUnsubscribeCompleteCallback( MQTTAgentCommandContext_t* pxCommandContext,
    MQTTAgentReturnInfo_t* pxReturnInfo )
{

    /* Store the result in the application defined context so the task that
     * initiated the publish can check the operation's status. */
    pxCommandContext->xReturnStatus = pxReturnInfo->returnCode;

    if (pxCommandContext->xTaskToNotify != NULL)
    {
        /* Send the context's ulNotificationValue as the notification value so
         * the receiving task can check the value it set in the context matches
         * the value it receives in the notification. */
        xTaskNotify(pxCommandContext->xTaskToNotify, (uint32_t)(pxReturnInfo->returnCode), eSetValueWithOverwrite);
    }
}

/*-----------------------------------------------------------*/

static uint32_t prvGetTimeMs( void )
{
    TickType_t xTickCount = 0;
    uint32_t ulTimeMs = 0UL;

    /* Get the current tick count. */
    xTickCount = xTaskGetTickCount();

    /* Convert the ticks to milliseconds. */
    ulTimeMs = ( uint32_t ) xTickCount * otaexampleMILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = ( uint32_t ) ( ulTimeMs - ulGlobalEntryTimeMs );

    return ulTimeMs;
}

/*-----------------------------------------------------------*/

static void prvIncomingPublishCallback( MQTTAgentContext_t * pMqttAgentContext,
                                        uint16_t packetId,
                                        MQTTPublishInfo_t * pxPublishInfo )
{
    bool xPublishHandled = false;
    char cOriginalChar, * pcLocation;

    ( void ) packetId;

    /* Fan out the incoming publishes to the callbacks registered using
     * subscription manager. */
    xPublishHandled = handleIncomingPublishes( ( SubscriptionElement_t * ) pMqttAgentContext->pIncomingCallbackContext,
                                               pxPublishInfo );

    /* If there are no callbacks to handle the incoming publishes,
     * handle it as an unsolicited publish. */
    if( xPublishHandled != true )
    {
        /* Ensure the topic string is terminated for printing.  This will over-
         * write the message ID, which is restored afterwards. */
        pcLocation = ( char * ) &( pxPublishInfo->pTopicName[ pxPublishInfo->topicNameLength ] );
        cOriginalChar = *pcLocation;
        *pcLocation = 0x00;
        LogWarn( ( "Received an unsolicited publish from topic %s", pxPublishInfo->pTopicName ) );
        *pcLocation = cOriginalChar;
    }
}

/*-----------------------------------------------------------*/



static void prvSubscriptionCommandCallback( void * pxCommandContext,
                                            MQTTAgentReturnInfo_t * pxReturnInfo )
{
    size_t xIndex = 0;
    MQTTAgentSubscribeArgs_t * pxSubscribeArgs = ( MQTTAgentSubscribeArgs_t * ) pxCommandContext;

    /* If the return code is success, no further action is required as all the topic filters
     * are already part of the subscription list. */
    if( pxReturnInfo->returnCode != MQTTSuccess )
    {
        /* Check through each of the suback codes and determine if there are any failures. */
        for( xIndex = 0; xIndex < pxSubscribeArgs->numSubscriptions; xIndex++ )
        {
            /* This demo doesn't attempt to resubscribe in the event that a SUBACK failed. */
            if( pxReturnInfo->pSubackCodes[xIndex] == MQTTSubAckFailure )
            {
                LogError( ( "Failed to resubscribe to topic %.*s.",
                            pxSubscribeArgs->pSubscribeInfo[xIndex].topicFilterLength,
                            pxSubscribeArgs->pSubscribeInfo[xIndex].pTopicFilter ) );
                /* Remove subscription callback for unsubscribe. */
                removeSubscription( xGlobalSubscriptionList,
                                    pxSubscribeArgs->pSubscribeInfo[xIndex].pTopicFilter,
                                    pxSubscribeArgs->pSubscribeInfo[xIndex].topicFilterLength );
            }
        }

        /* Hit an assert as some of the tasks won't be able to proceed correctly without
         * the subscriptions. This logic will be updated with exponential backoff and retry.  */
        configASSERT( pdTRUE );
    }
}



/*-----------------------------------------------------------*/

static MQTTStatus_t prvHandleResubscribe( void )
{
    MQTTStatus_t xResult = MQTTBadParameter;
    uint32_t ulIndex = 0U;
    uint16_t usNumSubscriptions = 0U;

    /* These variables need to stay in scope until command completes. */
    static MQTTAgentSubscribeArgs_t xSubArgs = { 0 };
    static MQTTSubscribeInfo_t xSubInfo[ SUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS ] = { 0 };
    static MQTTAgentCommandInfo_t xCommandParams = { 0 };

    /* Loop through each subscription in the subscription list and add a subscribe
     * command to the command queue. */
    for( ulIndex = 0U; ulIndex < SUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS; ulIndex++ )
    {
        /* Check if there is a subscription in the subscription list. This demo
         * doesn't check for duplicate subscriptions. */
        if( xGlobalSubscriptionList[ ulIndex ].usFilterStringLength != 0 )
        {
            xSubInfo[ usNumSubscriptions ].pTopicFilter = xGlobalSubscriptionList[ ulIndex ].pcSubscriptionFilterString;
            xSubInfo[ usNumSubscriptions ].topicFilterLength = xGlobalSubscriptionList[ ulIndex ].usFilterStringLength;

            /* QoS1 is used for all the subscriptions in this demo. */
            xSubInfo[ usNumSubscriptions ].qos = MQTTQoS1;

            LogInfo( ( "Resubscribe to the topic %.*s will be attempted.",
                       xSubInfo[ usNumSubscriptions ].topicFilterLength,
                       xSubInfo[ usNumSubscriptions ].pTopicFilter ) );

            usNumSubscriptions++;
        }
    }

    if( usNumSubscriptions > 0U )
    {
        xSubArgs.pSubscribeInfo = xSubInfo;
        xSubArgs.numSubscriptions = usNumSubscriptions;

        /* The block time can be 0 as the command loop is not running at this point. */
        xCommandParams.blockTimeMs = 0U;
        xCommandParams.cmdCompleteCallback = prvSubscriptionCommandCallback;
        xCommandParams.pCmdCompleteCallbackContext = ( void * ) &xSubArgs;

        /* Enqueue subscribe to the command queue. These commands will be processed only
         * when command loop starts. */
        xResult = MQTTAgent_Subscribe( &xGlobalMqttAgentContext, &xSubArgs, &xCommandParams );
    }
    else
    {
        /* Mark the resubscribe as success if there is nothing to be subscribed. */
        xResult = MQTTSuccess;
    }

    if( xResult != MQTTSuccess )
    {
        LogError( ( "Failed to enqueue the MQTT subscribe command. xResult=%s.",
                    MQTT_Status_strerror( xResult ) ) );
    }

    return xResult;
}

static void prvRegisterOTACallback( const char * pTopicFilter,
                                    uint16_t topicFilterLength )
{
    bool isMatch = false;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint16_t index = 0U;
    uint16_t numTopicFilters = sizeof( otaTopicFilterCallbacks ) / sizeof( OtaTopicFilterCallback_t );


    bool subscriptionAdded;

    ( void ) mqttStatus;

    /* Match the input topic filter against the wild-card pattern of topics filters
    * relevant for the OTA Update service to determine the type of topic filter. */
    for( ; index < numTopicFilters; index++ )
    {
        mqttStatus = MQTT_MatchTopic( pTopicFilter,
                                      topicFilterLength,
                                      otaTopicFilterCallbacks[ index ].pTopicFilter,
                                      otaTopicFilterCallbacks[ index ].topicFilterLength,
                                      &isMatch );
        assert( mqttStatus == MQTTSuccess );

        if( isMatch )
        {
            /* Add subscription so that incoming publishes are routed to the application callback. */
            subscriptionAdded = addSubscription( ( SubscriptionElement_t * ) xGlobalMqttAgentContext.pIncomingCallbackContext,
                                                 pTopicFilter,
                                                 topicFilterLength,
                                                 otaTopicFilterCallbacks[ index ].callback,
                                                 NULL );

            if( subscriptionAdded == false )
            {
                LogError( ( "Failed to register a publish callback for topic %.*s.",
                            pTopicFilter,
                            topicFilterLength ) );
            }
        }
    }
}

static BaseType_t prvSocketConnect( NetworkContext_t * pxNetworkContext )
{
    BaseType_t xConnected = pdFAIL;
    BackoffAlgorithmStatus_t xBackoffAlgStatus = BackoffAlgorithmSuccess;
    BackoffAlgorithmContext_t xReconnectParams = { 0 };
    uint16_t usNextRetryBackOff = 0U;

    TlsTransportStatus_t xNetworkStatus = TLS_TRANSPORT_CONNECT_FAILURE;
    NetworkCredentials_t xNetworkCredentials = { 0 };

    /* ALPN protocols must be a NULL-terminated list of strings. Therefore,
     * the first entry will contain the actual ALPN protocol string while the
     * second entry must remain NULL. */
    char * pcAlpnProtocols[] = { NULL, NULL };

    /* The ALPN string changes depending on whether username/password authentication is used. */
    #ifdef democonfigCLIENT_USERNAME
        pcAlpnProtocols[ 0 ] = AWS_IOT_CUSTOM_AUTH_ALPN;
    #else
        pcAlpnProtocols[ 0 ] = AWS_IOT_MQTT_ALPN;
    #endif
    xNetworkCredentials.pAlpnProtos = pcAlpnProtocols;

    /* Set the credentials for establishing a TLS connection. */
    xNetworkCredentials.pRootCa = ( const unsigned char * ) democonfigROOT_CA_PEM;
    xNetworkCredentials.rootCaSize = sizeof( democonfigROOT_CA_PEM );
    #ifdef democonfigCLIENT_CERTIFICATE_PEM
        xNetworkCredentials.pClientCert = ( const unsigned char * ) democonfigCLIENT_CERTIFICATE_PEM;
        xNetworkCredentials.clientCertSize = sizeof( democonfigCLIENT_CERTIFICATE_PEM );
        xNetworkCredentials.pPrivateKey = ( const unsigned char * ) democonfigCLIENT_PRIVATE_KEY_PEM;
        xNetworkCredentials.privateKeySize = sizeof( democonfigCLIENT_PRIVATE_KEY_PEM );
    #endif
    xNetworkCredentials.disableSni = democonfigDISABLE_SNI;


    /* We will use a retry mechanism with an exponential backoff mechanism and
     * jitter.  That is done to prevent a fleet of IoT devices all trying to
     * reconnect at exactly the same time should they become disconnected at
     * the same time. We initialize reconnect attempts and interval here. */
    BackoffAlgorithm_InitializeParams( &xReconnectParams,
                                       RETRY_BACKOFF_BASE_MS,
                                       RETRY_MAX_BACKOFF_DELAY_MS,
                                       RETRY_MAX_ATTEMPTS );

    /* Attempt to connect to MQTT broker. If connection fails, retry after a
     * timeout. Timeout value will exponentially increase until the maximum
     * number of attempts are reached.
     */
    do
    {
        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in democonfigMQTT_BROKER_ENDPOINT and
         * democonfigMQTT_BROKER_PORT at the top of this file. */
        LogInfo( ( "Creating a TLS connection to %s:%d.",
                   democonfigMQTT_BROKER_ENDPOINT,
                   democonfigMQTT_BROKER_PORT ) );
        xNetworkStatus = TLS_FreeRTOS_Connect( pxNetworkContext,
                                               democonfigMQTT_BROKER_ENDPOINT,
                                               democonfigMQTT_BROKER_PORT,
                                               &xNetworkCredentials,
                                               otaexampleTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                               otaexampleTRANSPORT_SEND_RECV_TIMEOUT_MS );
        xConnected = ( xNetworkStatus == TLS_TRANSPORT_SUCCESS ) ? pdPASS : pdFAIL;

        if( !xConnected )
        {
            /* Get back-off value (in milliseconds) for the next connection retry. */
            xBackoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &xReconnectParams, uxRand(), &usNextRetryBackOff );

            if( xBackoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the broker failed. "
                           "Retrying connection in %hu ms.",
                           usNextRetryBackOff ) );
                vTaskDelay( pdMS_TO_TICKS( usNextRetryBackOff ) );
            }
        }

        if( xBackoffAlgStatus == BackoffAlgorithmRetriesExhausted )
        {
            LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
        }
    } while( ( xConnected != pdPASS ) && ( xBackoffAlgStatus == BackoffAlgorithmSuccess ) );

    return xConnected;
}

/*-----------------------------------------------------------*/

static BaseType_t prvSocketDisconnect(NetworkContext_t* pxNetworkContext)
{
    BaseType_t xDisconnected = pdFAIL;

    LogInfo(("Disconnecting TLS connection.\n"));
    TLS_FreeRTOS_Disconnect(pxNetworkContext);
    xDisconnected = pdPASS;

    return xDisconnected;
}

static MQTTStatus_t prvMQTTInit( void )
{
    TransportInterface_t xTransport;
    MQTTStatus_t xReturn;
    MQTTFixedBuffer_t xFixedBuffer = { .pBuffer = xNetworkBuffer, .size = MQTT_AGENT_NETWORK_BUFFER_SIZE };
    static uint8_t staticQueueStorageArea[ MQTT_AGENT_COMMAND_QUEUE_LENGTH * sizeof( MQTTAgentCommand_t * ) ];
    static StaticQueue_t staticQueueStructure;
    MQTTAgentMessageInterface_t messageInterface =
    {
        .pMsgCtx        = NULL,
        .send           = Agent_MessageSend,
        .recv           = Agent_MessageReceive,
        .getCommand     = Agent_GetCommand,
        .releaseCommand = Agent_ReleaseCommand
    };

    LogDebug( ( "Creating command queue." ) );
    xCommandQueue.queue = xQueueCreateStatic( MQTT_AGENT_COMMAND_QUEUE_LENGTH,
                                              sizeof( MQTTAgentCommand_t* ),
                                              staticQueueStorageArea,
                                              &staticQueueStructure );
    configASSERT( xCommandQueue.queue );
    messageInterface.pMsgCtx = &xCommandQueue;

    /* Initialize the task pool. */
    Agent_InitializePool();

    /* Fill in Transport Interface send and receive function pointers. */
    xTransport.pNetworkContext = &xNetworkContextMqtt;
    xTransport.send = TLS_FreeRTOS_send;
    xTransport.recv = TLS_FreeRTOS_recv;

    /* Initialize MQTT library. */
    xReturn = MQTTAgent_Init( &xGlobalMqttAgentContext,
                              &messageInterface,
                              &xFixedBuffer,
                              &xTransport,
                              prvGetTimeMs,
                              prvIncomingPublishCallback,
                              /* Context to pass into the callback. Passing the pointer to subscription array. */
                              xGlobalSubscriptionList );

    return xReturn;
}

static MQTTStatus_t prvMQTTConnect( bool xCleanSession )
{
    MQTTStatus_t xResult;
    MQTTConnectInfo_t xConnectInfo;
    bool xSessionPresent = false;

    /* Many fields are not used in this demo so start with everything at 0. */
    memset( &xConnectInfo, 0x00, sizeof( xConnectInfo ) );

    /* Start with a clean session i.e. direct the MQTT broker to discard any
     * previous session data. Also, establishing a connection with clean session
     * will ensure that the broker does not store any data when this client
     * gets disconnected. */
    xConnectInfo.cleanSession = xCleanSession;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    xConnectInfo.pClientIdentifier = democonfigCLIENT_IDENTIFIER;
    xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( democonfigCLIENT_IDENTIFIER );

    /* Set MQTT keep-alive period. It is the responsibility of the application
     * to ensure that the interval between Control Packets being sent does not
     * exceed the Keep Alive value. In the absence of sending any other Control
     * Packets, the Client MUST send a PINGREQ Packet.  This responsibility will
     * be moved inside the agent. */
    xConnectInfo.keepAliveSeconds = otaexampleKEEP_ALIVE_INTERVAL_SECONDS;

    /* Append metrics when connecting to the AWS IoT Core broker. */
    #ifdef democonfigUSE_AWS_IOT_CORE_BROKER
        #ifdef democonfigCLIENT_USERNAME
            xConnectInfo.pUserName = CLIENT_USERNAME_WITH_METRICS;
            xConnectInfo.userNameLength = ( uint16_t ) strlen( CLIENT_USERNAME_WITH_METRICS );
            xConnectInfo.pPassword = democonfigCLIENT_PASSWORD;
            xConnectInfo.passwordLength = ( uint16_t ) strlen( democonfigCLIENT_PASSWORD );
        #else
            xConnectInfo.pUserName = AWS_IOT_METRICS_STRING;
            xConnectInfo.userNameLength = AWS_IOT_METRICS_STRING_LENGTH;
            /* Password for authentication is not used. */
            xConnectInfo.pPassword = NULL;
            xConnectInfo.passwordLength = 0U;
        #endif
    #else /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */
        #ifdef democonfigCLIENT_USERNAME
            xConnectInfo.pUserName = democonfigCLIENT_USERNAME;
            xConnectInfo.userNameLength = ( uint16_t ) strlen( democonfigCLIENT_USERNAME );
            xConnectInfo.pPassword = democonfigCLIENT_PASSWORD;
            xConnectInfo.passwordLength = ( uint16_t ) strlen( democonfigCLIENT_PASSWORD );
        #endif /* ifdef democonfigCLIENT_USERNAME */
    #endif /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */

    /* Send MQTT CONNECT packet to broker. MQTT's Last Will and Testament feature
     * is not used in this demo, so it is passed as NULL. */
    xResult = MQTT_Connect( &( xGlobalMqttAgentContext.mqttContext ),
                            &xConnectInfo,
                            NULL,
                            otaexampleCONNACK_RECV_TIMEOUT_MS,
                            &xSessionPresent );

    LogInfo( ( "Session present: %d\n", xSessionPresent ) );

    /* Resume a session if desired. */
    if( ( xResult == MQTTSuccess ) && ( xCleanSession == false ) )
    {
        xResult = MQTTAgent_ResumeSession( &xGlobalMqttAgentContext, xSessionPresent );

        /* Resubscribe to all the subscribed topics. */
        if( ( xResult == MQTTSuccess ) && ( xSessionPresent == false ) )
        {
            xResult = prvHandleResubscribe();
        }
    }

    return xResult;
}

static void prvConnectToMQTTBroker( void )
{
    BaseType_t xNetworkStatus = pdFAIL;
    MQTTStatus_t xMQTTStatus;

    /* Initialize network context. */
    xNetworkContextMqtt.pParams = &xTlsTransportParams;

    /* Connect a TCP socket to the broker. */
    xNetworkStatus = prvSocketConnect( &xNetworkContextMqtt );
    configASSERT( xNetworkStatus == pdPASS );

    /* Initialize the MQTT context with the buffer and transport interface. */
    xMQTTStatus = prvMQTTInit();
    configASSERT( xMQTTStatus == MQTTSuccess );

    /* Form an MQTT connection without a persistent session. */
    xMQTTStatus = prvMQTTConnect( true );
    configASSERT( xMQTTStatus == MQTTSuccess );
}

static void prvDisconnectFromMQTTBroker( void )
{
    MQTTAgentCommandContext_t xCommandContext = { 0 };
    MQTTAgentCommandInfo_t xCommandParams = { 0 };
    MQTTStatus_t xCommandStatus;

    /* Disconnect from broker. */
    LogInfo( ( "Disconnecting the MQTT connection with %s.", democonfigMQTT_BROKER_ENDPOINT ) );

    xCommandParams.blockTimeMs = MQTT_AGENT_SEND_BLOCK_TIME_MS;
    xCommandParams.cmdCompleteCallback = prvCommandCallback;
    xCommandParams.pCmdCompleteCallbackContext = &xCommandContext;
    xCommandContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
    xCommandContext.pArgs = NULL;
    xCommandContext.xReturnStatus = MQTTSendFailed;

    /* Disconnect MQTT session. */
    xCommandStatus = MQTTAgent_Disconnect( &xGlobalMqttAgentContext, &xCommandParams );
    configASSERT( xCommandStatus == MQTTSuccess );

    xTaskNotifyWait( 0,
                     0,
                     NULL,
                     pdMS_TO_TICKS( MQTT_AGENT_MS_TO_WAIT_FOR_NOTIFICATION ) );

    /* End TLS session, then close TCP connection. */
    prvSocketDisconnect( &xNetworkContextMqtt );
}

static OtaMqttStatus_t prvMQTTSubscribe(const char* pTopicFilter,
    uint16_t topicFilterLength,
    uint8_t ucQoS)
{
    MQTTStatus_t mqttStatus;
    uint32_t ulNotifiedValue;
    MQTTAgentSubscribeArgs_t xSubscribeArgs = { 0 };
    MQTTSubscribeInfo_t xSubscribeInfo = { 0 };
    BaseType_t result;
    MQTTAgentCommandInfo_t xCommandParams = { 0 };
    MQTTAgentCommandContext_t xApplicationDefinedContext = { 0 };
    OtaMqttStatus_t otaRet = OtaMqttSuccess;

    configASSERT(pTopicFilter != NULL);
    configASSERT(topicFilterLength > 0);

    xSubscribeInfo.pTopicFilter = pTopicFilter;
    xSubscribeInfo.topicFilterLength = topicFilterLength;
    xSubscribeInfo.qos = ucQoS;
    xSubscribeArgs.pSubscribeInfo = &xSubscribeInfo;
    xSubscribeArgs.numSubscriptions = 1;

    xApplicationDefinedContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
    xApplicationDefinedContext.pArgs = &xSubscribeArgs;
    xApplicationDefinedContext.xReturnStatus = MQTTSendFailed;

    xCommandParams.blockTimeMs = otaexampleMQTT_TIMEOUT_MS;
    xCommandParams.cmdCompleteCallback = prvMQTTSubscribeCompleteCallback;
    xCommandParams.pCmdCompleteCallbackContext = (void*)&xApplicationDefinedContext;

    xTaskNotifyStateClear(NULL);

    mqttStatus = MQTTAgent_Subscribe(&xGlobalMqttAgentContext,
        &xSubscribeArgs,
        &xCommandParams);

    /* Wait for command to complete so MQTTSubscribeInfo_t remains in scope for the
     * duration of the command. */
    if (mqttStatus == MQTTSuccess)
    {
        result = xTaskNotifyWait(0, otaexampleMAX_UINT32, &ulNotifiedValue, pdMS_TO_TICKS(otaexampleMQTT_TIMEOUT_MS));

        if (result == pdTRUE)
        {
            mqttStatus = xApplicationDefinedContext.xReturnStatus;
        }
        else
        {
            mqttStatus = MQTTRecvFailed;
        }
    }

    if (mqttStatus != MQTTSuccess)
    {
        LogError(("Failed to SUBSCRIBE to topic with error = %u.",
            mqttStatus));

        otaRet = OtaMqttSubscribeFailed;
    }
    else
    {
        LogInfo(("Subscribed to topic %.*s.\n\n",
            topicFilterLength,
            pTopicFilter));

        otaRet = OtaMqttSuccess;
    }

    return otaRet;
}

static OtaMqttStatus_t prvMQTTPublish(const char* const pacTopic,
    uint16_t topicLen,
    const char* pMsg,
    uint32_t msgSize,
    uint8_t qos)
{
    OtaMqttStatus_t otaRet = OtaMqttSuccess;
    BaseType_t result;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTPublishInfo_t publishInfo = { 0 };
    MQTTAgentCommandInfo_t xCommandParams = { 0 };
    MQTTAgentCommandContext_t xCommandContext = { 0 };

    publishInfo.pTopicName = pacTopic;
    publishInfo.topicNameLength = topicLen;
    publishInfo.qos = qos;
    publishInfo.pPayload = pMsg;
    publishInfo.payloadLength = msgSize;

    xCommandContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
    xTaskNotifyStateClear(NULL);

    xCommandParams.blockTimeMs = otaexampleMQTT_TIMEOUT_MS;
    xCommandParams.cmdCompleteCallback = prvCommandCallback;
    xCommandParams.pCmdCompleteCallbackContext = (void*)&xCommandContext;

    mqttStatus = MQTTAgent_Publish(&xGlobalMqttAgentContext,
        &publishInfo,
        &xCommandParams);

    /* Wait for command to complete so MQTTSubscribeInfo_t remains in scope for the
     * duration of the command. */
    if (mqttStatus == MQTTSuccess)
    {
        result = xTaskNotifyWait(0, otaexampleMAX_UINT32, NULL, pdMS_TO_TICKS(otaexampleMQTT_TIMEOUT_MS));

        if (result != pdTRUE)
        {
            mqttStatus = MQTTSendFailed;
        }
        else
        {
            mqttStatus = xCommandContext.xReturnStatus;
        }
    }

    if (mqttStatus != MQTTSuccess)
    {
        LogError(("Failed to send PUBLISH packet to broker with error = %u.", mqttStatus));
        otaRet = OtaMqttPublishFailed;
    }
    else
    {
        LogInfo(("Sent PUBLISH packet to broker %.*s to broker.\n\n",
            topicLen,
            pacTopic));

        otaRet = OtaMqttSuccess;
    }

    return otaRet;
}

static OtaMqttStatus_t prvMQTTUnsubscribe(const char* pTopicFilter,
    uint16_t topicFilterLength,
    uint8_t ucQoS)
{
    MQTTStatus_t mqttStatus;
    uint32_t ulNotifiedValue;
    MQTTAgentSubscribeArgs_t xSubscribeArgs = { 0 };
    MQTTSubscribeInfo_t xSubscribeInfo = { 0 };
    BaseType_t result;
    MQTTAgentCommandInfo_t xCommandParams = { 0 };
    MQTTAgentCommandContext_t xApplicationDefinedContext = { 0 };
    OtaMqttStatus_t otaRet = OtaMqttSuccess;

    configASSERT(pTopicFilter != NULL);
    configASSERT(topicFilterLength > 0);

    xSubscribeInfo.pTopicFilter = pTopicFilter;
    xSubscribeInfo.topicFilterLength = topicFilterLength;
    xSubscribeInfo.qos = ucQoS;
    xSubscribeArgs.pSubscribeInfo = &xSubscribeInfo;
    xSubscribeArgs.numSubscriptions = 1;


    xApplicationDefinedContext.xTaskToNotify = xTaskGetCurrentTaskHandle();

    xCommandParams.blockTimeMs = otaexampleMQTT_TIMEOUT_MS;
    xCommandParams.cmdCompleteCallback = prvMQTTUnsubscribeCompleteCallback;
    xCommandParams.pCmdCompleteCallbackContext = (void*)&xApplicationDefinedContext;

    LogInfo((" Unsubscribing to topic filter: %s", pTopicFilter));
    xTaskNotifyStateClear(NULL);


    mqttStatus = MQTTAgent_Unsubscribe(&xGlobalMqttAgentContext,
        &xSubscribeArgs,
        &xCommandParams);

    /* Wait for command to complete so MQTTSubscribeInfo_t remains in scope for the
     * duration of the command. */
    if (mqttStatus == MQTTSuccess)
    {
        result = xTaskNotifyWait(0, otaexampleMAX_UINT32, &ulNotifiedValue, pdMS_TO_TICKS(otaexampleMQTT_TIMEOUT_MS));

        if (result == pdTRUE)
        {
            mqttStatus = xApplicationDefinedContext.xReturnStatus;
        }
        else
        {
            mqttStatus = MQTTRecvFailed;
        }
    }

    if (mqttStatus != MQTTSuccess)
    {
        LogError(("Failed to UNSUBSCRIBE from topic %.*s with error = %u.",
            topicFilterLength,
            pTopicFilter,
            mqttStatus));

        otaRet = OtaMqttUnsubscribeFailed;
    }
    else
    {
        LogInfo(("UNSUBSCRIBED from topic %.*s.\n\n",
            topicFilterLength,
            pTopicFilter));

        otaRet = OtaMqttSuccess;
    }

    return otaRet;
}

/*-----------------------------------------------------------*/

static void setOtaInterfaces(OtaInterfaces_t* pOtaInterfaces)
{
    configASSERT(pOtaInterfaces != NULL);

    /* Initialize OTA library OS Interface. */
    pOtaInterfaces->os.event.init = OtaInitEvent_FreeRTOS;
    pOtaInterfaces->os.event.send = OtaSendEvent_FreeRTOS;
    pOtaInterfaces->os.event.recv = OtaReceiveEvent_FreeRTOS;
    pOtaInterfaces->os.event.deinit = OtaDeinitEvent_FreeRTOS;
    pOtaInterfaces->os.timer.start = OtaStartTimer_FreeRTOS;
    pOtaInterfaces->os.timer.stop = OtaStopTimer_FreeRTOS;
    pOtaInterfaces->os.timer.delete = OtaDeleteTimer_FreeRTOS;
    pOtaInterfaces->os.mem.malloc = Malloc_FreeRTOS;
    pOtaInterfaces->os.mem.free = Free_FreeRTOS;

    /* Initialize the OTA library MQTT Interface.*/
    pOtaInterfaces->mqtt.subscribe = prvMQTTSubscribe;
    pOtaInterfaces->mqtt.publish = prvMQTTPublish;
    pOtaInterfaces->mqtt.unsubscribe = prvMQTTUnsubscribe;

    /* Initialize the OTA library PAL Interface.*/
    pOtaInterfaces->pal.getPlatformImageState = otaPal_GetPlatformImageState;
    pOtaInterfaces->pal.setPlatformImageState = otaPal_SetPlatformImageState;
    pOtaInterfaces->pal.writeBlock = otaPal_WriteBlock;
    pOtaInterfaces->pal.activate = otaPal_ActivateNewImage;
    pOtaInterfaces->pal.closeFile = otaPal_CloseFile;
    pOtaInterfaces->pal.reset = otaPal_ResetDevice;
    pOtaInterfaces->pal.abort = otaPal_Abort;
    pOtaInterfaces->pal.createFile = otaPal_CreateFileForRx;
}

/*-----------------------------------------------------------*/

static void prvOTAAgentTask(void* pParam)
{
    /* Calling OTA agent task. */
    OTA_EventProcessingTask(pParam);
    LogInfo(("OTA Agent stopped."));

    vTaskDelete(NULL);
}

static void prvMQTTAgentTask(void* pParam)
{
    BaseType_t xResult = pdFAIL;
    MQTTStatus_t xMQTTStatus = MQTTSuccess;

    (void)pParam;

    do
    {
        /* MQTTAgent_CommandLoop() is effectively the agent implementation.  It
         * will manage the MQTT protocol until such time that an error occurs,
         * which could be a disconnect.  If an error occurs the MQTT context on
         * which the error happened is returned so there can be an attempt to
         * clean up and reconnect however the application writer prefers. */
        xMQTTStatus = MQTTAgent_CommandLoop(&xGlobalMqttAgentContext);

        /* Clear Agent queue so that no any pending MQTT operations are processed. */
        xQueueReset(xCommandQueue.queue);

        /* Success is returned for application initiated disconnect or termination. The socket will also be disconnected by the caller. */
        if (xMQTTStatus != MQTTSuccess)
        {
            xResult = prvSuspendOTA();
            configASSERT(xResult == pdPASS);

            LogInfo(("Suspended OTA agent."));

            /* End TLS session, then close TCP connection. */
            prvSocketDisconnect(&xNetworkContextMqtt);

            /* Connect to MQTT broker. */
            prvConnectToMQTTBroker();

            xResult = prvResumeOTA();
            configASSERT(xResult == pdPASS);

            LogInfo(("Resumed OTA agent."));
        }
    } while (xMQTTStatus != MQTTSuccess);

    vTaskDelete(NULL);
}

static BaseType_t prvSuspendOTA(void)
{
    /* OTA library return status. */
    OtaErr_t otaRet = OtaErrNone;
    BaseType_t status = pdPASS;
    uint32_t suspendTimeout;

    otaRet = OTA_Suspend();

    if (otaRet == OtaErrNone)
    {
        suspendTimeout = OTA_SUSPEND_TIMEOUT_MS;

        while ((OTA_GetState() != OtaAgentStateSuspended) && (suspendTimeout > 0))
        {
            /* Wait for OTA Library state to suspend */
            vTaskDelay(pdMS_TO_TICKS(otaexampleTASK_DELAY_MS));
            suspendTimeout -= otaexampleTASK_DELAY_MS;
        }

        if (OTA_GetState() != OtaAgentStateSuspended)
        {
            LogError(("Failed to suspend OTA."));
            status = pdFAIL;
        }
    }
    else
    {
        LogError(("Error while trying to suspend OTA agent %d", otaRet));
        status = pdFAIL;
    }

    return status;
}

static BaseType_t prvResumeOTA(void)
{
    /* OTA library return status. */
    OtaErr_t otaRet = OtaErrNone;
    BaseType_t status = pdPASS;
    uint32_t suspendTimeout;

    otaRet = OTA_Resume();

    if (otaRet == OtaErrNone)
    {
        suspendTimeout = OTA_SUSPEND_TIMEOUT_MS;

        while ((OTA_GetState() == OtaAgentStateSuspended) && (suspendTimeout > 0))
        {
            /* Wait for OTA Library state to suspend */
            vTaskDelay(pdMS_TO_TICKS(otaexampleTASK_DELAY_MS));
            suspendTimeout -= otaexampleTASK_DELAY_MS;
        }

        if (OTA_GetState() == OtaAgentStateSuspended)
        {
            LogError(("Failed to resume OTA."));
            status = pdFAIL;
        }
    }
    else
    {
        LogError(("Error while trying to resume OTA agent %d", otaRet));
        status = pdFAIL;
    }

    return status;
}

static BaseType_t prvRunOTADemo( void )
{
    /* Status indicating a successful demo or not. */
    BaseType_t xStatus = pdPASS;

    /* OTA library return status. */
    OtaErr_t otaRet = OtaErrNone;

    /* OTA event message used for sending event to OTA Agent.*/
    OtaEventMsg_t eventMsg = { 0 };

    /* OTA interface context required for library interface functions.*/
    OtaInterfaces_t otaInterfaces;

    /* OTA library packet statistics per job.*/
    OtaAgentStatistics_t otaStatistics = { 0 };

    /* OTA Agent state returned from calling OTA_GetState.*/
    OtaState_t state = OtaAgentStateStopped;

    /* Set OTA Library interfaces.*/
    setOtaInterfaces( &otaInterfaces );

    /****************************** Init OTA Library. ******************************/

    if( xStatus == pdPASS )
    {
        if( ( otaRet = OTA_Init( &otaBuffer,
                                 &otaInterfaces,
                                 ( const uint8_t * ) ( democonfigCLIENT_IDENTIFIER ),
                                 otaAppCallback ) ) != OtaErrNone )
        {
            LogError( ( "Failed to initialize OTA Agent, exiting = %u.",
                        otaRet ) );

            xStatus = pdFAIL;
        }
    }

    /****************************** Create OTA Agent Task. ******************************/

    if( xStatus == pdPASS )
    {
        xStatus = xTaskCreate( prvOTAAgentTask,
                               "OTA Agent Task",
                               OTA_AGENT_TASK_STACK_SIZE,
                               NULL,
                               OTA_AGENT_TASK_PRIORITY,
                               NULL );

        if( xStatus != pdPASS )
        {
            LogError( ( "Failed to create OTA agent task:" ) );
        }
    }

    /**
     * Register a callback for receiving messages intended for OTA agent from broker,
     * for which the topic has not been subscribed for.
     */
    prvRegisterOTACallback( OTA_DEFAULT_TOPIC_FILTER, OTA_DEFAULT_TOPIC_FILTER_LENGTH );

    /****************************** Start OTA ******************************/

    if( xStatus == pdPASS )
    {
        /* Send start event to OTA Agent.*/
        eventMsg.eventId = OtaAgentEventStart;
        OTA_SignalEvent( &eventMsg );
    }

    /****************************** Loop and display OTA statistics ******************************/

    if( xStatus == pdPASS )
    {
        while( ( state = OTA_GetState() ) != OtaAgentStateStopped )
        {
            /* Get OTA statistics for currently executing job. */
            if( state != OtaAgentStateSuspended )
            {
                OTA_GetStatistics( &otaStatistics );

                LogInfo( ( " Received: %u   Queued: %u   Processed: %u   Dropped: %u",
                           otaStatistics.otaPacketsReceived,
                           otaStatistics.otaPacketsQueued,
                           otaStatistics.otaPacketsProcessed,
                           otaStatistics.otaPacketsDropped ) );
            }

            vTaskDelay( pdMS_TO_TICKS(otaexampleTASK_DELAY_MS) );
        }
    }

    /**
     * Remvove callback for receiving messages intended for OTA agent from broker,
     * for which the topic has not been subscribed for.
     */
    removeSubscription( ( SubscriptionElement_t * ) xGlobalMqttAgentContext.pIncomingCallbackContext,
                        OTA_DEFAULT_TOPIC_FILTER,
                        OTA_DEFAULT_TOPIC_FILTER_LENGTH );

    return xStatus;
}

/**
 * @brief Entry point of Ota demo task.
 *
 * This example initializes the OTA library to enable OTA updates via the
 * MQTT broker. It simply connects to the MQTT broker with the users
 * credentials and spins in an indefinite loop to allow MQTT messages to be
 * forwarded to the OTA agent for possible processing. The OTA agent does all
 * of the real work; checking to see if the message topic is one destined for
 * the OTA agent. If not, it is simply ignored.
 *
 */
static void vOtaDemoTask( void* pvParam )
{
    /* Return error status. */
    BaseType_t xReturnStatus = pdPASS;

    /* Flag for MQTT init status. */
    bool mqttInitialized = false;

    ( void )pvParam;

    LogInfo( ( "OTA over MQTT demo, Application version %u.%u.%u",
               appFirmwareVersion.u.x.major,
               appFirmwareVersion.u.x.minor,
               appFirmwareVersion.u.x.build ) );

    /* Initialize semaphore for buffer operations. */
    xBufferSemaphore = xSemaphoreCreateMutex();

    if( xBufferSemaphore == NULL )
    {
        LogError( ( "Failed to initialize buffer semaphore." ) );
        xReturnStatus = pdFAIL;
    }

    /****************************** Init MQTT ******************************/

    if(xReturnStatus == pdPASS )
    {
        /* Create the TCP connection to the broker, then the MQTT connection to the
         * same. */
        prvConnectToMQTTBroker();
    }

    /****************************** Create MQTT Agent Task. ******************************/

    if(xReturnStatus == pdPASS )
    {
        if( xTaskCreate( prvMQTTAgentTask,
                         "MQTT Agent Task",
                         MQTT_AGENT_TASK_STACK_SIZE,
                         NULL,
                         MQTT_AGENT_TASK_PRIORITY,
                         NULL ) != pdPASS )
        {
            xReturnStatus = pdFAIL;
            LogError( ( "Failed to create MQTT agent task:" ) );
        }
    }

    /****************************** Start OTA Demo. ******************************/

    if(xReturnStatus == pdPASS)
    {
        /* Start OTA demo. The function returns only if OTA completes successfully and a
         * shutdown of OTA is triggered for a manual restart of the device.*/
        if( prvRunOTADemo() != pdPASS )
        {
            xReturnStatus = pdFAIL;
        }
    }

    /****************************** Cleanup ******************************/

    if( mqttInitialized )
    {
        prvDisconnectFromMQTTBroker();
    }

    if( xBufferSemaphore != NULL )
    {
        /* Cleanup semaphore created for buffer operations. */
        vSemaphoreDelete( xBufferSemaphore );
    }
}

/*
 * @brief Create the task that demonstrates the Ota demo.
 */
void vStartOtaDemo(void)
{
    /* 
     * vOtaDemoTask() connects to the MQTT broker, creates the
     * MQTT Agent task and calls the Ota demo loop prvRunOTADemo() 
     * which creates the OTA Agent task. 
     */

    xTaskCreate(vOtaDemoTask, /* Function that implements the task. */
        "OTA Demo Task",             /* Text name for the task - only used for debugging. */
        democonfigDEMO_STACKSIZE,     /* Size of stack (in words, not bytes) to allocate for the task. */
        NULL,                         /* Optional - task parameter - not used in this case. */
        tskIDLE_PRIORITY + 1,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
        NULL);                       /* Optional - used to pass out a handle to the created task. */
}
