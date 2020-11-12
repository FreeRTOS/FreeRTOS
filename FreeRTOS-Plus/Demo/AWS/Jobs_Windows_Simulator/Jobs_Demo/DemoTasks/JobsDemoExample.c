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

/**
 * @file JobsDemoExample.c
 *
 * @brief Demo for showing use of the Jobs library API. This demo uses the Jobs library
 * along with the coreMQTT, mbedTLS and FreeRTOS+TCP libraries to communicate with the AWS IoT Jobs service.
 * Please refer to AWS documentation for more information about AWS IoT Jobs.
 * https://docs.aws.amazon.com/iot/latest/developerguide/iot-jobs.html
 *
 * The Jobs library API provides macros and helper functions for assembling MQTT topics strings,
 * and for determining whether an incoming MQTT message is related to the AWS IoT Jobs service.
 * The Jobs library does not depend on a MQTT library, therefore the code for MQTT connections
 * are placed in another file (mqtt_demo_helpers.c). to make it easy to read the demo code using the
 * Jobs library.
 *
 * @note This demo requires setup of an AWS account, provisioning of a Thing resource on the AWS IoT account,
 * and the creation of Jobs for the Thing resource. Please refer to AWS CLI documentation for more information in creating a
 * job document.
 * https://docs.aws.amazon.com/cli/latest/reference/iot/create-job.html
 *
 * This demo connects to the AWS IoT broker and calls the MQTT APIs of the AWS IoT Jobs service to receive
 * jobs queued (as JSON documents) for the Thing resource (associated with this demo application) on the cloud,
 * then executes the jobs and updates the status of the jobs back to the cloud.
 * The demo expects job documents to have an "action" JSON key. Actions can
 * be one of "print", "publish", or "exit".
 * Print Jobs log a message to the local console, and must contain a "message",
 * e.g. { "action": "print", "message": "Hello World!" }.
 * Publish Jobs publish a message to an MQTT Topic. The job document must
 * contain a "message" and "topic" to publish to, e.g.
 * { "action": "publish", "topic": "demo/jobs", "message": "Hello World!" }.
 * An Exit Job exits the demo. Sending { "action": "exit" } will end the program.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* Demo Specific config file. */
#include "demo_config.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Jobs library header. */
#include "jobs.h"

/* JSON library includes. */
#include "core_json.h"

/* Include common MQTT demo helpers. */
#include "mqtt_demo_helpers.h"

/*------------- Demo configurations -------------------------*/

#ifndef democonfigTHING_NAME
    #define democonfigTHING_NAME    democonfigCLIENT_IDENTIFIER
#endif

/**
 * @brief The length of #democonfigTHING_NAME.
 */
#define THING_NAME_LENGTH    ( ( uint16_t ) ( sizeof( democonfigTHING_NAME ) - 1 ) )

/*-----------------------------------------------------------*/

/**
 * @brief The JSON key of the execution object.
 *
 * Job documents received from the AWS IoT Jobs service are in JSON format.
 * All such JSON documents will contain this key, whose value represents the unique
 * identifier of a Job.
 */
#define jobsexampleEXECUTION_KEY                    "execution"

/**
 * @brief The length of #jobsexampleEXECUTION_KEY.
 */
#define jobsexampleEXECUTION_KEY_LENGTH             ( sizeof( jobsexampleEXECUTION_KEY ) - 1 )

/**
 * @brief The query key to use for searching the Job ID key in message payload
 * from AWS IoT Jobs service.
 *
 * Job documents received from the AWS IoT Jobs service are in JSON format.
 * All such JSON documents will contain this key, whose value represents the unique
 * identifier of a Job.
 */
#define jobsexampleQUERY_KEY_FOR_JOB_ID             jobsexampleEXECUTION_KEY  ".jobId"

/**
 * @brief The length of #jobsexampleQUERY_KEY_FOR_JOB_ID.
 */
#define jobsexampleQUERY_KEY_FOR_JOB_ID_LENGTH      ( sizeof( jobsexampleQUERY_KEY_FOR_JOB_ID ) - 1 )

/**
 * @brief The query key to use for searching the Jobs document ID key in message payload
 * from AWS IoT Jobs service.
 *
 * Job documents received from the AWS IoT Jobs service are in JSON format.
 * All such JSON documents will contain this key, whose value represents the unique
 * identifier of a Job.
 */
#define jobsexampleQUERY_KEY_FOR_JOBS_DOC           jobsexampleEXECUTION_KEY  ".jobDocument"

/**
 * @brief The length of #jobsexampleQUERY_KEY_FOR_JOBS_DOC.
 */
#define jobsexampleQUERY_KEY_FOR_JOBS_DOC_LENGTH    ( sizeof( jobsexampleQUERY_KEY_FOR_JOBS_DOC ) - 1 )

/**
 * @brief The query key to use for searching the Action key in Jobs document
 * from AWS IoT Jobs service.
 *
 * This demo program expects this key to be in the Job document. It is a key
 * specific to this demo.
 */
#define jobsexampleQUERY_KEY_FOR_ACTION             jobsexampleQUERY_KEY_FOR_JOBS_DOC ".action"

/**
 * @brief The length of #jobsexampleQUERY_KEY_FOR_ACTION.
 */
#define jobsexampleQUERY_KEY_FOR_ACTION_LENGTH      ( sizeof( jobsexampleQUERY_KEY_FOR_ACTION ) - 1 )

/**
 * @brief The query key to use for searching the Message key in Jobs document
 * from AWS IoT Jobs service.
 *
 * This demo program expects this key to be in the Job document if the "action"
 * is either "publish" or "print". It represents the message that should be
 * published or printed, respectively.
 */
#define jobsexampleQUERY_KEY_FOR_MESSAGE            jobsexampleQUERY_KEY_FOR_JOBS_DOC ".message"

/**
 * @brief The length of #jobsexampleQUERY_KEY_FOR_MESSAGE.
 */
#define jobsexampleQUERY_KEY_FOR_MESSAGE_LENGTH     ( sizeof( jobsexampleQUERY_KEY_FOR_MESSAGE ) - 1 )

/**
 * @brief The query key to use for searching the topic key in Jobs document
 * from AWS IoT Jobs service.
 *
 * This demo program expects this key to be in the Job document if the "action"
 * is "publish". It represents the MQTT topic on which the message should be
 * published.
 */
#define jobsexampleQUERY_KEY_FOR_TOPIC              jobsexampleQUERY_KEY_FOR_JOBS_DOC ".topic"

/**
 * @brief The length of #jobsexampleQUERY_KEY_FOR_TOPIC.
 */
#define jobsexampleQUERY_KEY_FOR_TOPIC_LENGTH       ( sizeof( jobsexampleQUERY_KEY_FOR_TOPIC ) - 1 )

/**
 * @brief Utility macro to generate the PUBLISH topic string to the
 * DescribePendingJobExecution API of AWS IoT Jobs service for requesting
 * the next pending job information.
 *
 * @param[in] thingName The name of the Thing resource to query for the
 * next pending job.
 */
#define START_NEXT_JOB_TOPIC( thingName ) \
    ( JOBS_API_PREFIX thingName JOBS_API_BRIDGE JOBS_API_STARTNEXT )

/**
 * @brief Utility macro to generate the subscription topic string for the
 * NextJobExecutionChanged API of AWS IoT Jobs service that is required
 * for getting notification about changes in the next pending job in the queue.
 *
 * @param[in] thingName The name of the Thing resource to query for the
 * next pending Job.
 */
#define NEXT_JOB_EXECUTION_CHANGED_TOPIC( thingName ) \
    ( JOBS_API_PREFIX thingName JOBS_API_BRIDGE JOBS_API_NEXTJOBCHANGED )

/**
 * @brief Format a JSON status message.
 *
 * @param[in] x one of "IN_PROGRESS", "SUCCEEDED", or "FAILED"
 */
#define MAKE_STATUS_REPORT( x )    "{\"status\":\"" x "\"}"

/*-----------------------------------------------------------*/

/**
 * @brief Currently supported actions that a job document can specify.
 */
typedef enum JobActionType
{
    JOB_ACTION_PRINT,   /**< Print a message. */
    JOB_ACTION_PUBLISH, /**< Publish a message to an MQTT topic. */
    JOB_ACTION_EXIT,    /**< Exit the demo. */
    JOB_ACTION_UNKNOWN  /**< Unknown action. */
} JobActionType;

/*-----------------------------------------------------------*/

/**
 * @brief The MQTT context used for MQTT operation.
 */
static MQTTContext_t xMqttContext;

/**
 * @brief The network context used for Openssl operation.
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
 * @brief A global flag which represents whether a job for the "Exit" action
 * has been received from AWS IoT Jobs service.
 */
static BaseType_t xExitActionJobReceived = pdFALSE;

/**
 * @brief A global flag which represents whether an error was encountered while
 * executing the demo.
 *
 * @note When this flag is set, the demo terminates execution.
 */
static BaseType_t xDemoEncounteredError = pdFALSE;

/*-----------------------------------------------------------*/

/**
 * @brief Converts a string in a job document to a #JobActionType
 * value.
 *
 * @param[in] pcAction The job action as a string.
 * @param[in] xActionLength The length of @p pcAction.
 *
 * @return A #JobActionType equivalent to the given string.
 */
static JobActionType prvGetAction( const char * pcAction,
                                   size_t xActionLength );

/**
 * @brief This example uses the MQTT library of the AWS IoT Device SDK for
 * Embedded C. This is the prototype of the callback function defined by
 * that library. It will be invoked whenever the MQTT library receives an
 * incoming message.
 *
 * @param[in] pxMqttContext MQTT context pointer.
 * @param[in] pxPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pxDeserializedInfo Deserialized information from the incoming packet.
 */
static void prvEventCallback( MQTTContext_t * pxMqttContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              MQTTDeserializedInfo_t * pxDeserializedInfo );

/**
 * @brief Process payload from $aws/things/<thingName>/jobs/start-next/accepted topic.
 *
 * This handler parses the payload received about the next pending job to identify
 * the action requested in the job document, and perform the appropriate
 * action to execute the job.
 *
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 * @param[in] pcJobId The ID of the next pending job in queue.
 * @param[in] usJobIdLength The length of the job ID string.
 */
static void prvStartNextJobHandler( MQTTPublishInfo_t * pxPublishInfo,
                                    char * pJobId,
                                    uint16_t usJobIdLength );

/**
 * @brief Sends an update for a job to the UpdateJobExecution API of the AWS IoT Jobs service.
 *
 * @param[in] pcJobId The job ID whose status has to be updated.
 * @param[in] usJobIdLength The length of the job ID string.
 * @param[in] pcJobStatusReport The JSON formatted report to send to the AWS IoT Jobs service
 * to update the status of @p pcJobId.
 */
static void prvSendUpdateForJob( char * pcJobId,
                                 uint16_t usJobIdLength,
                                 const char * pcJobStatusReport );

/**
 * @brief Executes a job received from AWS IoT Jobs service and sends an update back to the service.
 * It parses the received job document, executes the job depending on the job "Action" type, and
 * sends an update to AWS for the Job.
 *
 * @param[in] pxPublishInfo The PUBLISH packet containing the job document received from the
 * AWS IoT Jobs service.
 * @param[in] pcJobId The ID of the job to execute.
 * @param[in] usJobIdLength The length of the job ID string.
 */
static void prvProcessJobDocument( MQTTPublishInfo_t * pxPublishInfo,
                                   char * pcJobId,
                                   uint16_t usJobIdLength );

/**
 * @brief The task used to demonstrate the Jobs library API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation.
 * Not used in this example.
 */
static void prvJobsDemoTask( void * pvParameters );


/*-----------------------------------------------------------*/

static JobActionType prvGetAction( const char * pcAction,
                                   size_t xActionLength )
{
    JobActionType xAction = JOB_ACTION_UNKNOWN;

    configASSERT( pcAction != NULL );

    if( strncmp( pcAction, "print", xActionLength ) == 0 )
    {
        xAction = JOB_ACTION_PRINT;
    }
    else if( strncmp( pcAction, "publish", xActionLength ) == 0 )
    {
        xAction = JOB_ACTION_PUBLISH;
    }
    else if( strncmp( pcAction, "exit", xActionLength ) == 0 )
    {
        xAction = JOB_ACTION_EXIT;
    }

    return xAction;
}

static void prvSendUpdateForJob( char * pcJobId,
                                 uint16_t usJobIdLength,
                                 const char * pcJobStatusReport )
{
    char pUpdateJobTopic[ JOBS_API_MAX_LENGTH( THING_NAME_LENGTH ) ];
    size_t ulTopicLength = 0;
    JobsStatus_t xStatus = JobsSuccess;

    configASSERT( ( pcJobId != NULL ) && ( usJobIdLength > 0 ) );
    configASSERT( pcJobStatusReport != NULL );

    /* Generate the PUBLISH topic string for the UpdateJobExecution API of AWS IoT Jobs service. */
    xStatus = Jobs_Update( pUpdateJobTopic,
                           sizeof( pUpdateJobTopic ),
                           democonfigTHING_NAME,
                           THING_NAME_LENGTH,
                           pcJobId,
                           usJobIdLength,
                           &ulTopicLength );

    if( xStatus == JobsSuccess )
    {
        if( xPublishToTopic( &xMqttContext,
                             pUpdateJobTopic,
                             ulTopicLength,
                             pcJobStatusReport,
                             strlen( pcJobStatusReport ) ) == pdFALSE )
        {
            /* Set global flag to terminate demo as PUBLISH operation to update job status failed. */
            xDemoEncounteredError = pdTRUE;

            LogError( ( "Failed to update the status of job: JobID=%.*s, NewStatePayload=%s",
                        usJobIdLength, pcJobId, pcJobStatusReport ) );
        }
    }
    else
    {
        /* Set global flag to terminate demo as topic generation for UpdateJobExecution API failed. */
        xDemoEncounteredError = pdTRUE;

        LogError( ( "Failed to generate Publish topic string for sending job update: "
                    "JobID=%.*s, NewStatePayload=%s",
                    usJobIdLength, pcJobId, pcJobStatusReport ) );
    }
}

static void prvProcessJobDocument( MQTTPublishInfo_t * pxPublishInfo,
                                   char * pcJobId,
                                   uint16_t usJobIdLength )
{
    char * pcAction = NULL;
    size_t uActionLength = 0U;
    JSONStatus_t xJsonStatus = JSONSuccess;

    configASSERT( pxPublishInfo != NULL );
    configASSERT( ( pxPublishInfo->pPayload != NULL ) && ( pxPublishInfo->payloadLength > 0 ) );

    xJsonStatus = JSON_Search( ( char * ) pxPublishInfo->pPayload,
                               pxPublishInfo->payloadLength,
                               jobsexampleQUERY_KEY_FOR_ACTION,
                               jobsexampleQUERY_KEY_FOR_ACTION_LENGTH,
                               &pcAction,
                               &uActionLength );

    if( xJsonStatus != JSONSuccess )
    {
        LogError( ( "Job document schema is invalid. Missing expected \"action\" key in document." ) );
        prvSendUpdateForJob( pcJobId, usJobIdLength, MAKE_STATUS_REPORT( "FAILED" ) );
    }
    else
    {
        JobActionType xActionType = JOB_ACTION_UNKNOWN;
        char * pcMessage = NULL;
        size_t ulMessageLength = 0U;

        xActionType = prvGetAction( pcAction, uActionLength );

        switch( xActionType )
        {
            case JOB_ACTION_EXIT:
                LogInfo( ( "Received job contains \"exit\" action. Updating state of demo." ) );
                xExitActionJobReceived = pdTRUE;
                prvSendUpdateForJob( pcJobId, usJobIdLength, MAKE_STATUS_REPORT( "SUCCEEDED" ) );
                break;

            case JOB_ACTION_PRINT:
                LogInfo( ( "Received job contains \"print\" action." ) );

                xJsonStatus = JSON_Search( ( char * ) pxPublishInfo->pPayload,
                                           pxPublishInfo->payloadLength,
                                           jobsexampleQUERY_KEY_FOR_MESSAGE,
                                           jobsexampleQUERY_KEY_FOR_MESSAGE_LENGTH,
                                           &pcMessage,
                                           &ulMessageLength );

                if( xJsonStatus == JSONSuccess )
                {
                    /* Print the given message if the action is "print". */
                    LogInfo( ( "\r\n"
                               "/*-----------------------------------------------------------*/\r\n"
                               "\r\n"
                               "%.*s\r\n"
                               "\r\n"
                               "/*-----------------------------------------------------------*/\r\n"
                               "\r\n", ulMessageLength, pcMessage ) );
                    prvSendUpdateForJob( pcJobId, usJobIdLength, MAKE_STATUS_REPORT( "SUCCEEDED" ) );
                }
                else
                {
                    LogError( ( "Job document schema is invalid. Missing \"message\" for \"print\" action type." ) );
                    prvSendUpdateForJob( pcJobId, usJobIdLength, MAKE_STATUS_REPORT( "FAILED" ) );
                }

                break;

            case JOB_ACTION_PUBLISH:
                LogInfo( ( "Received job contains \"publish\" action." ) );
                char * pcTopic = NULL;
                size_t ulTopicLength = 0U;

                xJsonStatus = JSON_Search( ( char * ) pxPublishInfo->pPayload,
                                           pxPublishInfo->payloadLength,
                                           jobsexampleQUERY_KEY_FOR_TOPIC,
                                           jobsexampleQUERY_KEY_FOR_TOPIC_LENGTH,
                                           &pcTopic,
                                           &ulTopicLength );

                /* Search for "topic" key in the Jobs document.*/
                if( xJsonStatus != JSONSuccess )
                {
                    LogError( ( "Job document schema is invalid. Missing \"topic\" key for \"publish\" action type." ) );
                    prvSendUpdateForJob( pcJobId, usJobIdLength, MAKE_STATUS_REPORT( "FAILED" ) );
                }
                else
                {
                    xJsonStatus = JSON_Search( ( char * ) pxPublishInfo->pPayload,
                                               pxPublishInfo->payloadLength,
                                               jobsexampleQUERY_KEY_FOR_MESSAGE,
                                               jobsexampleQUERY_KEY_FOR_MESSAGE_LENGTH,
                                               &pcMessage,
                                               &ulMessageLength );

                    /* Search for "message" key in Jobs document.*/
                    if( xJsonStatus == JSONSuccess )
                    {
                        /* Publish to the parsed MQTT topic with the message obtained from
                         * the Jobs document.*/
                        if( xPublishToTopic( &xMqttContext,
                                             pcTopic,
                                             ulTopicLength,
                                             pcMessage,
                                             ulMessageLength ) == pdFALSE )
                        {
                            /* Set global flag to terminate demo as PUBLISH operation to execute job failed. */
                            xDemoEncounteredError = pdTRUE;

                            LogError( ( "Failed to execute job with \"publish\" action: Failed to publish to topic. "
                                        "JobID=%.*s, Topic=%.*s",
                                        usJobIdLength, pcJobId, ulTopicLength, pcTopic ) );
                        }

                        prvSendUpdateForJob( pcJobId, usJobIdLength, MAKE_STATUS_REPORT( "SUCCEEDED" ) );
                    }
                    else
                    {
                        LogError( ( "Job document schema is invalid. Missing \"message\" key for \"publish\" action type." ) );
                        prvSendUpdateForJob( pcJobId, usJobIdLength, MAKE_STATUS_REPORT( "FAILED" ) );
                    }
                }

                break;

            default:
                configPRINTF( ( "Received Job document with unknown action %.*s.",
                                uActionLength, pcAction ) );
                break;
        }
    }
}

static void prvStartNextJobHandler( MQTTPublishInfo_t * pxPublishInfo,
                                    char * pJobId,
                                    uint16_t usJobIdLength )
{
    JSONStatus_t xJsonStatus = JSONSuccess;

    configASSERT( pxPublishInfo != NULL );
    configASSERT( ( pxPublishInfo->pPayload != NULL ) && ( pxPublishInfo->payloadLength > 0 ) );

    /* Check validity of JSON message response from server.*/
    xJsonStatus = JSON_Validate( pxPublishInfo->pPayload, pxPublishInfo->payloadLength );

    if( xJsonStatus != JSONSuccess )
    {
        LogError( ( "Received invalid JSON payload from AWS IoT Jobs service" ) );
    }
    else
    {
        /* Process the Job document and execute the job. */
        prvProcessJobDocument( pxPublishInfo, pcJobId, ( uint16_t ) ulJobIdLength );
    }
}

/*-----------------------------------------------------------*/

/* This is the callback function invoked by the MQTT stack when it receives
 * incoming messages. This function demonstrates how to use the Jobs_MatchTopic
 * function to determine whether the incoming message is a Jobs message
 * or not. If it is, it handles the message depending on the message type.
 */
static void prvEventCallback( MQTTContext_t * pxMqttContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              MQTTDeserializedInfo_t * pxDeserializedInfo )
{
    uint16_t usPacketIdentifier;

    ( void ) pxMqttContext;

    configASSERT( pxDeserializedInfo != NULL );
    configASSERT( pxMqttContext != NULL );
    configASSERT( pxPacketInfo != NULL );

    usPacketIdentifier = pxDeserializedInfo->packetIdentifier;

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pxPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        configASSERT( pxDeserializedInfo->pPublishInfo != NULL );
        JobsTopic_t topicType = JobsMaxTopic;
        char * pcJobId = NULL;
        uint16_t usJobIdLength = 0;
        JobsStatus_t xStatus = JobsError;

        LogDebug( ( "Received an incoming publish message: TopicName=%.*s",
                    pxDeserializedInfo->pPublishInfo->topicNameLength,
                    ( const char * ) pxDeserializedInfo->pPublishInfo->pTopicName ) );

        /* Let the Jobs library tell us whether this is a Jobs message. */
        xStatus = Jobs_MatchTopic( ( char * ) pxDeserializedInfo->pPublishInfo->pTopicName,
                                   pxDeserializedInfo->pPublishInfo->topicNameLength,
                                   democonfigTHING_NAME,
                                   THING_NAME_LENGTH,
                                   &topicType,
                                   &pcJobId,
                                   &usJobIdLength );

        if( xStatus == JobsSuccess )
        {
            /* Upon successful return, the messageType has been filled in. */
            if( ( topicType == JobsStartNextSuccess ) || ( topicType == JobsNextJobChanged ) )
            {
                /* Handler function to process payload. */
                prvStartNextJobHandler( pxDeserializedInfo->pPublishInfo, pcJobId, usJobIdLength );
            }
            else if( topicType == JobsUpdateSuccess )
            {
                LogInfo( ( "Job update status request has been accepted by AWS Iot Jobs service." ) );
            }
            else if( topicType == JobsStartNextFailed )
            {
                LogWarn( ( "Request for next job description rejected: RejectedResponse=%.*s.",
                           pxDeserializedInfo->pPublishInfo->payloadLength,
                           ( const char * ) pxDeserializedInfo->pPublishInfo->pPayload ) );
            }
            else if( topicType == JobsUpdateFailed )
            {
                /* Set the global flag to terminate the demo, because the request for updating and executing the job status
                 * has been rejected by the AWS IoT Jobs service. */
                xDemoEncounteredError = pdTRUE;

                LogWarn( ( "Request for job update rejected: RejectedResponse=%.*s.",
                           pxDeserializedInfo->pPublishInfo->payloadLength,
                           ( const char * ) pxDeserializedInfo->pPublishInfo->pPayload ) );

                LogError( ( "Terminating demo as request to update job status has been rejected by "
                            "AWS IoT Jobs service..." ) );
            }
            else
            {
                LogWarn( ( "Received an unexpected messages from AWS IoT Jobs service: "
                           "JobsTopicType=%u", topicType ) );
            }
        }
        else if( xStatus == JobsNoMatch )
        {
            LogWarn( ( "Incoming message topic does not belong to AWS IoT Jobs!: topic=%.*s",
                       pxDeserializedInfo->pPublishInfo->topicNameLength,
                       ( const char * ) pxDeserializedInfo->pPublishInfo->pTopicName ) );
        }
        else
        {
            LogError( ( "Failed to parse incoming publish job. Topic=%.*s!",
                        pxDeserializedInfo->pPublishInfo->topicNameLength,
                        ( const char * ) pxDeserializedInfo->pPublishInfo->pTopicName ) );
        }
    }
    else
    {
        vHandleOtherIncomingPacket( pxPacketInfo, usPacketIdentifier );
    }
}

/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the Jobs library API via a
 * MQTT mutually authenticated network connection with the AWS IoT broker.
 */
void vStartJobsDemo( void )
{
    /* This example uses a single application task, which shows that how to
    * use Jobs library to generate and validate AWS IoT Jobs service MQTT topics
    * via coreMQTT library to communicate with the AWS IoT Jobs service. */
    xTaskCreate( prvJobsDemoTask,          /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of the Jobs demo.
 *
 * This main function demonstrates how to use the Jobs library API library.
 *
 * This demo uses helper functions for MQTT operations that have internal
 * loops to process incoming messages. Those are not the focus of this demo
 * and therefore, are placed in a separate file mqtt_demo_helpers.c.
 *
 * This function also shows that the communication with the AWS IoT Jobs services does
 * not require explicit subscriptions to the response MQTT topics for request commands that
 * sent to the MQTT APIs (like DescribeJobExecution API) of the service. The service
 * will send messages on the response topics for the request commands on the same
 * MQTT connection irrespective of whether the client subscribes to the response topics.
 * Therefore, this demo processes incoming messages from response topics of DescribeJobExecution
 * and UpdateJobExecution APIs without explicitly subscribing to the topics.
 */
void prvJobsDemoTask( void * pvParameters )
{
    BaseType_t xDemoStatus = pdPASS;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Establish an MQTT connection with AWS IoT over a mutually authenticated TLS session. */
    xDemoStatus = xEstablishMqttSession( &xMqttContext,
                                         &xNetworkContext,
                                         &xBuffer,
                                         prvEventCallback );

    if( xDemoStatus == pdFAIL )
    {
        /* Log error to indicate connection failure. */
        LogError( ( "Failed to connect to AWS IoT broker." ) );
    }
    else
    {
        /* Print out a short user guide to the console. The default logging
         * limit of 255 characters can be changed in demo_logging.c, but breaking
         * up the only instance of a 1000+ character string is more practical. */
        LogInfo( ( "\r\n"
                   "/*-----------------------------------------------------------*/\r\n"
                   "\r\n"
                   "The Jobs demo is now ready to accept Jobs.\r\n"
                   "Jobs may be created using the AWS IoT console or AWS CLI.\r\n"
                   "See the following link for more information.\r\n" ) );
        LogInfo( ( "\r"
                   "https://docs.aws.amazon.com/cli/latest/reference/iot/create-job.html\r\n"
                   "\r\n"
                   "This demo expects Job documents to have an \"action\" JSON key.\r\n"
                   "The following actions are currently supported:\r\n" ) );
        LogInfo( ( "\r"
                   " - print          \r\n"
                   "   Logs a message to the local console. The Job document must also contain a \"message\".\r\n"
                   "   For example: { \"action\": \"print\", \"message\": \"Hello world!\"} will cause\r\n"
                   "   \"Hello world!\" to be printed on the console.\r\n" ) );
        LogInfo( ( "\r"
                   " - publish        \r\n"
                   "   Publishes a message to an MQTT topic. The Job document must also contain a \"message\" and \"topic\".\r\n" ) );
        LogInfo( ( "\r"
                   "   For example: { \"action\": \"publish\", \"topic\": \"demo/jobs\", \"message\": \"Hello world!\"} will cause\r\n"
                   "   \"Hello world!\" to be published to the topic \"demo/jobs\".\r\n" ) );
        LogInfo( ( "\r"
                   " - exit           \r\n"
                   "   Exits the demo program. This program will run until { \"action\": \"exit\" } is received.\r\n"
                   "\r\n"
                   "/*-----------------------------------------------------------*/\r\n" ) );

        /* Subscribe to the NextJobExecutionChanged API topic to receive notifications about the next pending
         * job in the queue for the Thing resource used by this demo. */
        if( xSubscribeToTopic( &xMqttContext,
                               NEXT_JOB_EXECUTION_CHANGED_TOPIC( democonfigTHING_NAME ),
                               sizeof( NEXT_JOB_EXECUTION_CHANGED_TOPIC( democonfigTHING_NAME ) - 1 ) ) != pdPASS )
        {
            xDemoStatus = pdFAIL;
            LogError( ( "Failed to subscribe to NextJobExecutionChanged API of AWS IoT Jobs service: Topic=%s",
                        NEXT_JOB_EXECUTION_CHANGED_TOPIC( democonfigTHING_NAME ) ) );
        }
    }

    /* Keep on running the demo until we receive a job for the "Exit" action to exit the demo. */
    while( ( xExitActionJobReceived == pdFALSE ) &&
           ( xDemoEncounteredError == pdFALSE ) &&
           ( xDemoStatus == pdPASS ) )
    {
        /* Publish to AWS IoT Jobs on the DescribeJobExecution API to request the next pending job.
         *
         * Note: It is not required to make MQTT subscriptions to the response topics of the
         * DescribeJobExecution API because the AWS IoT Jobs service sends responses for the PUBLISH
         * commands on the same MQTT connection irrespective of whether the client has subscribed to the
         * response topics or not.
         * This demo processes incoming messages from the response topics of the API in the prvEventCallback()
         * handler that is supplied to the coreMQTT library. */
        xDemoStatus = xPublishToTopic( &xMqttContext,
                                       START_NEXT_JOB_TOPIC( democonfigTHING_NAME ),
                                       sizeof( START_NEXT_JOB_TOPIC( democonfigTHING_NAME ) ) - 1,
                                       NULL,
                                       0 );

        /* Delay before next iteration. */
        LogInfo( ( "Adding some delay before requesting the next pending job..." ) );
        vTaskDelay( pdMS_TO_TICKS( 300 ) );
    }

    /* Unsubscribe from the NextJobExecutionChanged API topic. */
    if( xSubscribeToTopic( &xMqttContext,
                           NEXT_JOB_EXECUTION_CHANGED_TOPIC( democonfigTHING_NAME ),
                           sizeof( NEXT_JOB_EXECUTION_CHANGED_TOPIC( democonfigTHING_NAME ) - 1 ) ) != pdPASS )
    {
        LogError( ( "Failed to subscribe unsubscribe from the NextJobExecutionChanged API of AWS IoT Jobs service: "
                    "Topic=%s", NEXT_JOB_EXECUTION_CHANGED_TOPIC( democonfigTHING_NAME ) ) );
    }

    /* Disconnect the MQTT and network connections with AWS IoT. */
    if( xDisconnectMqttSession( &xMqttContext, &xNetworkContext ) != pdPASS )
    {
        LogError( ( "Disconnection from AWS Iot failed..." ) );
    }

    /* Delete this demo task. */
    LogInfo( ( "Deleting Jobs Demo task." ) );
    vTaskDelete( NULL );
}
