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
 * Demo for showing how to use the Device Shadow library's API. This version
 * of the Device Shadow API provides macros and helper functions for assembling MQTT topics
 * strings, and for determining whether an incoming MQTT message is related to the
 * device shadow. The Device Shadow library does not depend on a MQTT library,
 * therefore the code for MQTT connections are placed in another file (shadow_demo_helpers.c)
 * to make it easy to read the code using Device Shadow library.
 *
 * This example assumes there is a powerOn state in the device shadow. It does the
 * following operations:
 * 1. Establish a MQTT connection by using the helper functions in shadow_demo_helpers.c.
 * 2. Assemble strings for the MQTT topics of device shadow, by using macros defined by the Device Shadow library.
 * 3. Subscribe to those MQTT topics by using helper functions in shadow_demo_helpers.c.
 * 4. Publish a desired state of powerOn by using helper functions in shadow_demo_helpers.c.  That will cause
 * a delta message to be sent to device.
 * 5. Handle incoming MQTT messages in prvEventCallback, determine whether the message is related to the device
 * shadow by using a function defined by the Device Shadow library (Shadow_MatchTopic). If the message is a
 * device shadow delta message, set a flag for the main function to know, then the main function will publish
 * a second message to update the reported state of powerOn.
 * 6. Handle incoming message again in prvEventCallback. If the message is from update/accepted, verify that it
 * has the same clientToken as previously published in the update message. That will mark the end of the demo.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Shadow API header. */
#include "shadow.h"

/* JSON library includes. */
#include "core_json.h"

/* Include MQTT demo helpers header. */
#include "mqtt_demo_helpers.h"

/* Demo Specific config file. */
#include "demo_config.h"


/**
 * @brief Format string representing a Shadow document with a "desired" state.
 *
 * The real json document will look like this:
 * {
 *   "state": {
 *     "desired": {
 *       "powerOn": 1
 *     }
 *   },
 *   "clientToken": "021909"
 * }
 *
 * Note the client token, which is optional for all Shadow updates. The client
 * token must be unique at any given time, but may be reused once the update is
 * completed. For this demo, a timestamp is used for a client token.
 */
#define SHADOW_DESIRED_JSON     \
    "{"                         \
    "\"state\":{"               \
    "\"desired\":{"             \
    "\"powerOn\":%01d"          \
    "}"                         \
    "},"                        \
    "\"clientToken\":\"%06lu\"" \
    "}"

/**
 * @brief The expected size of #SHADOW_DESIRED_JSON.
 *
 * Because all the format specifiers in #SHADOW_DESIRED_JSON include a length,
 * its full actual size is known by pre-calculation, here's the formula why
 * the length need to minus 3:
 * 1. The length of "%01d" is 4.
 * 2. The length of %06lu is 5.
 * 3. The actual length we will use in case 1. is 1 ( for the state of powerOn ).
 * 4. The actual length we will use in case 2. is 6 ( for the clientToken length ).
 * 5. Thus the additional size 3 = 4 + 5 - 1 - 6 + 1 (termination character).
 *
 * In your own application, you could calculate the size of the json doc in this way.
 */
#define SHADOW_DESIRED_JSON_LENGTH    ( sizeof( SHADOW_DESIRED_JSON ) - 3 )

/**
 * @brief Format string representing a Shadow document with a "reported" state.
 *
 * The real json document will look like this:
 * {
 *   "state": {
 *     "reported": {
 *       "powerOn": 1
 *     }
 *   },
 *   "clientToken": "021909"
 * }
 *
 * Note the client token, which is required for all Shadow updates. The client
 * token must be unique at any given time, but may be reused once the update is
 * completed. For this demo, a timestamp is used for a client token.
 */
#define SHADOW_REPORTED_JSON    \
    "{"                         \
    "\"state\":{"               \
    "\"reported\":{"            \
    "\"powerOn\":%01d"          \
    "}"                         \
    "},"                        \
    "\"clientToken\":\"%06lu\"" \
    "}"

/**
 * @brief The expected size of #SHADOW_REPORTED_JSON.
 *
 * Because all the format specifiers in #SHADOW_REPORTED_JSON include a length,
 * its full size is known at compile-time by pre-calculation. Users could refer to
 * the way how to calculate the actual length in #SHADOW_DESIRED_JSON_LENGTH.
 */
#define SHADOW_REPORTED_JSON_LENGTH    ( sizeof( SHADOW_REPORTED_JSON ) - 3 )

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef SHADOW_MAX_DEMO_LOOP_COUNT
    #define SHADOW_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in ticks to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_TICKS       ( pdMS_TO_TICKS( 5000U ) )

/**
 * @brief The maximum number of times to call MQTT_ProcessLoop() when waiting
 * for a response for Shadow delete operation.
 */
#define MQTT_PROCESS_LOOP_DELETE_RESPONSE_COUNT_MAX     ( 30U )

/**
 * @brief Timeout for MQTT_ProcessLoop in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS                    ( 700U )

/**
 * @brief JSON key for response code that indicates the type of error in
 * the error document received on topic `/delete/rejected`.
 */
#define SHADOW_DELETE_REJECTED_ERROR_CODE_KEY           "code"

/**
 * @brief Length of #SHADOW_DELETE_REJECTED_ERROR_CODE_KEY.
 */
#define SHADOW_DELETE_REJECTED_ERROR_CODE_KEY_LENGTH    ( ( uint16_t ) ( sizeof( SHADOW_DELETE_REJECTED_ERROR_CODE_KEY ) - 1 ) )

/**
 * @brief Error response code sent from AWS IoT Shadow service when an attempt
 * is made to delete a Shadow document that doesn't exist.
 */
#define SHADOW_NO_SHADOW_EXISTS_ERROR_CODE              "404"

/**
 * @brief Length of #SHADOW_NO_SHADOW_EXISTS_ERROR_CODE.
 */
#define SHADOW_NO_SHADOW_EXISTS_ERROR_CODE_LENGTH       ( ( uint16_t ) ( sizeof( SHADOW_NO_SHADOW_EXISTS_ERROR_CODE ) - 1 ) )

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
    .pBuffer = ucSharedBuffer,
    .size    = democonfigNETWORK_BUFFER_SIZE
};

/**
 * @brief The simulated device current power on state.
 */
static uint32_t ulCurrentPowerOnState = 0;

/**
 * @brief The flag to indicate the device current power on state changed.
 */
static bool stateChanged = pdFALSE;

/**
 * @brief When we send an update to the device shadow, and if we care about
 * the response from cloud (accepted/rejected), remember the clientToken and
 * use it to match with the response.
 */
static uint32_t ulClientToken = 0U;

/**
 * @brief The return status of prvUpdateDeltaHandler callback function.
 */
static BaseType_t xUpdateDeltaReturn = pdPASS;

/**
 * @brief The return status of prvUpdateAcceptedHandler callback function.
 */
static BaseType_t xUpdateAcceptedReturn = pdPASS;

/**
 * @brief Status of the response of Shadow delete operation from AWS IoT
 * message broker.
 */
static BaseType_t xDeleteResponseReceived = pdFALSE;

/**
 * @brief Status of the Shadow delete operation.
 *
 * The Shadow delete status will be updated by the incoming publishes on the
 * MQTT topics for delete acknowledgement from AWS IoT message broker
 * (accepted/rejected). Shadow document is considered to be deleted if an
 * incoming publish is received on `/delete/accepted` topic or an incoming
 * publish is received on `/delete/rejected` topic with error code 404. Code 404
 * indicates that the Shadow document does not exist for the Thing yet.
 */
static BaseType_t xShadowDeleted = pdFALSE;

/*-----------------------------------------------------------*/

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
 * @brief Process payload from /update/delta topic.
 *
 * This handler examines the version number and the powerOn state. If powerOn
 * state has changed, it sets a flag for the main function to take further actions.
 *
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void prvUpdateDeltaHandler( MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief Process payload from /update/accepted topic.
 *
 * This handler examines the accepted message that carries the same clientToken
 * as sent before.
 *
 * @param[in] pxPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void prvUpdateAcceptedHandler( MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief The task used to demonstrate the Shadow API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvShadowDemoTask( void * pvParameters );

/**
 * @brief Process payload from `/delete/rejected` topic.
 *
 * This handler examines the rejected message to look for the reject reason code.
 * If the reject reason code is `404`, an attempt was made to delete a shadow
 * document which was not present yet. This is considered to be success for this
 * demo application.
 *
 * @param[in] pxPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void prvDeleteRejectedHandler( MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief Helper function to wait for a response for Shadow delete operation.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 *
 * @return pdPASS if successfully received a response for Shadow delete
 * operation; pdFAIL otherwise.
 */
static BaseType_t prvWaitForDeleteResponse( MQTTContext_t * pxMQTTContext );

/*-----------------------------------------------------------*/

static BaseType_t prvWaitForDeleteResponse( MQTTContext_t * pxMQTTContext )
{
    uint8_t ucCount = 0U;
    MQTTStatus_t xMQTTStatus = MQTTSuccess;
    BaseType_t xReturnStatus = pdPASS;

    configASSERT( pxMQTTContext != NULL );

    while( ( xDeleteResponseReceived != pdTRUE ) &&
           ( ucCount++ < MQTT_PROCESS_LOOP_DELETE_RESPONSE_COUNT_MAX ) &&
           ( xMQTTStatus == MQTTSuccess ) )
    {
        /* Event callback will set #xDeleteResponseReceived when receiving an
         * incoming publish on either `/delete/accepted` or `/delete/rejected`
         * Shadow topics. */
        xMQTTStatus = MQTT_ProcessLoop( pxMQTTContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    if( ( xMQTTStatus != MQTTSuccess ) || ( xDeleteResponseReceived != pdTRUE ) )
    {
        LogError( ( "MQTT_ProcessLoop failed to receive a response for Shadow delete operation:"
                    " LoopDuration=%u, MQTT Status=%s.",
                    ( MQTT_PROCESS_LOOP_TIMEOUT_MS * ucCount ),
                    MQTT_Status_strerror( xMQTTStatus ) ) );
        xReturnStatus = pdFAIL;
    }

    return xReturnStatus;
}

/*-----------------------------------------------------------*/

static void prvDeleteRejectedHandler( MQTTPublishInfo_t * pxPublishInfo )
{
    JSONStatus_t result = JSONSuccess;
    char * pcOutValue = NULL;
    uint32_t ulOutValueLength = 0UL;

    configASSERT( pxPublishInfo != NULL );
    configASSERT( pxPublishInfo->pPayload != NULL );

    LogInfo( ( "/delete/rejected json payload:%s.", ( const char * ) pxPublishInfo->pPayload ) );

    /* The payload will look similar to this:
     * {
     *    "code": error-code,
     *    "message": "error-message",
     *    "timestamp": timestamp,
     *    "clientToken": "token"
     * }
     */

    /* Make sure the payload is a valid json document. */
    result = JSON_Validate( pxPublishInfo->pPayload,
                            pxPublishInfo->payloadLength );

    if( result == JSONSuccess )
    {
        /* Then we start to get the version value by JSON keyword "version". */
        result = JSON_SearchConst( pxPublishInfo->pPayload,
                                   pxPublishInfo->payloadLength,
                                   SHADOW_DELETE_REJECTED_ERROR_CODE_KEY,
                                   SHADOW_DELETE_REJECTED_ERROR_CODE_KEY_LENGTH,
                                   &pcOutValue,
                                   ( size_t * ) &ulOutValueLength,
                                   NULL );
    }
    else
    {
        LogError( ( "The json document is invalid!!" ) );
    }

    if( result == JSONSuccess )
    {
        LogInfo( ( "Error code is: %.*s.",
                   ulOutValueLength,
                   pcOutValue ) );

        /* Check if error code is `404`. An error code `404` indicates that an
         * attempt was made to delete a Shadow document that didn't exist. */
        if( ulOutValueLength == SHADOW_NO_SHADOW_EXISTS_ERROR_CODE_LENGTH )
        {
            if( strncmp( pcOutValue, SHADOW_NO_SHADOW_EXISTS_ERROR_CODE,
                         SHADOW_NO_SHADOW_EXISTS_ERROR_CODE_LENGTH ) == 0 )
            {
                xShadowDeleted = pdTRUE;
            }
        }
    }
    else
    {
        LogError( ( "No error code in json document!!" ) );
    }
}

/*-----------------------------------------------------------*/

static void prvUpdateDeltaHandler( MQTTPublishInfo_t * pxPublishInfo )
{
    static uint32_t ulCurrentVersion = 0; /* Remember the latestVersion # we've ever received */
    uint32_t ulVersion = 0U;
    uint32_t ulNewState = 0U;
    char * pcOutValue = NULL;
    uint32_t ulOutValueLength = 0U;
    JSONStatus_t result = JSONSuccess;

    configASSERT( pxPublishInfo != NULL );
    configASSERT( pxPublishInfo->pPayload != NULL );

    LogInfo( ( "/update/delta json payload:%s.", ( const char * ) pxPublishInfo->pPayload ) );

    /* The payload will look similar to this:
     * {
     *      "version": 12,
     *      "timestamp": 1595437367,
     *      "state": {
     *          "powerOn": 1
     *      },
     *      "metadata": {
     *          "powerOn": {
     *          "timestamp": 1595437367
     *          }
     *      },
     *      "clientToken": "388062"
     *  }
     */

    /* Make sure the payload is a valid json document. */
    result = JSON_Validate( pxPublishInfo->pPayload,
                            pxPublishInfo->payloadLength );

    if( result == JSONSuccess )
    {
        /* Then we start to get the version value by JSON keyword "version". */
        result = JSON_Search( ( char * ) pxPublishInfo->pPayload,
                              pxPublishInfo->payloadLength,
                              "version",
                              sizeof( "version" ) - 1,
                              &pcOutValue,
                              ( size_t * ) &ulOutValueLength );
    }
    else
    {
        LogError( ( "The json document is invalid!!" ) );
    }

    if( result == JSONSuccess )
    {
        LogInfo( ( "version: %.*s",
                   ulOutValueLength,
                   pcOutValue ) );

        /* Convert the extracted value to an unsigned integer value. */
        ulVersion = ( uint32_t ) strtoul( pcOutValue, NULL, 10 );
    }
    else
    {
        LogError( ( "No version in json document!!" ) );
    }

    LogInfo( ( "version:%d, ulCurrentVersion:%d \r\n", ulVersion, ulCurrentVersion ) );

    /* When the version is much newer than the one we retained, that means the powerOn
     * state is valid for us. */
    if( ulVersion > ulCurrentVersion )
    {
        /* Set to received version as the current version. */
        ulCurrentVersion = ulVersion;

        /* Get powerOn state from json documents. */
        result = JSON_Search( ( char * ) pxPublishInfo->pPayload,
                              pxPublishInfo->payloadLength,
                              "state.powerOn",
                              sizeof( "state.powerOn" ) - 1,
                              &pcOutValue,
                              ( size_t * ) &ulOutValueLength );
    }
    else
    {
        /* In this demo, we discard the incoming message
         * if the version number is not newer than the latest
         * that we've received before. Your application may use a
         * different approach.
         */
        LogWarn( ( "The received version is smaller than current one!!" ) );
    }

    if( result == JSONSuccess )
    {
        /* Convert the powerOn state value to an unsigned integer value. */
        ulNewState = ( uint32_t ) strtoul( pcOutValue, NULL, 10 );

        LogInfo( ( "The new power on state newState:%d, ulCurrentPowerOnState:%d \r\n",
                   ulNewState, ulCurrentPowerOnState ) );

        if( ulNewState != ulCurrentPowerOnState )
        {
            /* The received powerOn state is different from the one we retained before, so we switch them
             * and set the flag. */
            ulCurrentPowerOnState = ulNewState;

            /* State change will be handled in main(), where we will publish a "reported"
             * state to the device shadow. We do not do it here because we are inside of
             * a callback from the MQTT library, so that we don't re-enter
             * the MQTT library. */
            stateChanged = true;
        }
    }
    else
    {
        LogError( ( "No powerOn in json document!!" ) );
        xUpdateDeltaReturn = pdFAIL;
    }
}

/*-----------------------------------------------------------*/

static void prvUpdateAcceptedHandler( MQTTPublishInfo_t * pxPublishInfo )
{
    char * pcOutValue = NULL;
    uint32_t ulOutValueLength = 0U;
    uint32_t ulReceivedToken = 0U;
    JSONStatus_t result = JSONSuccess;

    configASSERT( pxPublishInfo != NULL );
    configASSERT( pxPublishInfo->pPayload != NULL );

    LogInfo( ( "/update/accepted json payload:%s.", ( const char * ) pxPublishInfo->pPayload ) );

    /* Handle the reported state with state change in /update/accepted topic.
     * Thus we will retrieve the client token from the json document to see if
     * it's the same one we sent with reported state on the /update topic.
     * The payload will look similar to this:
     *  {
     *      "state": {
     *          "reported": {
     *          "powerOn": 1
     *          }
     *      },
     *      "metadata": {
     *          "reported": {
     *          "powerOn": {
     *              "timestamp": 1596573647
     *          }
     *          }
     *      },
     *      "version": 14698,
     *      "timestamp": 1596573647,
     *      "clientToken": "022485"
     *  }
     */

    /* Make sure the payload is a valid json document. */
    result = JSON_Validate( pxPublishInfo->pPayload,
                            pxPublishInfo->payloadLength );

    if( result == JSONSuccess )
    {
        /* Get clientToken from json documents. */
        result = JSON_Search( ( char * ) pxPublishInfo->pPayload,
                              pxPublishInfo->payloadLength,
                              "clientToken",
                              sizeof( "clientToken" ) - 1,
                              &pcOutValue,
                              ( size_t * ) &ulOutValueLength );
    }
    else
    {
        LogError( ( "Invalid json documents !!" ) );
    }

    if( result == JSONSuccess )
    {
        LogInfo( ( "clientToken: %.*s", ulOutValueLength,
                   pcOutValue ) );

        /* Convert the code to an unsigned integer value. */
        ulReceivedToken = ( uint32_t ) strtoul( pcOutValue, NULL, 10 );

        LogInfo( ( "receivedToken:%u, clientToken:%u \r\n", ulReceivedToken, ulClientToken ) );

        /* If the clientToken in this update/accepted message matches the one we
         * published before, it means the device shadow has accepted our latest
         * reported state. We are done. */
        if( ulReceivedToken == ulClientToken )
        {
            LogInfo( ( "Received response from the device shadow. Previously published "
                       "update with clientToken=%u has been accepted. ", ulClientToken ) );
        }
        else
        {
            LogWarn( ( "The received clientToken=%u is not identical with the one=%u we sent ",
                       ulReceivedToken, ulClientToken ) );
        }
    }
    else
    {
        LogError( ( "No clientToken in json document!!" ) );
        xUpdateAcceptedReturn = pdFAIL;
    }
}

/*-----------------------------------------------------------*/

/* This is the callback function invoked by the MQTT stack when it receives
 * incoming messages. This function demonstrates how to use the Shadow_MatchTopic
 * function to determine whether the incoming message is a device shadow message
 * or not. If it is, it handles the message depending on the message type.
 */
static void prvEventCallback( MQTTContext_t * pxMqttContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              MQTTDeserializedInfo_t * pxDeserializedInfo )
{
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pcThingName = NULL;
    uint16_t usThingNameLength = 0U;
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
        LogInfo( ( "pPublishInfo->pTopicName:%s.", pxDeserializedInfo->pPublishInfo->pTopicName ) );

        /* Let the Device Shadow library tell us whether this is a device shadow message. */
        if( SHADOW_SUCCESS == Shadow_MatchTopic( pxDeserializedInfo->pPublishInfo->pTopicName,
                                                 pxDeserializedInfo->pPublishInfo->topicNameLength,
                                                 &messageType,
                                                 &pcThingName,
                                                 &usThingNameLength ) )
        {
            /* Upon successful return, the messageType has been filled in. */
            if( messageType == ShadowMessageTypeUpdateDelta )
            {
                /* Handler function to process payload. */
                prvUpdateDeltaHandler( pxDeserializedInfo->pPublishInfo );
            }
            else if( messageType == ShadowMessageTypeUpdateAccepted )
            {
                /* Handler function to process payload. */
                prvUpdateAcceptedHandler( pxDeserializedInfo->pPublishInfo );
            }
            else if( messageType == ShadowMessageTypeUpdateDocuments )
            {
                LogInfo( ( "/update/documents json payload:%s.", ( const char * ) pxDeserializedInfo->pPublishInfo->pPayload ) );
            }
            else if( messageType == ShadowMessageTypeUpdateRejected )
            {
                LogInfo( ( "/update/rejected json payload:%s.", ( const char * ) pxDeserializedInfo->pPublishInfo->pPayload ) );
            }
            else if( messageType == ShadowMessageTypeDeleteAccepted )
            {
                LogInfo( ( "Received an MQTT incoming publish on /delete/accepted topic." ) );
                xShadowDeleted = pdTRUE;
                xDeleteResponseReceived = pdTRUE;
            }
            else if( messageType == ShadowMessageTypeDeleteRejected )
            {
                /* Handler function to process payload. */
                prvDeleteRejectedHandler( pxDeserializedInfo->pPublishInfo );
                xDeleteResponseReceived = pdTRUE;
            }
            else
            {
                LogInfo( ( "Other message type:%d !!", messageType ) );
            }
        }
        else
        {
            LogError( ( "Shadow_MatchTopic parse failed:%s !!", ( const char * ) pxDeserializedInfo->pPublishInfo->pTopicName ) );
        }
    }
    else
    {
        vHandleOtherIncomingPacket( pxPacketInfo, usPacketIdentifier );
    }
}
/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the Device Shadow library API via a
 * MQTT mutually authenticated network connection with the AWS IoT broker.
 */
void vStartShadowDemo( void )
{
    /* This example uses a single application task, which shows that how to
     * use Device Shadow library to generate and validate AWS IoT Device Shadow
     * MQTT topics, and use the coreMQTT library to communicate with the AWS IoT
     * Device Shadow service. */
    xTaskCreate( prvShadowDemoTask,        /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

/**
 * @brief Entry point of shadow demo.
 *
 * This main function demonstrates how to use the macros provided by the
 * Device Shadow library to assemble strings for the MQTT topics defined
 * by AWS IoT Device Shadow. It uses these macros for topics to subscribe
 * to:
 * - SHADOW_TOPIC_STRING_UPDATE_DELTA for "$aws/things/thingName/shadow/update/delta"
 * - SHADOW_TOPIC_STRING_UPDATE_ACCEPTED for "$aws/things/thingName/shadow/update/accepted"
 * - SHADOW_TOPIC_STRING_UPDATE_REJECTED for "$aws/things/thingName/shadow/update/rejected"
 *
 * It also uses these macros for topics to publish to:
 * - SHADOW_TOPIC_STIRNG_DELETE for "$aws/things/thingName/shadow/delete"
 * - SHADOW_TOPIC_STRING_UPDATE for "$aws/things/thingName/shadow/update"
 *
 * The helper functions this demo uses for MQTT operations have internal
 * loops to process incoming messages. Those are not the focus of this demo
 * and therefor, are placed in a separate file shadow_demo_helpers.c.
 */
void prvShadowDemoTask( void * pvParameters )
{
    BaseType_t xDemoStatus = pdPASS;
    UBaseType_t uxDemoRunCount = 0UL;

    /* A buffer containing the update document. It has static duration to prevent
     * it from being placed on the call stack. */
    static char pcUpdateDocument[ SHADOW_REPORTED_JSON_LENGTH + 1 ] = { 0 };

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pParams = &xTlsTransportParams;

    /****************************** Connect. ******************************/

    /* This demo runs a single loop unless there are failures in the demo execution.
     * In case of failures in the demo execution, demo loop will be retried for up to
     * SHADOW_MAX_DEMO_LOOP_COUNT times. */
    do
    {
        /****************************** Connect. ******************************/

        xDemoStatus = xEstablishMqttSession( &xMqttContext,
                                             &xNetworkContext,
                                             &xBuffer,
                                             prvEventCallback );

        if( xDemoStatus == pdFAIL )
        {
            /* Log error to indicate connection failure. */
            LogError( ( "Failed to connect to MQTT broker." ) );
        }

        /**************** Attempt to delete Shadow document. ******************/

        if( xDemoStatus == pdPASS )
        {
            /* Reset the shadow delete status flags. */
            xDeleteResponseReceived = pdFALSE;
            xShadowDeleted = pdFALSE;

            /* First of all, try to delete any Shadow document in the cloud.
             * Try to subscribe to `/delete/accepted` and `/delete/rejected` topics. */
            xDemoStatus = xSubscribeToTopic( &xMqttContext,
                                             SHADOW_TOPIC_STRING_DELETE_ACCEPTED( democonfigTHING_NAME ),
                                             SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED( THING_NAME_LENGTH ) );
        }

        if( xDemoStatus == pdPASS )
        {
            /* Try to subscribe to `/delete/rejected` topic. */
            xDemoStatus = xSubscribeToTopic( &xMqttContext,
                                             SHADOW_TOPIC_STRING_DELETE_REJECTED( democonfigTHING_NAME ),
                                             SHADOW_TOPIC_LENGTH_DELETE_REJECTED( THING_NAME_LENGTH ) );
        }

        if( xDemoStatus == pdPASS )
        {
            /* Publish to Shadow `delete` topic to attempt to delete the
             * Shadow document if exists. */
            xDemoStatus = xPublishToTopic( &xMqttContext,
                                           SHADOW_TOPIC_STRING_DELETE( democonfigTHING_NAME ),
                                           SHADOW_TOPIC_LENGTH_DELETE( THING_NAME_LENGTH ),
                                           pcUpdateDocument,
                                           0U );
        }

        /* Wait for an incoming publish on `/delete/accepted` or `/delete/rejected`
         * topics, if not already received a publish. */
        if( ( xDemoStatus == pdPASS ) && ( xDeleteResponseReceived != pdTRUE ) )
        {
            xDemoStatus = prvWaitForDeleteResponse( &xMqttContext );
        }

        /* Unsubscribe from the `/delete/accepted` and 'delete/rejected` topics.*/
        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = xUnsubscribeFromTopic( &xMqttContext,
                                                 SHADOW_TOPIC_STRING_DELETE_ACCEPTED( democonfigTHING_NAME ),
                                                 SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED( THING_NAME_LENGTH ) );
        }

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = xUnsubscribeFromTopic( &xMqttContext,
                                                 SHADOW_TOPIC_STRING_DELETE_REJECTED( democonfigTHING_NAME ),
                                                 SHADOW_TOPIC_LENGTH_DELETE_REJECTED( THING_NAME_LENGTH ) );
        }

        /* Check if Shadow document delete was successful. A delete can be
         * successful in cases listed below.
         *  1. If an incoming publish is received on `/delete/accepted` topic.
         *  2. If an incoming publish is received on `/delete/rejected` topic
         *     with error code 404. This indicates that a Shadow document was
         *     not present for the Thing. */
        if( xShadowDeleted == pdFALSE )
        {
            LogError( ( "Shadow delete operation failed." ) );
            xDemoStatus = pdFAIL;
        }

        /********************* Subscribe to Shadow topics. ************************/

        /* Then try to subscribe the Shadow topics. */

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = xSubscribeToTopic( &xMqttContext,
                                             SHADOW_TOPIC_STRING_UPDATE_DELTA( democonfigTHING_NAME ),
                                             SHADOW_TOPIC_LENGTH_UPDATE_DELTA( THING_NAME_LENGTH ) );
        }

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = xSubscribeToTopic( &xMqttContext,
                                             SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( democonfigTHING_NAME ),
                                             SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( THING_NAME_LENGTH ) );
        }

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = xSubscribeToTopic( &xMqttContext,
                                             SHADOW_TOPIC_STRING_UPDATE_REJECTED( democonfigTHING_NAME ),
                                             SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( THING_NAME_LENGTH ) );
        }

        /********************* Publish to Shadow topics. **********************/

        /* This demo uses a constant #democonfigTHING_NAME known at compile time
         * therefore we can use macros to assemble shadow topic strings.
         * If the thing name is known at run time, then we could use the API
         * #Shadow_GetTopicString to assemble shadow topic strings, here is the
         * example for /update/delta:
         *
         * For /update/delta:
         *
         * #define SHADOW_TOPIC_MAX_LENGTH  (256U)
         *
         * ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;
         * char cTopicBuffer[ SHADOW_TOPIC_MAX_LENGTH ] = { 0 };
         * uint16_t usBufferSize = SHADOW_TOPIC_MAX_LENGTH;
         * uint16_t usOutLength = 0;
         * const char * pcThingName = "TestThingName";
         * uint16_t usThingNameLength  = ( sizeof( pcThingName ) - 1U );
         *
         * shadowStatus = Shadow_GetTopicString( SHADOW_TOPIC_STRING_TYPE_UPDATE_DELTA,
         *                                       pcThingName,
         *                                       usThingNameLength,
         *                                       & ( cTopicBuffer[ 0 ] ),
         *                                       usBufferSize,
         *                                       & usOutLength );
         */

        /* Then we publish a desired state to the /update topic. Since we've deleted
         * the device shadow at the beginning of the demo, this will cause a delta
         * message to be published, which we have subscribed to.
         * In many real applications, the desired state is not published by
         * the device itself. But for the purpose of making this demo self-contained,
         * we publish one here so that we can receive a delta message later.
         */
        if( xDemoStatus == pdPASS )
        {
            /* Desired power on state . */
            LogInfo( ( "Send desired power state with 1." ) );

            ( void ) memset( pcUpdateDocument,
                             0x00,
                             sizeof( pcUpdateDocument ) );

            snprintf( pcUpdateDocument,
                      SHADOW_DESIRED_JSON_LENGTH + 1,
                      SHADOW_DESIRED_JSON,
                      ( int ) 1,
                      ( long unsigned ) ( xTaskGetTickCount() % 1000000 ) );

            xDemoStatus = xPublishToTopic( &xMqttContext,
                                           SHADOW_TOPIC_STRING_UPDATE( democonfigTHING_NAME ),
                                           SHADOW_TOPIC_LENGTH_UPDATE( THING_NAME_LENGTH ),
                                           pcUpdateDocument,
                                           ( SHADOW_DESIRED_JSON_LENGTH + 1 ) );
        }

        if( xDemoStatus == pdPASS )
        {
            /* Note that PublishToTopic already called MQTT_ProcessLoop,
             * therefore responses may have been received and the prvEventCallback
             * may have been called, which may have changed the stateChanged flag.
             * Check if the state change flag has been modified or not. If it's modified,
             * then we publish reported state to update topic.
             */
            if( stateChanged == true )
            {
                /* Report the latest power state back to device shadow. */
                LogInfo( ( "Report to the state change: %d", ulCurrentPowerOnState ) );
                ( void ) memset( pcUpdateDocument,
                                 0x00,
                                 sizeof( pcUpdateDocument ) );

                /* Keep the client token in global variable used to compare if
                 * the same token in /update/accepted. */
                ulClientToken = ( xTaskGetTickCount() % 1000000 );

                snprintf( pcUpdateDocument,
                          SHADOW_REPORTED_JSON_LENGTH + 1,
                          SHADOW_REPORTED_JSON,
                          ( int ) ulCurrentPowerOnState,
                          ( long unsigned ) ulClientToken );

                xDemoStatus = xPublishToTopic( &xMqttContext,
                                               SHADOW_TOPIC_STRING_UPDATE( democonfigTHING_NAME ),
                                               SHADOW_TOPIC_LENGTH_UPDATE( THING_NAME_LENGTH ),
                                               pcUpdateDocument,
                                               ( SHADOW_DESIRED_JSON_LENGTH + 1 ) );
            }
            else
            {
                LogInfo( ( "No change from /update/delta, unsubscribe all shadow topics and disconnect from MQTT.\r\n" ) );
            }
        }

        /****************** Unsubscribe from Shadow topics. *******************/

        if( xDemoStatus == pdPASS )
        {
            LogInfo( ( "Start to unsubscribe shadow topics and disconnect from MQTT. \r\n" ) );

            xDemoStatus = xUnsubscribeFromTopic( &xMqttContext,
                                                 SHADOW_TOPIC_STRING_UPDATE_DELTA( democonfigTHING_NAME ),
                                                 SHADOW_TOPIC_LENGTH_UPDATE_DELTA( THING_NAME_LENGTH ) );

            if( xDemoStatus != pdPASS )
            {
                LogError( ( "Failed to unsubscribe the topic %s",
                            SHADOW_TOPIC_STRING_UPDATE_DELTA( democonfigTHING_NAME ) ) );
            }
        }

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = xUnsubscribeFromTopic( &xMqttContext,
                                                 SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( democonfigTHING_NAME ),
                                                 SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( THING_NAME_LENGTH ) );

            if( xDemoStatus != pdPASS )
            {
                LogError( ( "Failed to unsubscribe the topic %s",
                            SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( democonfigTHING_NAME ) ) );
            }
        }

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = xUnsubscribeFromTopic( &xMqttContext,
                                                 SHADOW_TOPIC_STRING_UPDATE_REJECTED( democonfigTHING_NAME ),
                                                 SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( THING_NAME_LENGTH ) );

            if( xDemoStatus != pdPASS )
            {
                LogError( ( "Failed to unsubscribe the topic %s",
                            SHADOW_TOPIC_STRING_UPDATE_REJECTED( democonfigTHING_NAME ) ) );
            }
        }

        /****************************** Disconnect. *******************************/

        /* The MQTT session is always disconnected, even if there were prior failures. */
        xDemoStatus = xDisconnectMqttSession( &xMqttContext, &xNetworkContext );

        /* This demo performs only Device Shadow operations. If matching the Shadow
         * MQTT topic fails or there are failure in parsing the received JSON document,
         * then this demo was not successful. */
        if( ( xUpdateAcceptedReturn != pdPASS ) || ( xUpdateDeltaReturn != pdPASS ) )
        {
            LogError( ( "Callback function failed." ) );
        }

        /*********************** Retry in case of failure. ************************/

        /* Increment the demo run count. */
        uxDemoRunCount++;

        if( xDemoStatus == pdPASS )
        {
            LogInfo( ( "Demo iteration %lu is successful.", uxDemoRunCount ) );
        }
        /* Attempt to retry a failed iteration of demo for up to #SHADOW_MAX_DEMO_LOOP_COUNT times. */
        else if( uxDemoRunCount < SHADOW_MAX_DEMO_LOOP_COUNT )
        {
            LogWarn( ( "Demo iteration %lu failed. Retrying...", uxDemoRunCount ) );
            vTaskDelay( DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_TICKS );
        }
        /* Failed all #SHADOW_MAX_DEMO_LOOP_COUNT demo iterations. */
        else
        {
            LogError( ( "All %d demo iterations failed.", SHADOW_MAX_DEMO_LOOP_COUNT ) );
            break;
        }
    } while( xDemoStatus != pdPASS );

    if( xDemoStatus == pdPASS )
    {
        LogInfo( ( "Demo completed successfully." ) );
    }
    else
    {
        LogError( ( "Shadow Demo failed." ) );
    }

    /* Delete this task. */
    LogInfo( ( "Deleting Shadow Demo task." ) );
    vTaskDelete( NULL );
}
