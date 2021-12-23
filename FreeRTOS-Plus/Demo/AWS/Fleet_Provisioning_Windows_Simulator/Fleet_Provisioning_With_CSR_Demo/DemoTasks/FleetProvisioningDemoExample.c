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

/*
 * Demo for showing use of the Fleet Provisioning library to use the Fleet
 * Provisioning feature of AWS IoT Core for provisioning devices with
 * credentials. This demo shows how a device can be provisioned with AWS IoT
 * Core using the Certificate Signing Request workflow of the Fleet
 * Provisioning feature.
 *
 * The Fleet Provisioning library provides macros and helper functions for
 * assembling MQTT topics strings, and for determining whether an incoming MQTT
 * message is related to the Fleet Provisioning API of AWS IoT Core. The Fleet
 * Provisioning library does not depend on any particular MQTT library,
 * therefore the functionality for MQTT operations is placed in another file
 * (mqtt_operations.c). This demo uses the coreMQTT library. If needed,
 * mqtt_operations.c can be modified to replace coreMQTT with another MQTT
 * library. This demo requires using the AWS IoT Core broker as Fleet
 * Provisioning is an AWS IoT Core feature.
 *
 * This demo provisions a device certificate using the provisioning by claim
 * workflow with a Certificate Signing Request (CSR). The demo connects to AWS
 * IoT Core using provided claim credentials (whose certificate needs to be
 * registered with IoT Core before running this demo), subscribes to the
 * CreateCertificateFromCsr topics, and obtains a certificate. It then
 * subscribes to the RegisterThing topics and activates the certificate and
 * obtains a Thing using the provisioning template. Finally, it reconnects to
 * AWS IoT Core using the new credentials.
 */

/* Standard includes. */
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo Config */
#include "demo_config.h"

/* mbedTLS include for configuring threading functions */
#include "mbedtls/threading.h"
#include "threading_alt.h"

/* TinyCBOR library for CBOR encoding and decoding operations. */
#include "cbor.h"

/* corePKCS11 includes. */
#include "core_pkcs11.h"
#include "core_pkcs11_config.h"

/* AWS IoT Fleet Provisioning Library. */
#include "fleet_provisioning.h"

/* Demo includes. */
#include "mqtt_operations.h"
#include "pkcs11_operations.h"
#include "tinycbor_serializer.h"
#include "using_mbedtls_pkcs11.h"

/**
 * These configurations are required. Throw compilation error if it is not
 * defined.
 */
#ifndef democonfigPROVISIONING_TEMPLATE_NAME
    #error "Please define democonfigPROVISIONING_TEMPLATE_NAME to the template name registered with AWS IoT Core in demo_config.h."
#endif
#ifndef democonfigROOT_CA_PEM
    #error "Please define Root CA certificate of the MQTT broker(democonfigROOT_CA_PEM) in demo_config.h."
#endif

/**
 * @brief The length of #democonfigPROVISIONING_TEMPLATE_NAME.
 */
#define fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH    ( ( uint16_t ) ( sizeof( democonfigPROVISIONING_TEMPLATE_NAME ) - 1 ) )

/**
 * @brief The length of #democonfigFP_DEMO_ID.
 */
#define fpdemoFP_DEMO_ID_LENGTH                    ( ( uint16_t ) ( sizeof( democonfigFP_DEMO_ID ) - 1 ) )

/**
 * @brief Size of AWS IoT Thing name buffer.
 *
 * See https://docs.aws.amazon.com/iot/latest/apireference/API_CreateThing.html#iot-CreateThing-request-thingName
 */
#define fpdemoMAX_THING_NAME_LENGTH                128

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef fpdemoMAX_DEMO_LOOP_COUNT
    #define fpdemoMAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in seconds to wait between retries of the demo loop if
 * demo loop fails.
 */
#define fpdemoDELAY_BETWEEN_DEMO_RETRY_ITERATIONS_SECONDS    ( 5 )

/**
 * @brief Size of buffer in which to hold the certificate signing request (CSR).
 */
#define fpdemoCSR_BUFFER_LENGTH                              2048

/**
 * @brief Size of buffer in which to hold the certificate.
 */
#define fpdemoCERT_BUFFER_LENGTH                             2048

/**
 * @brief Size of buffer in which to hold the certificate id.
 *
 * See https://docs.aws.amazon.com/iot/latest/apireference/API_Certificate.html#iot-Type-Certificate-certificateId
 */
#define fpdemoCERT_ID_BUFFER_LENGTH                          64

/**
 * @brief Size of buffer in which to hold the certificate ownership token.
 */
#define fpdemoOWNERSHIP_TOKEN_BUFFER_LENGTH                  512

/**
 * @brief Milliseconds per second.
 */
#define fpdemoMILLISECONDS_PER_SECOND                        ( 1000U )

/**
 * @brief Milliseconds per FreeRTOS tick.
 */
#define fpdemoMILLISECONDS_PER_TICK                          ( fpdemoMILLISECONDS_PER_SECOND / configTICK_RATE_HZ )

/**
 * @brief Status values of the Fleet Provisioning response.
 */
typedef enum
{
    ResponseNotReceived,
    ResponseAccepted,
    ResponseRejected
} ResponseStatus_t;

/*-----------------------------------------------------------*/

/**
 * @brief Status reported from the MQTT publish callback.
 */
static ResponseStatus_t xResponseStatus;

/**
 * @brief Buffer to hold the provisioned AWS IoT Thing name.
 */
static char pcThingName[ fpdemoMAX_THING_NAME_LENGTH ];

/**
 * @brief Length of the AWS IoT Thing name.
 */
static size_t xThingNameLength;

/**
 * @brief Buffer to hold responses received from the AWS IoT Fleet Provisioning
 * APIs. When the MQTT publish callback receives an expected Fleet Provisioning
 * accepted payload, it copies it into this buffer.
 */
static uint8_t pucPayloadBuffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief Length of the payload stored in #pucPayloadBuffer. This is set by the
 * MQTT publish callback when it copies a received payload into #pucPayloadBuffer.
 */
static size_t xPayloadLength;

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
    TlsTransportParams_t * pxParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief Callback to receive the incoming publish messages from the MQTT
 * broker. Sets xResponseStatus if an expected CreateCertificateFromCsr or
 * RegisterThing response is received, and copies the response into
 * responseBuffer if the response is an accepted one.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] usPacketIdentifier Packet identifier of the incoming publish.
 */
static void prvProvisioningPublishCallback( MQTTPublishInfo_t * pPublishInfo,
                                            uint16_t usPacketIdentifier );

/**
 * @brief Run the MQTT process loop to get a response.
 */
static bool prvWaitForResponse( void );

/**
 * @brief Subscribe to the CreateCertificateFromCsr accepted and rejected topics.
 */
static bool prvSubscribeToCsrResponseTopics( void );

/**
 * @brief Unsubscribe from the CreateCertificateFromCsr accepted and rejected topics.
 */
static bool prvUnsubscribeFromCsrResponseTopics( void );

/**
 * @brief Subscribe to the RegisterThing accepted and rejected topics.
 */
static bool prvSubscribeToRegisterThingResponseTopics( void );

/**
 * @brief Unsubscribe from the RegisterThing accepted and rejected topics.
 */
static bool prvUnsubscribeFromRegisterThingResponseTopics( void );

/**
 * @brief The task used to demonstrate the FP API.
 *
 * This task uses the provided claim key and certificate files to connect to
 * AWS and use PKCS #11 to generate a new device key and certificate with a CSR.
 * The task then creates a new Thing with the Fleet Provisioning API using the
 * newly-created credentials. The task finishes by connecting to the newly-created
 * Thing to verify that it was successfully created and accessible using the key/cert.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation.
 * Not used in this example.
 */
static int prvFleetProvisioningTask( void * pvParameters );


/*-----------------------------------------------------------*/

static void prvProvisioningPublishCallback( MQTTPublishInfo_t * pPublishInfo,
                                            uint16_t usPacketIdentifier )
{
    FleetProvisioningStatus_t status;
    FleetProvisioningTopic_t api;

    /* Silence compiler warnings about unused variables. */
    ( void ) usPacketIdentifier;

    status = FleetProvisioning_MatchTopic( pPublishInfo->pTopicName,
                                           pPublishInfo->topicNameLength, &api );

    if( status != FleetProvisioningSuccess )
    {
        LogWarn( ( "Unexpected publish message received. Topic: %.*s.",
                   ( int ) pPublishInfo->topicNameLength,
                   ( const char * ) pPublishInfo->pTopicName ) );
    }
    else
    {
        if( api == FleetProvCborCreateCertFromCsrAccepted )
        {
            LogInfo( ( "Received accepted response from Fleet Provisioning CreateCertificateFromCsr API." ) );

            xResponseStatus = ResponseAccepted;

            /* Copy the payload from the MQTT library's buffer to #pucPayloadBuffer. */
            ( void ) memcpy( ( void * ) pucPayloadBuffer,
                             ( const void * ) pPublishInfo->pPayload,
                             ( size_t ) pPublishInfo->payloadLength );

            xPayloadLength = pPublishInfo->payloadLength;
        }
        else if( api == FleetProvCborCreateCertFromCsrRejected )
        {
            LogError( ( "Received rejected response from Fleet Provisioning CreateCertificateFromCsr API." ) );

            xResponseStatus = ResponseRejected;
        }
        else if( api == FleetProvCborRegisterThingAccepted )
        {
            LogInfo( ( "Received accepted response from Fleet Provisioning RegisterThing API." ) );

            xResponseStatus = ResponseAccepted;

            /* Copy the payload from the MQTT library's buffer to #pucPayloadBuffer. */
            ( void ) memcpy( ( void * ) pucPayloadBuffer,
                             ( const void * ) pPublishInfo->pPayload,
                             ( size_t ) pPublishInfo->payloadLength );

            xPayloadLength = pPublishInfo->payloadLength;
        }
        else if( api == FleetProvCborRegisterThingRejected )
        {
            LogError( ( "Received rejected response from Fleet Provisioning RegisterThing API." ) );

            xResponseStatus = ResponseRejected;
        }
        else
        {
            LogError( ( "Received message on unexpected Fleet Provisioning topic. Topic: %.*s.",
                        ( int ) pPublishInfo->topicNameLength,
                        ( const char * ) pPublishInfo->pTopicName ) );
        }
    }
}
/*-----------------------------------------------------------*/

static bool prvWaitForResponse( void )
{
    bool xStatus = false;

    xResponseStatus = ResponseNotReceived;

    /* xResponseStatus is updated from the MQTT publish callback. */
    ( void ) xProcessLoop();

    if( xResponseStatus == ResponseNotReceived )
    {
        LogError( ( "Timed out waiting for response." ) );
    }

    if( xResponseStatus == ResponseAccepted )
    {
        xStatus = true;
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvSubscribeToCsrResponseTopics( void )
{
    bool xStatus;

    xStatus = xSubscribeToTopic( FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC,
                                 FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH );

    if( xStatus == false )
    {
        LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                    FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH,
                    FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC ) );
    }

    if( xStatus == true )
    {
        xStatus = xSubscribeToTopic( FP_CBOR_CREATE_CERT_REJECTED_TOPIC,
                                     FP_CBOR_CREATE_CERT_REJECTED_LENGTH );

        if( xStatus == false )
        {
            LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                        FP_CBOR_CREATE_CERT_REJECTED_LENGTH,
                        FP_CBOR_CREATE_CERT_REJECTED_TOPIC ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvUnsubscribeFromCsrResponseTopics( void )
{
    bool xStatus;

    xStatus = xUnsubscribeFromTopic( FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC,
                                     FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH );

    if( xStatus == false )
    {
        LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                    FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH,
                    FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC ) );
    }

    if( xStatus == true )
    {
        xStatus = xUnsubscribeFromTopic( FP_CBOR_CREATE_CERT_REJECTED_TOPIC,
                                         FP_CBOR_CREATE_CERT_REJECTED_LENGTH );

        if( xStatus == false )
        {
            LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                        FP_CBOR_CREATE_CERT_REJECTED_LENGTH,
                        FP_CBOR_CREATE_CERT_REJECTED_TOPIC ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvSubscribeToRegisterThingResponseTopics( void )
{
    bool xStatus;

    xStatus = xSubscribeToTopic( FP_CBOR_REGISTER_ACCEPTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ),
                                 FP_CBOR_REGISTER_ACCEPTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ) );

    if( xStatus == false )
    {
        LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                    FP_CBOR_REGISTER_ACCEPTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ),
                    FP_CBOR_REGISTER_ACCEPTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ) ) );
    }

    if( xStatus == true )
    {
        xStatus = xSubscribeToTopic( FP_CBOR_REGISTER_REJECTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ),
                                     FP_CBOR_REGISTER_REJECTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ) );

        if( xStatus == false )
        {
            LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                        FP_CBOR_REGISTER_REJECTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ),
                        FP_CBOR_REGISTER_REJECTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ) ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

static bool prvUnsubscribeFromRegisterThingResponseTopics( void )
{
    bool xStatus;

    xStatus = xUnsubscribeFromTopic( FP_CBOR_REGISTER_ACCEPTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ),
                                     FP_CBOR_REGISTER_ACCEPTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ) );

    if( xStatus == false )
    {
        LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                    FP_CBOR_REGISTER_ACCEPTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ),
                    FP_CBOR_REGISTER_ACCEPTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ) ) );
    }

    if( xStatus == true )
    {
        xStatus = xUnsubscribeFromTopic( FP_CBOR_REGISTER_REJECTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ),
                                         FP_CBOR_REGISTER_REJECTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ) );

        if( xStatus == false )
        {
            LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                        FP_CBOR_REGISTER_REJECTED_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ),
                        FP_CBOR_REGISTER_REJECTED_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ) ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

/**
 * @brief Create the task that demonstrates the Fleet Provisioning library API
 */
void vStartFleetProvisioningDemo()
{
    /* Configure mbedTLS to use FreeRTOS specific threading function. */
    mbedtls_threading_set_alt( mbedtls_platform_mutex_init,
                               mbedtls_platform_mutex_free,
                               mbedtls_platform_mutex_lock,
                               mbedtls_platform_mutex_unlock );

    /* This example uses a single application task, which shows that how to use
     * Device Defender library to generate and validate AWS IoT Device Defender
     * MQTT topics, and use the coreMQTT library to communicate with the AWS
     * IoT Device Defender service. */
    xTaskCreate( prvFleetProvisioningTask, /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}

/* This example uses a single application task, which shows that how to use
 * the Fleet Provisioning library to generate and validate AWS IoT Fleet
 * Provisioning MQTT topics, and use the coreMQTT library to communicate with
 * the AWS IoT Fleet Provisioning APIs. */
int prvFleetProvisioningTask( void * pvParameters )
{
    bool xStatus = false;
    /* Buffer for holding the CSR. */
    char pcCsr[ fpdemoCSR_BUFFER_LENGTH ] = { 0 };
    size_t xCsrLength = 0;
    /* Buffer for holding received certificate until it is saved. */
    char pcCertificate[ fpdemoCERT_BUFFER_LENGTH ];
    size_t xCertificateLength;
    /* Buffer for holding the certificate ID. */
    char pcCertificateId[ fpdemoCERT_ID_BUFFER_LENGTH ];
    size_t xCertificateIdLength;
    /* Buffer for holding the certificate ownership token. */
    char pcOwnershipToken[ fpdemoOWNERSHIP_TOKEN_BUFFER_LENGTH ];
    size_t xOwnershipTokenLength;
    bool xConnectionEstablished = false;
    CK_SESSION_HANDLE xP11Session;
    uint32_t ulDemoRunCount = 0U;
    CK_RV xPkcs11Ret = CKR_OK;


    NetworkContext_t xNetworkContext = { 0 };
    TlsTransportParams_t xTlsTransportParams = { 0 };

    /* Silence compiler warnings about unused variables. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pxParams = &xTlsTransportParams;

    do
    {
        /* Initialize the buffer lengths to their max lengths. */
        xCertificateLength = fpdemoCERT_BUFFER_LENGTH;
        xCertificateIdLength = fpdemoCERT_ID_BUFFER_LENGTH;
        xOwnershipTokenLength = fpdemoOWNERSHIP_TOKEN_BUFFER_LENGTH;

        /* Initialize the PKCS #11 module */
        xPkcs11Ret = xInitializePkcs11Session( &xP11Session );

        if( xPkcs11Ret != CKR_OK )
        {
            LogError( ( "Failed to initialize PKCS #11." ) );
            xStatus = false;
        }
        else
        {
            xStatus = xGenerateKeyAndCsr( xP11Session,
                                          pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
                                          pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS,
                                          pcCsr,
                                          fpdemoCSR_BUFFER_LENGTH,
                                          &xCsrLength );

            if( xStatus == false )
            {
                LogError( ( "Failed to generate Key and Certificate Signing Request." ) );
            }

            xPkcs11CloseSession( xP11Session );
        }

        /**** Connect to AWS IoT Core with provisioning claim credentials *****/

        /* We first use the claim credentials to connect to the broker. These
         * credentials should allow use of the RegisterThing API and one of the
         * CreateCertificatefromCsr or CreateKeysAndCertificate.
         * In this demo we use CreateCertificatefromCsr. */
        if( xStatus == true )
        {
            /* Attempts to connect to the AWS IoT MQTT broker. If the
             * connection fails, retries after a timeout. Timeout value will
             * exponentially increase until maximum attempts are reached. */
            LogInfo( ( "Establishing MQTT session with claim certificate..." ) );
            xStatus = xEstablishMqttSession( prvProvisioningPublishCallback,
                                             pkcs11configLABEL_CLAIM_CERTIFICATE,
                                             pkcs11configLABEL_CLAIM_PRIVATE_KEY );

            if( xStatus == false )
            {
                LogError( ( "Failed to establish MQTT session." ) );
            }
            else
            {
                LogInfo( ( "Established connection with claim credentials." ) );
                xConnectionEstablished = true;
            }
        }

        /**** Call the CreateCertificateFromCsr API ***************************/

        /* We use the CreateCertificatefromCsr API to obtain a client certificate
         * for a key on the device by means of sending a certificate signing
         * request (CSR). */
        if( xStatus == true )
        {
            /* Subscribe to the CreateCertificateFromCsr accepted and rejected
             * topics. In this demo we use CBOR encoding for the payloads,
             * so we use the CBOR variants of the topics. */
            xStatus = prvSubscribeToCsrResponseTopics();
        }

        if( xStatus == true )
        {
            /* Create the request payload containing the CSR to publish to the
             * CreateCertificateFromCsr APIs. */
            xStatus = xGenerateCsrRequest( pucPayloadBuffer,
                                           democonfigNETWORK_BUFFER_SIZE,
                                           pcCsr,
                                           xCsrLength,
                                           &xPayloadLength );
        }

        if( xStatus == true )
        {
            /* Publish the CSR to the CreateCertificatefromCsr API. */
            xPublishToTopic( FP_CBOR_CREATE_CERT_PUBLISH_TOPIC,
                             FP_CBOR_CREATE_CERT_PUBLISH_LENGTH,
                             ( char * ) pucPayloadBuffer,
                             xPayloadLength );

            if( xStatus == false )
            {
                LogError( ( "Failed to publish to fleet provisioning topic: %.*s.",
                            FP_CBOR_CREATE_CERT_PUBLISH_LENGTH,
                            FP_CBOR_CREATE_CERT_PUBLISH_TOPIC ) );
            }
        }

        if( xStatus == true )
        {
            /* Get the response to the CreateCertificatefromCsr request. */
            xStatus = prvWaitForResponse();
        }

        if( xStatus == true )
        {
            /* From the response, extract the certificate, certificate ID, and
             * certificate ownership token. */
            xStatus = xParseCsrResponse( pucPayloadBuffer,
                                         xPayloadLength,
                                         pcCertificate,
                                         &xCertificateLength,
                                         pcCertificateId,
                                         &xCertificateIdLength,
                                         pcOwnershipToken,
                                         &xOwnershipTokenLength );

            if( xStatus == true )
            {
                LogInfo( ( "Received certificate with Id: %.*s", ( int ) xCertificateIdLength, pcCertificateId ) );
            }
        }

        if( xStatus == true )
        {
            /* Save the certificate into PKCS #11. */
            xStatus = xLoadCertificate( xP11Session,
                                        pcCertificate,
                                        pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                                        xCertificateLength );
        }

        if( xStatus == true )
        {
            /* Unsubscribe from the CreateCertificateFromCsr topics. */
            xStatus = prvUnsubscribeFromCsrResponseTopics();
        }

        /**** Call the RegisterThing API **************************************/

        /* We then use the RegisterThing API to activate the received certificate,
         * provision AWS IoT resources according to the provisioning template, and
         * receive device configuration. */
        if( xStatus == true )
        {
            /* Create the request payload to publish to the RegisterThing API. */
            xStatus = xGenerateRegisterThingRequest( pucPayloadBuffer,
                                                     democonfigNETWORK_BUFFER_SIZE,
                                                     pcOwnershipToken,
                                                     xOwnershipTokenLength,
                                                     democonfigFP_DEMO_ID,
                                                     fpdemoFP_DEMO_ID_LENGTH,
                                                     &xPayloadLength );
        }

        if( xStatus == true )
        {
            /* Subscribe to the RegisterThing response topics. */
            xStatus = prvSubscribeToRegisterThingResponseTopics();
        }

        if( xStatus == true )
        {
            /* Publish the RegisterThing request. */
            xPublishToTopic( FP_CBOR_REGISTER_PUBLISH_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ),
                             FP_CBOR_REGISTER_PUBLISH_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ),
                             ( char * ) pucPayloadBuffer,
                             xPayloadLength );

            if( xStatus == false )
            {
                LogError( ( "Failed to publish to fleet provisioning topic: %.*s.",
                            FP_CBOR_REGISTER_PUBLISH_LENGTH( fpdemoPROVISIONING_TEMPLATE_NAME_LENGTH ),
                            FP_CBOR_REGISTER_PUBLISH_TOPIC( democonfigPROVISIONING_TEMPLATE_NAME ) ) );
            }
        }

        if( xStatus == true )
        {
            /* Get the response to the RegisterThing request. */
            xStatus = prvWaitForResponse();
        }

        if( xStatus == true )
        {
            /* Extract the Thing name from the response. */
            xThingNameLength = fpdemoMAX_THING_NAME_LENGTH;
            xStatus = xParseRegisterThingResponse( pucPayloadBuffer,
                                                   xPayloadLength,
                                                   pcThingName,
                                                   &xThingNameLength );

            if( xStatus == true )
            {
                LogInfo( ( "Received AWS IoT Thing name: %.*s", ( int ) xThingNameLength, pcThingName ) );
            }
        }

        if( xStatus == true )
        {
            /* Unsubscribe from the RegisterThing topics. */
            prvUnsubscribeFromRegisterThingResponseTopics();
        }

        /**** Disconnect from AWS IoT Core ************************************/

        /* As we have completed the provisioning workflow, we disconnect from
         * the connection using the provisioning claim credentials. We will
         * establish a new MQTT connection with the newly provisioned
         * credentials. */
        if( xConnectionEstablished == true )
        {
            xDisconnectMqttSession();
            xConnectionEstablished = false;
        }

        /**** Connect to AWS IoT Core with provisioned certificate ************/

        if( xStatus == true )
        {
            LogInfo( ( "Establishing MQTT session with provisioned certificate..." ) );
            xStatus = xEstablishMqttSession( prvProvisioningPublishCallback,
                                             pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                                             pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS );

            if( xStatus != true )
            {
                LogError( ( "Failed to establish MQTT session with provisioned "
                            "credentials. Verify on your AWS account that the "
                            "new certificate is active and has an attached IoT "
                            "Policy that allows the \"iot:Connect\" action." ) );
            }
            else
            {
                LogInfo( ( "Sucessfully established connection with provisioned credentials." ) );
                xConnectionEstablished = true;
            }
        }

        /**** Finish **********************************************************/

        if( xConnectionEstablished == true )
        {
            /* Close the connection. */
            xDisconnectMqttSession();
            xConnectionEstablished = false;
        }

        /**** Retry in case of failure ****************************************/

        /* Increment the demo run count. */
        ulDemoRunCount++;

        if( xStatus == true )
        {
            LogInfo( ( "Demo iteration %d is successful.", ulDemoRunCount ) );
        }
        /* Attempt to retry a failed iteration of demo for up to #fpdemoMAX_DEMO_LOOP_COUNT times. */
        else if( ulDemoRunCount < fpdemoMAX_DEMO_LOOP_COUNT )
        {
            LogWarn( ( "Demo iteration %d failed. Retrying...", ulDemoRunCount ) );
            vTaskDelay( fpdemoDELAY_BETWEEN_DEMO_RETRY_ITERATIONS_SECONDS );
        }
        /* Failed all #fpdemoMAX_DEMO_LOOP_COUNT demo iterations. */
        else
        {
            LogError( ( "All %d demo iterations failed.", fpdemoMAX_DEMO_LOOP_COUNT ) );
            break;
        }
    } while( xStatus != true );

    /* Log demo success. */
    if( xStatus == true )
    {
        LogInfo( ( "Demo completed successfully." ) );
    }

    /* Delete this task. */
    LogInfo( ( "Deleting Fleet Provisioning Demo task." ) );
    vTaskDelete( NULL );

    return ( xStatus == true ) ? EXIT_SUCCESS : EXIT_FAILURE;
}
/*-----------------------------------------------------------*/
