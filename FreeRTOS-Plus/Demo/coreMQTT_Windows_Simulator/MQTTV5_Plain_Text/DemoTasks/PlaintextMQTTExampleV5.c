

/*
 * Demo for showing use of the MQTT V5 API.
 *
*/

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo Specific configs. */
#include "demo_config.h"
#include "core_mqtt_config.h"

/* MQTT library includes. */
#include "core_mqtt.h"

/* Exponential backoff retry include. */
#include "backoff_algorithm.h"

/* Transport interface implementation include header for plaintext connection. */
#include "transport_plaintext.h"


/*-----------------------------------------------------------*/

/* Compile time error for undefined configs. */
#ifndef democonfigMQTT_BROKER_ENDPOINT
    #error "Define the config democonfigMQTT_BROKER_ENDPOINT by following the instructions in file demo_config.h."
#endif
/*-----------------------------------------------------------*/

/* Default values for configs. */
#ifndef democonfigCLIENT_IDENTIFIER

/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.
 *
 * @note Appending __TIME__ to the client id string will help to create a unique
 * client id every time an application binary is built. Only a single instance of
 * this application's compiled binary may be used at a time, since the client ID
 * will always be the same.
 */
    #define democonfigCLIENT_IDENTIFIER    "testClient"__TIME__
#endif

#ifndef democonfigMQTT_BROKER_PORT

/**
 * @brief The port to use for the demo.
 */
    #define democonfigMQTT_BROKER_PORT    ( 8883 )
#endif

/*-----------------------------------------------------------*/

/**
 * @brief The maximum number of retries for network operation with server.
 */
#define mqttexampleRETRY_MAX_ATTEMPTS                     ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying failed operation
 *  with server.
 */
#define mqttexampleRETRY_MAX_BACKOFF_DELAY_MS             ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for network operation retry
 * attempts.
 */
#define mqttexampleRETRY_BACKOFF_BASE_MS                  ( 500U )

/**
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define mqttexampleCONNACK_RECV_TIMEOUT_MS                ( 100000U )

/**
 * @brief The prefix to the topic(s) subscribe(d) to and publish(ed) to in the example.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define mqttexampleTOPIC_PREFIX                           "test"

/**
 * @brief The number of topic filters to subscribe.
 */
#define mqttexampleTOPIC_COUNT                            ( 2 )

/**
 * @brief The size of the buffer for each topic string.
 */
#define mqttexampleTOPIC_BUFFER_SIZE                      ( 100U )

/**
 * @brief The MQTT message published in this example.
 */
#define mqttexampleMESSAGE                                "Hello World!"

/**
 * @brief Time in ticks to wait between each cycle of the demo implemented
 * by prvMQTTDemoTask().
 */
#define mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS_TICKS    ( pdMS_TO_TICKS( 5000U ) )

/**
 * @brief Timeout for MQTT_ProcessLoop in milliseconds.
 * Refer to FreeRTOS-Plus/Demo/coreMQTT_Windows_Simulator/readme.txt for more details.
 */
#define mqttexamplePROCESS_LOOP_TIMEOUT_MS                ( 2000U )

/**
 * @brief The keep-alive timeout period reported to the broker while establishing
 * an MQTT connection.
 *
 * It is the responsibility of the client to ensure that the interval between
 * control packets being sent does not exceed this keep-alive value. In the
 * absence of sending any other control packets, the client MUST send a
 * PINGREQ packet.
 */
#define mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS             ( 60U )

/**
 * @brief Delay (in ticks) between consecutive cycles of MQTT publish operations in a
 * demo iteration.
 *
 * Note that the process loop also has a timeout, so the total time between
 * publishes is the sum of the two delays.
 */
#define mqttexampleDELAY_BETWEEN_PUBLISHES_TICKS          ( pdMS_TO_TICKS( 2000U ) )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS         ( 200U )

/**
 * @brief The length of the outgoing publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for outgoing publishes.
 * Number of publishes = ulMaxPublishCount * mqttexampleTOPIC_COUNT
 * Update in ulMaxPublishCount needs updating mqttexampleOUTGOING_PUBLISH_RECORD_LEN.
 */
#define mqttexampleOUTGOING_PUBLISH_RECORD_LEN            ( 15U )

/**
 * @brief The length of the incoming publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for incoming publishes.
 * Number of publishes = ulMaxPublishCount * mqttexampleTOPIC_COUNT
 * Update in ulMaxPublishCount needs updating mqttexampleINCOMING_PUBLISH_RECORD_LEN.
 */
#define mqttexampleINCOMING_PUBLISH_RECORD_LEN            ( 15U )

/**
 * @brief Milliseconds per second.
 */
#define MILLISECONDS_PER_SECOND                           ( 1000U )

/**
 * @brief Milliseconds per FreeRTOS tick.
 */
#define MILLISECONDS_PER_TICK                             ( MILLISECONDS_PER_SECOND / configTICK_RATE_HZ )

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
    PlaintextTransportParams_t * pParams;
};

/*-----------------------------------------------------------*/
/**
 * @brief The task used to demonstrate the MQTT API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvMQTTDemoTask( void * pvParameters );

/**
 * @brief Connect to MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increase until the maximum
 * timeout value is reached or the number of attempts are exhausted.
 *
 * @param[out] pxNetworkContext The output parameter to return the created network context.
 *
 * @return The status of the final connection attempt.
 */
static PlaintextTransportStatus_t prvConnectToServerWithBackoffRetries( NetworkContext_t * pxNetworkContext );

/**
 * @brief Sends an MQTT Connect packet over the already connected TLS over TCP connection.
 *
 * @param[in, out] pxMQTTContext MQTT context pointer.
 * @param[in] xNetworkContext network context.
 */
static void prvCreateMQTTConnectionWithBroker(MQTTContext_t* pxMQTTContext,
    NetworkContext_t* pxNetworkContext, MQTTConnectProperties_t* pxProperties, MqttPropBuilder_t* ackPropsBuilder); 



/**
 * @brief Publishes a message mqttexampleMESSAGE on mqttexampleTOPIC topic.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 */
//static void prvMQTTPublishToTopics( MQTTContext_t * pxMQTTContext );



/**
 * @brief The timer query function provided to the MQTT context.
 *
 * @return Time in milliseconds.
 */
static uint32_t prvGetTimeMs( void );
static uint16_t usUnsubscribePacketIdentifier;
static uint16_t usPublishPacketIdentifier;


static void prvMQTTSubscribeToTopics(MQTTContext_t * pxMQTTContext) ; 

static void prvMQTTUnsubscribeFromTopics(MQTTContext_t* pxMQTTContext);

static void prvMQTTPublishToTopics(MQTTContext_t* pxMQTTContext);

/**
 * @brief The application callback function for getting the incoming publishes,
 * incoming acks, and ping responses reported from the MQTT library.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 * @param[in] pxPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pxDeserializedInfo Deserialized information from the incoming packet.
 */
static void prvEventCallback( MQTTContext_t * pxMQTTContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              MQTTDeserializedInfo_t * pxDeserializedInfo, 
                              MQTTPublishFailReasonCode_t * reasonCode);

/**
 * @brief Call #MQTT_ProcessLoop in a loop for the duration of a timeout or
 * #MQTT_ProcessLoop returns a failure.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] ulTimeoutMs Duration to call #MQTT_ProcessLoop for.
 *
 * @return Returns the return value of the last call to #MQTT_ProcessLoop.
 */
static MQTTStatus_t prvProcessLoopWithTimeout( MQTTContext_t * pMqttContext,
                                               uint32_t ulTimeoutMs );

/**
 * @brief Initialize the topic filter string and SUBACK buffers.
 */
static void prvInitializeTopicBuffers( void );

/**
 * @brief Process a response or ack to an MQTT request (PING, PUBLISH,
 * SUBSCRIBE or UNSUBSCRIBE). This function processes PINGRESP, PUBACK,
 * PUBREC, PUBREL, PUBCOMP, SUBACK, and UNSUBACK.
 *
 * @param[in] pxIncomingPacket is a pointer to structure containing deserialized
 * MQTT response.
 * @param[in] usPacketId is the packet identifier from the ack received.
 */
static void prvMQTTProcessResponse(MQTTPacketInfo_t* pxIncomingPacket,
    uint16_t usPacketId);

/**
 * @brief Function to update variable #Context with status
 * information from Subscribe ACK. Called by the event callback after processing
 * an incoming SUBACK packet.
 *
 * @param[in] Server response to the subscription request.
 */
static void prvUpdateSubAckStatus(MQTTPacketInfo_t* pxPacketInfo);


/*-----------------------------------------------------------*/

static uint8_t ucSharedBuffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief Global entry time into the application to use as a reference timestamp
 * in the #prvGetTimeMs function. #prvGetTimeMs will always return the difference
 * between the current time and the global entry time. This will reduce the chances
 * of overflow for the 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t ulGlobalEntryTimeMs;

/**
 * @brief Packet Identifier generated when Publish request was sent to the broker;
 * it is used to match received Publish ACK to the transmitted Publish packet.
 */
static uint16_t usSubscribePacketIdentifier;


/**
 * @brief A pair containing a topic filter and its SUBACK status.
 */
typedef struct topicFilterContext
{
    uint8_t pcTopicFilter[ mqttexampleTOPIC_BUFFER_SIZE ];
    MQTTSubAckStatus_t xSubAckStatus;
} topicFilterContext_t;

/**
 * @brief An array containing the context of a SUBACK; the SUBACK status
 * of a filter is updated when the event callback processes a SUBACK.
 */
static topicFilterContext_t xTopicFilterContext[ mqttexampleTOPIC_COUNT ];


/** @brief Static buffer used to hold MQTT messages being sent and received. */
static MQTTFixedBuffer_t xBuffer =
{
    ucSharedBuffer,
    democonfigNETWORK_BUFFER_SIZE
};

/**
 * @brief Array to track the outgoing publish records for outgoing publishes
 * with QoS > 0.
 *
 * This is passed into #MQTT_InitStatefulQoS to allow for QoS > 0.
 *
 */
static MQTTPubAckInfo_t pOutgoingPublishRecords[ mqttexampleOUTGOING_PUBLISH_RECORD_LEN ];

/**
 * @brief Array to track the incoming publish records for incoming publishes
 * with QoS > 0.
 *
 * This is passed into #MQTT_InitStatefulQoS to allow for QoS > 0.
 *
 */
static MQTTPubAckInfo_t pIncomingPublishRecords[ mqttexampleINCOMING_PUBLISH_RECORD_LEN ];

/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the MQTT API Demo over a
 * server-authenticated network connection with MQTT broker.
 */
void vStartSimpleMQTTDemo( void )
{
    /* This example uses a single application task, which in turn is used to
     * connect, subscribe, publish, unsubscribe, and disconnect from the MQTT
     * broker.
     *
     * Also see https://www.freertos.org/mqtt/mqtt-agent-demo.html? for an
     * alternative run time model whereby coreMQTT runs in an autonomous
     * background agent task.  Executing the MQTT protocol in an agent task
     * removes the need for the application writer to explicitly manage any MQTT
     * state or call the MQTT_ProcessLoop() API function. Using an agent task
     * also enables multiple application tasks to more easily share a single
     * MQTT connection. */
    xTaskCreate( prvMQTTDemoTask,          /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

/*
 * @brief The Example shown below uses MQTT APIs to create MQTT messages and
 * send them over the server-authenticated network connection established with the
 * MQTT broker. This example is single-threaded and uses statically allocated
 * memory. It uses QoS2 for sending and receiving messages from the broker.
 *
 * This MQTT client subscribes to the topic as specified in mqttexampleTOPIC at the
 * top of this file by sending a subscribe packet and waiting for a subscribe
 * acknowledgment (SUBACK) from the broker. The client will then publish to the
 * same topic it subscribed to, therefore expecting that all outgoing messages will be
 * sent back from the broker.
 */
static void prvMQTTDemoTask( void * pvParameters )
{
    uint32_t ulPublishCount = 0U, ulTopicCount = 0U;
    const uint32_t ulMaxPublishCount = 5UL;
    NetworkContext_t xNetworkContext = { 0 };
    PlaintextTransportParams_t xPlaintextTransportParams = { 0 };
    MQTTContext_t xMQTTContext = { 0 };
    MQTTStatus_t xMQTTStatus;
    PlaintextTransportStatus_t xNetworkStatus;
    MQTTConnectProperties_t xProperties;
    MQTTAckInfo_t disconnect = { 0 };




    MqttPropBuilder_t ackPropsBuilder;
    uint8_t ackPropsBuf[500]; 
    size_t ackPropsBufLength = sizeof(ackPropsBuf);
    MqttPropertyBuilder_Init(&(ackPropsBuilder), ackPropsBuf, ackPropsBufLength);

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pParams = &xPlaintextTransportParams;

    /* Set the entry time of the demo application. This entry time will be used
     * to calculate relative time elapsed in the execution of the demo application,
     * by the timer utility function that is provided to the MQTT library.
     */
    ulGlobalEntryTimeMs = prvGetTimeMs();


        LogInfo( ( "---------STARTING DEMO---------\r\n" ) );

        /**************************** Initialize. *****************************/

        prvInitializeTopicBuffers();

        /****************************** Connect. ******************************/

        /* Wait for Networking */
        if( xPlatformIsNetworkUp() == pdFALSE )
        {
            LogInfo( ( "Waiting for the network link up event..." ) );

            while( xPlatformIsNetworkUp() == pdFALSE )
            {
                vTaskDelay( pdMS_TO_TICKS( 1000U ) );
            }
        }

        /* Attempt to establish a TLS connection with the MQTT broker. This example
         * connects to the MQTT broker specified in democonfigMQTT_BROKER_ENDPOINT, using
         * the port number specified in democonfigMQTT_BROKER_PORT (these macros are defined
         * in file demo_config.h). If the connection fails, attempt to re-connect after a timeout.
         * The timeout value will be exponentially increased until either the maximum timeout value
         * is reached, or the maximum number of attempts are exhausted. The function returns a failure status
         * if the TCP connection cannot be established with the broker after a configured number
         * of attempts. */
        xNetworkStatus = prvConnectToServerWithBackoffRetries( &xNetworkContext );
        configASSERT( xNetworkStatus == PLAINTEXT_TRANSPORT_SUCCESS );

        /* Send an MQTT CONNECT packet over the established TLS connection,
         * and wait for the connection acknowledgment (CONNACK) packet. */
        LogInfo( ( "Creating an MQTT connection to %s.\r\n", democonfigMQTT_BROKER_ENDPOINT ) );
        prvCreateMQTTConnectionWithBroker( &xMQTTContext, &xNetworkContext, &xProperties, &ackPropsBuilder);


        /**************************** Publish and Keep-Alive Loop. ******************************


            /* Subscribing to Topics */
            LogInfo( ( "Attempt to send Subcribe to Broker.\r\n" ) );
            prvMQTTSubscribeToTopics(&xMQTTContext) ; 

            prvMQTTPublishToTopics(&xMQTTContext);




            /* Process incoming publish echo. Since the application subscribed and published
            / * to the same topic, the broker will send the incoming publish message back
            / * to the application. */

            prvMQTTUnsubscribeFromTopics(&xMQTTContext); 

            ///* Process incoming UNSUBACK packet from the broker. */
            xMQTTStatus = prvProcessLoopWithTimeout(&xMQTTContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS);
            configASSERT(xMQTTStatus == MQTTSuccess);



            MqttPropBuilder_t propBuilder;
            uint8_t buf[500];
            size_t bufLength = sizeof(buf);
            xMQTTStatus = MqttPropertyBuilder_Init(&(propBuilder), buf, bufLength); 

            MQTTUserProperties_t userProperty;
            memset(&userProperty, 0x0, sizeof(userProperty));
            userProperty.count = 1;
            userProperty.userProperty[0].pKey = "Disconnect";
            userProperty.userProperty[0].pValue = "Disconnect";
            userProperty.userProperty[0].keyLength = 10;
            userProperty.userProperty[0].valueLength = 10;
            

            MQTTDisconnectReasonCode_t reasonCode = MQTTNormalDisconnection; 
            xMQTTStatus = MQTTPropAdd_UserProps(&(propBuilder), &userProperty);
            xMQTTStatus = MQTTPropAdd_DisconnReasonString(&(propBuilder), "DISCONNECT-RS", 13); 

            xMQTTStatus = MQTT_Disconnect(&xMQTTContext, &propBuilder, MQTTNormalDisconnection);


            configASSERT(xMQTTStatus == MQTTSuccess);


        /* Close the network connection.  */
        Plaintext_FreeRTOS_Disconnect( &xNetworkContext );

        /* Wait for some time between two iterations to ensure that we do not
         * bombard the broker. */
        LogInfo( ( "prvMQTTDemoTask() completed an iteration successfully. Total free heap is %u.\r\n", xPortGetFreeHeapSize() ) );
        LogInfo( ( "Demo completed successfully.\r\n" ) );
        LogInfo( ( "-------DEMO FINISHED-------\r\n" ) );
        vTaskDelay( mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS_TICKS );


    
}
/*-----------------------------------------------------------*/

static PlaintextTransportStatus_t prvConnectToServerWithBackoffRetries( NetworkContext_t * pxNetworkContext )
{
    PlaintextTransportStatus_t xNetworkStatus;
    BackoffAlgorithmStatus_t xBackoffAlgStatus = BackoffAlgorithmSuccess;
    BackoffAlgorithmContext_t xReconnectParams;
    uint16_t usNextRetryBackOff = 0U;

    /* Initialize reconnect attempts and interval.*/
    BackoffAlgorithm_InitializeParams( &xReconnectParams,
                                       mqttexampleRETRY_BACKOFF_BASE_MS,
                                       mqttexampleRETRY_MAX_BACKOFF_DELAY_MS,
                                       mqttexampleRETRY_MAX_ATTEMPTS );

    /* Attempt to connect to MQTT broker. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase till maximum
     * attempts are reached.
     */
    do
    {
        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in democonfigMQTT_BROKER_ENDPOINT and
         * democonfigMQTT_BROKER_PORT at the top of this file. */
        LogInfo( ( "Create a TCP connection to %s:%d.",
                   democonfigMQTT_BROKER_ENDPOINT,
                   democonfigMQTT_BROKER_PORT ) );
        xNetworkStatus = Plaintext_FreeRTOS_Connect( pxNetworkContext,
                                                     democonfigMQTT_BROKER_ENDPOINT,
                                                     democonfigMQTT_BROKER_PORT,
                                                     mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                     mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( xNetworkStatus != PLAINTEXT_TRANSPORT_SUCCESS )
        {
            /* Generate a random number and calculate backoff value (in milliseconds) for
             * the next connection retry.
             * Note: It is recommended to seed the random number generator with a device-specific
             * entropy source so that possibility of multiple devices retrying failed network operations
             * at similar intervals can be avoided. */
            xBackoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &xReconnectParams, uxRand(), &usNextRetryBackOff );

            if( xBackoffAlgStatus == BackoffAlgorithmRetriesExhausted )
            {
                LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            }
            else if( xBackoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the broker failed. "
                           "Retrying connection with backoff and jitter." ) );
                vTaskDelay( pdMS_TO_TICKS( usNextRetryBackOff ) );
            }
        }
    } while( ( xNetworkStatus != PLAINTEXT_TRANSPORT_SUCCESS ) && ( xBackoffAlgStatus == BackoffAlgorithmSuccess ) );

    return xNetworkStatus;
}
/*-----------------------------------------------------------*/

static void prvCreateMQTTConnectionWithBroker( MQTTContext_t * pxMQTTContext,
                                               NetworkContext_t * pxNetworkContext, MQTTConnectProperties_t* pxProperties, MqttPropBuilder_t *ackPropsBuilder)
{
    MQTTStatus_t xResult;
    MQTTConnectInfo_t xConnectInfo;
    MQTTUserProperties_t xUserProperties ; 
    MQTTAckInfo_t disconnect;
    PlaintextTransportStatus_t xNetworkStatus;
    MQTTPublishInfo_t willInfo;
    MQTTAuthInfo_t auth;
    bool xSessionPresent;
    TransportInterface_t xTransport;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Fill in Transport Interface send and receive function pointers. */
    xTransport.pNetworkContext = pxNetworkContext;
    xTransport.send = Plaintext_FreeRTOS_send;
    xTransport.recv = Plaintext_FreeRTOS_recv;
    xTransport.writev = NULL;

    /* Initialize MQTT library. */
    xResult = MQTT_Init( pxMQTTContext, &xTransport, prvGetTimeMs, prvEventCallback, &xBuffer, ackPropsBuilder);
    configASSERT( xResult == MQTTSuccess );
    xResult = MQTT_InitStatefulQoS( pxMQTTContext,
                                    pOutgoingPublishRecords,
                                    mqttexampleOUTGOING_PUBLISH_RECORD_LEN,
                                    pIncomingPublishRecords,
                                    mqttexampleINCOMING_PUBLISH_RECORD_LEN );
    configASSERT( xResult == MQTTSuccess );

    /* Some fields are not used in this demo so start with everything at 0. */
    ( void ) memset( ( void * ) &xConnectInfo, 0x00, sizeof( xConnectInfo ) );
    (void)memset((void*)&disconnect, 0x00, sizeof(disconnect));
    (void)memset((void*)&willInfo, 0x00, sizeof(willInfo));
    (void)memset((void*)&auth, 0x00, sizeof(auth));


    MqttPropBuilder_t propBuilder;
    uint8_t buf[500];
    size_t bufLength = sizeof(buf);
    xResult = MqttPropertyBuilder_Init(&(propBuilder), buf, bufLength);

    xUserProperties.count = 1;
    xUserProperties.userProperty[0].pKey = "Key1";
    xUserProperties.userProperty[0].pValue = "Value1";
    xUserProperties.userProperty[0].keyLength = 4;
    xUserProperties.userProperty[0].valueLength = 6;

    uint32_t sessionExpiry = 20;
    uint16_t receiveMax = 20 ; 
    uint32_t maxPacketSize = 200; 
    uint16_t topicAliasMaximum = 20;

            
    xResult = MQTTPropAdd_UserProps(&(propBuilder), &xUserProperties);
    xResult = MQTTPropAdd_ConnSessionExpiry(&(propBuilder), sessionExpiry);
    xResult = MQTTPropAdd_ConnReceiveMax(&(propBuilder), receiveMax); 
    xResult = MQTTPropAdd_ConnMaxPacketSize(&(propBuilder), maxPacketSize);
    xResult = MQTTPropAdd_ConnTopicAliasMax(&(propBuilder), topicAliasMaximum);
    /*xResult = MQTTPropAdd_ConnRequestProbInfo(&(propBuilder), 0);*/
    xResult = MQTTPropAdd_ConnRequestRespInfo(&(propBuilder), 1);
    //xResult = MQTTPropAdd_ConnAuthMethod(&(propBuilder), "SCRAM-SHA-1 ", 11);
    //xResult = MQTTPropAdd_ConnAuthData(&(propBuilder), "test", 4);



    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */


    /* Set MQTT keep-alive period. If the application does not send packets at an interval less than
     * the keep-alive period, the MQTT library will send PINGREQ packets. */
    xConnectInfo.keepAliveSeconds = mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS;

    MqttPropBuilder_t willPropBuilder;
    uint8_t wbuf[500];
    size_t wbufLength = sizeof(wbuf);
    xResult = MqttPropertyBuilder_Init(&(willPropBuilder), wbuf, wbufLength);
    xResult = MQTTPropAdd_UserProps(&(willPropBuilder), &xUserProperties);

    /*LWT verification with user properties.*/
    /*LWT with will delay.*/
    LogInfo(("Create a good connection with the broker and disconnect without sending the disconnect packet to validate will delay"));
    xConnectInfo.cleanSession = true;
    xConnectInfo.clientIdentifierLength = 5;
    xConnectInfo.pClientIdentifier = "abcde";
    //xNetworkStatus = prvConnectToServerWithBackoffRetries(pxNetworkContext);
    //configASSERT(xNetworkStatus == PLAINTEXT_TRANSPORT_SUCCESS);
    willInfo.pTopicName = "TestWill1234";
    willInfo.topicNameLength = 12;
    willInfo.payloadLength = 15;
    willInfo.pPayload = "TestWillPayload";
    willInfo.willDelay = 30;


    xResult = MQTT_Connect(pxMQTTContext,
        &xConnectInfo,
        &willInfo,
        mqttexampleCONNACK_RECV_TIMEOUT_MS,
        &xSessionPresent, &propBuilder, &willPropBuilder);

    configASSERT( xResult == MQTTSuccess );

    /* Successfully established and MQTT connection with the broker. */
    LogInfo( ( "An MQTT connection is established with %s.", democonfigMQTT_BROKER_ENDPOINT ) );
}
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/


static void prvMQTTProcessResponse(MQTTPacketInfo_t* pxIncomingPacket,
    uint16_t usPacketId)
{
    uint32_t ulTopicCount = 0U;
    if ((pxIncomingPacket->type & 0xF0U) == MQTT_PACKET_TYPE_PUBLISH)
    {
        LogInfo(("Incoming Publish received for packet ID %u. \n\n", usPacketId));
    }
    else
    {
        switch (pxIncomingPacket->type)
        {
        case MQTT_PACKET_TYPE_PUBLISH:
            LogInfo(("Incoming Publish received for packet ID %u. \n\n", usPacketId));
            break;
        case MQTT_PACKET_TYPE_SUBACK:
            LogError(("SUBACK received for packet ID %u.", usPacketId));
            /* A SUBACK from the broker, containing the server response to our subscription request, has been received.
             * It contains the status code indicating server approval/rejection for the subscription to the single topic
             * requested. The SUBACK will be parsed to obtain the status code, and this status code will be stored in global
             * variable #xTopicFilterContext. */
            prvUpdateSubAckStatus(pxIncomingPacket);

            for (ulTopicCount = 0; ulTopicCount < mqttexampleTOPIC_COUNT; ulTopicCount++)
            {
                if (xTopicFilterContext[ulTopicCount].xSubAckStatus != MQTTSubAckFailure)
                {
                    LogInfo(("Subscribed to the topic %s with maximum QoS %u.\r\n",
                        xTopicFilterContext[ulTopicCount].pcTopicFilter,
                        xTopicFilterContext[ulTopicCount].xSubAckStatus));
                }
            }

            /* Make sure ACK packet identifier matches with Request packet identifier. */
            configASSERT(usSubscribePacketIdentifier == usPacketId);
            break;
        case MQTT_PACKET_TYPE_UNSUBACK:
            LogInfo(("Unsuback received for packet ID %u. \n\n", usPacketId));
            break;
        case MQTT_PACKET_TYPE_PUBACK:
            LogInfo(("PUBACK received for packet ID %u.\r\n", usPacketId));
            break;
        case MQTT_PACKET_TYPE_PINGRESP:

            /* Nothing to be done from application as library handles
             * PINGRESP with the use of MQTT_ProcessLoop API function. */
            LogWarn(("PINGRESP should not be handled by the application "
                "callback when using MQTT_ProcessLoop.\n"));
            break;

        case MQTT_PACKET_TYPE_PUBREC:
            LogInfo(("PUBREC received for packet id %u.\n\n",
                usPacketId));
            break;

        case MQTT_PACKET_TYPE_PUBREL:

            /* Nothing to be done from application as library handles
             * PUBREL. */
            LogInfo(("PUBREL received for packet id %u.\n\n",
                usPacketId));
            break;

        case MQTT_PACKET_TYPE_PUBCOMP:

            /* Nothing to be done from application as library handles
             * PUBCOMP. */
            LogInfo(("PUBCOMP received for packet id %u.\n\n",
                usPacketId));
            break;

            /* Any other packet type is invalid. */
        default:
            LogWarn(("prvMQTTProcessResponse() called with unknown packet type:(%02X).\r\n",
                pxIncomingPacket->type));
        }
    }
}

static void prvUpdateSubAckStatus(MQTTPacketInfo_t* pxPacketInfo)
{
    MQTTStatus_t xResult = MQTTSuccess;
    uint8_t* pucPayload = NULL;
    size_t ulSize = 0;
    uint32_t ulTopicCount = 0U;

    xResult = MQTT_GetSubAckStatusCodes(pxPacketInfo, &pucPayload, &ulSize);

    /* MQTT_GetSubAckStatusCodes always returns success if called with packet info
     * from the event callback and non-NULL parameters. */
    configASSERT(xResult == MQTTSuccess);

    for (ulTopicCount = 0; ulTopicCount < ulSize; ulTopicCount++)
    {
        xTopicFilterContext[ulTopicCount].xSubAckStatus = pucPayload[ulTopicCount];
    }
}


static void prvEventCallback( MQTTContext_t * pxMQTTContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              MQTTDeserializedInfo_t * pxDeserializedInfo, 
                              MQTTPublishFailReasonCode_t * pReasonCode)
{
    /* The MQTT context is not used in this function. */
    ( void ) pxMQTTContext;
        if (pxPacketInfo->type == MQTT_PACKET_TYPE_PUBREC)
        {
            *pReasonCode = MQTTPacketIdNotFound; 
            MQTTPropAdd_PubAckReasonString(pxMQTTContext, "TESTPUBREL", 10); 
            prvMQTTProcessResponse(pxPacketInfo, pxDeserializedInfo->packetIdentifier);

        }
        else if((pxPacketInfo->type & 0xF0U) == MQTT_PACKET_TYPE_PUBLISH)
        {
            uint8_t* pCurrIndex = NULL;
            char * pUserPropKey = NULL;
            uint16_t userPropKeyLen, userPropKeyVal;
            char* pUserPropVal = NULL;

            do {
                bool ret = MQTT_IncomingPubGetNextProp(&pCurrIndex,
                    &pUserPropKey,
                    &userPropKeyLen,
                    &pUserPropVal,
                    &userPropKeyVal,
                    pxDeserializedInfo);

                if (ret == false)
                {
                    LogError(("No more keys to iterate over."));
                    break;
                }
                if (pUserPropKey != NULL)
                {
                    if (strcmp(pUserPropKey, "Key2") == 0)
                    {
                        LogError(("Found the key."));
                        LogError(("The value is: %.*s", userPropKeyVal, pUserPropVal));
                        break;
                    }
                }
            } while (true);

            *pReasonCode = MQTTPublishSuccess; 
            MQTTUserProperties_t xUserProperties;
            (void)memset((void*)&xUserProperties, 0x00, sizeof(xUserProperties)); 

            xUserProperties.count = 1;
            xUserProperties.userProperty[0].pKey = "Key1";
            xUserProperties.userProperty[0].pValue = "Value1";
            xUserProperties.userProperty[0].keyLength = 4;
            xUserProperties.userProperty[0].valueLength = 6;

            MQTTPropAdd_UserProps(&pxMQTTContext->ackPropsBuffer,&xUserProperties);
            MQTTPropAdd_PubAckReasonString(pxMQTTContext, "TESTPUBREC", 10);

            if (strncmp(mqttexampleMESSAGE, (const char*)(pxDeserializedInfo->pPublishInfo->pPayload), pxDeserializedInfo->pPublishInfo->payloadLength) != 0)
            {
                LogError(("Incoming Publish Message: %.*s does not match Expected Message: %s.\r\n",
                    pxDeserializedInfo->pPublishInfo->topicNameLength,
                    pxDeserializedInfo->pPublishInfo->pTopicName, mqttexampleMESSAGE));
            }


            
            prvMQTTProcessResponse(pxPacketInfo, pxDeserializedInfo->packetIdentifier);
            
        }
        else if (pxPacketInfo->type == MQTT_PACKET_TYPE_CONNACK)
        {
            pxDeserializedInfo->pNextAckInfo = NULL;
            uint8_t* pCurrIndex = NULL;
            char* pUserPropKey = NULL;
            uint16_t userPropKeyLen, userPropKeyVal;
            char* pUserPropVal = NULL;

            do {
                bool ret = MQTT_ConnackGetNextProp(&pCurrIndex,
                    &pUserPropKey,
                    &userPropKeyLen,
                    &pUserPropVal,
                    &userPropKeyVal,
                    pxMQTTContext);

                if (ret == false)
                {
                    LogError(("No more keys to iterate over."));
                    break;
                }
                if (pUserPropKey != NULL)
                {
                    if (strcmp(pUserPropKey, "Key1") == 0)
                    {
                        LogError(("Found the key."));
                        LogError(("The value is: %.*s", userPropKeyVal, pUserPropVal));
                        break;
                    }
                }
            } while (true);

        }
        else if (pxPacketInfo->type == MQTT_PACKET_TYPE_SUBACK)
        {
            uint8_t *startOfRc; 
            size_t size; 
            startOfRc = pxDeserializedInfo->pAckInfo->reasonCode; 
            size = pxDeserializedInfo->pAckInfo->reasonCodeLength; 
            LogError(("The size of the reason code is %d", size));
            int i; 
            for (i = 0; i < size; i++)
            {
                LogError(("The reason code is %d", startOfRc[i]));
            }
            prvMQTTProcessResponse(pxPacketInfo, pxDeserializedInfo->packetIdentifier);
        }
        else if (pxPacketInfo->type == MQTT_PACKET_TYPE_PUBREL)
        {
            *pReasonCode = MQTTPublishSuccess;

        }
        else if (pxPacketInfo->type == MQTT_PACKET_TYPE_PUBCOMP)
        {
            *pReasonCode = MQTTPublishSuccess; 
            pxMQTTContext->ackPropsBuffer.pBuffer = NULL;
        }
        else
        {
            pxMQTTContext->ackPropsBuffer.pBuffer = NULL;  
            prvMQTTProcessResponse(pxPacketInfo, pxDeserializedInfo->packetIdentifier);

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
    ulTimeMs = ( uint32_t ) xTickCount * MILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = ( uint32_t ) ( ulTimeMs - ulGlobalEntryTimeMs );

    return ulTimeMs;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t prvProcessLoopWithTimeout( MQTTContext_t * pMqttContext,
                                               uint32_t ulTimeoutMs )
{
    uint32_t ulMqttProcessLoopTimeoutTime;
    uint32_t ulCurrentTime;

    MQTTStatus_t eMqttStatus = MQTTSuccess;

    ulCurrentTime = pMqttContext->getTime();
    ulMqttProcessLoopTimeoutTime = ulCurrentTime + ulTimeoutMs;

    /* Call MQTT_ProcessLoop multiple times a timeout happens, or
     * MQTT_ProcessLoop fails. */
    while( ( ulCurrentTime < ulMqttProcessLoopTimeoutTime ) &&
           ( eMqttStatus == MQTTSuccess || eMqttStatus == MQTTNeedMoreBytes ) )
    {
        eMqttStatus = MQTT_ProcessLoop( pMqttContext );
        ulCurrentTime = pMqttContext->getTime();
    }

    if( eMqttStatus == MQTTNeedMoreBytes )
    {
        eMqttStatus = MQTTSuccess;
    }

    return eMqttStatus;
}

/*-----------------------------------------------------------*/

static void prvInitializeTopicBuffers( void )
{
    uint32_t ulTopicCount;
    int xCharactersWritten;


    for( ulTopicCount = 0; ulTopicCount < mqttexampleTOPIC_COUNT; ulTopicCount++ )
    {
        /* Write topic strings into buffers. */
        xCharactersWritten = snprintf( xTopicFilterContext[ ulTopicCount ].pcTopicFilter,
                                       mqttexampleTOPIC_BUFFER_SIZE,
                                       "%s%d", mqttexampleTOPIC_PREFIX, ( int ) ulTopicCount );

        configASSERT( xCharactersWritten >= 0 && xCharactersWritten < mqttexampleTOPIC_BUFFER_SIZE );

        /* Assign topic string to its corresponding SUBACK code initialized as a failure. */
        xTopicFilterContext[ ulTopicCount ].xSubAckStatus = MQTTSubAckFailure;
    }
}

/*-----------------------------------------------------------*/


static void prvMQTTSubscribeToTopics( MQTTContext_t * pxMQTTContext )
{
    MQTTStatus_t xResult = MQTTSuccess;
    BackoffAlgorithmStatus_t xBackoffAlgStatus = BackoffAlgorithmSuccess;
    uint16_t usNextRetryBackOff = 0U;
    MQTTSubscribeInfo_t xMQTTSubscription[ mqttexampleTOPIC_COUNT ];
    MQTTUserProperties_t xUserProperties ; 
    bool xFailedSubscribeToTopic = false;
    BackoffAlgorithmContext_t xRetryParams;
    uint32_t ulTopicCount = 0U;

    /* Some fields not used by this demo so start with everything at 0. */
    ( void ) memset( ( void * ) &xMQTTSubscription, 0x00, sizeof( xMQTTSubscription ) );
    ( void ) memset(( void * ) &xUserProperties, 0x00, sizeof( xUserProperties ));

    /* Get a unique packet id. */
    usSubscribePacketIdentifier = MQTT_GetPacketId( pxMQTTContext );

    /* Populating the User Properties*/

    for (ulTopicCount = 0; ulTopicCount < mqttexampleTOPIC_COUNT; ulTopicCount++)
    {
        xMQTTSubscription[ulTopicCount].qos = MQTTQoS2;
        xMQTTSubscription[ulTopicCount].pTopicFilter = xTopicFilterContext[ulTopicCount].pcTopicFilter;
        xMQTTSubscription[ulTopicCount].topicFilterLength = (uint16_t)strlen(xTopicFilterContext[ulTopicCount].pcTopicFilter);
        xMQTTSubscription[ulTopicCount].noLocalOption = false; 
        xMQTTSubscription[ulTopicCount].retainHandlingOption = 1; 
        xMQTTSubscription[ulTopicCount].retainAsPublishedOption = true;
    }
     
    xUserProperties.count = 1;
    xUserProperties.userProperty[0].pKey = "Key1";
    xUserProperties.userProperty[0].pValue = "Value1";
    xUserProperties.userProperty[0].keyLength = 4;
    xUserProperties.userProperty[0].valueLength = 6;

    MqttPropBuilder_t propBuilder;
    uint8_t buf[500];
    size_t bufLength = sizeof(buf);

    size_t subId = 2; 
    xResult = MqttPropertyBuilder_Init(&(propBuilder), buf, bufLength); 
    xResult = MQTTPropAdd_SubscribeId(&(propBuilder), subId); 
    xResult = MQTTPropAdd_UserProps(&(propBuilder), &xUserProperties);
    xResult = MQTTPropAdd_SubscribeId(&(propBuilder), 7);
   

/* The client is now connected to the broker. Subscribe to the topic
    * as specified in mqttexampleTOPIC at the top of this file by sending a
    * subscribe packet then waiting for a subscribe acknowledgment (SUBACK).
    * This client will then publish to the same topic it subscribed to, so it
    * will expect all the messages it sends to the broker to be sent back to it
    * from the broker. This demo uses QOS2 in Subscribe, therefore, the Publish
    * messages received from the broker will have QOS2. */

/* The client is now connected to the broker. Subscribe to the topic
    * as specified in mqttexampleTOPIC at the top of this file by sending a
    * subscribe packet then waiting for a subscribe acknowledgment (SUBACK).
    * This client will then publish to the same topic it subscribed to, so it
    * will expect all the messages it sends to the broker to be sent back to it
    * from the broker. This demo uses QOS2 in Subscribe, therefore, the Publish
    * messages received from the broker will have QOS2. */

    BackoffAlgorithm_InitializeParams(  &xRetryParams,
                                        mqttexampleRETRY_BACKOFF_BASE_MS,
                                        mqttexampleRETRY_MAX_BACKOFF_DELAY_MS,
                                        mqttexampleRETRY_MAX_ATTEMPTS);

    do
    {

        xResult = MQTT_Subscribe(   pxMQTTContext,
                                    xMQTTSubscription,
                                    2,
                                    usSubscribePacketIdentifier,
                                    &(propBuilder));

        LogInfo(("Attempt to receive SubAcks from Broker. \r\n"));
        configASSERT(xResult == MQTTSuccess);

        for (ulTopicCount = 0; ulTopicCount < mqttexampleTOPIC_COUNT; ulTopicCount++)
        {
            LogInfo(("SUBSCRIBE sent for topic %s to broker.\n\n",
                xTopicFilterContext[ulTopicCount].pcTopicFilter));
        }


        /* Process incoming packet from the broker. After sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Therefore,
         * call generic incoming packet processing function. Since this demo is
         * subscribing to the topic to which no one is publishing, probability of
         * receiving Publish message before subscribe ack is zero; but application
         * must be ready to receive any packet.  This demo uses the generic packet
         * processing function everywhere to highlight this fact. */
        xResult = prvProcessLoopWithTimeout(pxMQTTContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS);
        configASSERT(xResult == MQTTSuccess);

        /* Reset flag before checking suback responses. */
        xFailedSubscribeToTopic = false;

        /* Check if recent subscription request has been rejected. #xTopicFilterContext is updated
         * in the event callback to reflect the status of the SUBACK sent by the broker. It represents
         * either the QoS level granted by the server upon subscription, or acknowledgement of
         * server rejection of the subscription request. */
        for (ulTopicCount = 0; ulTopicCount < mqttexampleTOPIC_COUNT; ulTopicCount++)
        {
            if (xTopicFilterContext[ulTopicCount].xSubAckStatus == MQTTSubAckFailure)
            {
                xFailedSubscribeToTopic = true;

                /* Generate a random number and calculate backoff value (in milliseconds) for
                 * the next connection retry.
                 * Note: It is recommended to seed the random number generator with a device-specific
                 * entropy source so that possibility of multiple devices retrying failed network operations
                 * at similar intervals can be avoided. */
                xBackoffAlgStatus = BackoffAlgorithm_GetNextBackoff(&xRetryParams, uxRand(), &usNextRetryBackOff);

                if (xBackoffAlgStatus == BackoffAlgorithmRetriesExhausted)
                {
                    LogError(("Server rejected subscription request. All retry attempts have exhausted. Topic=%s",
                        xTopicFilterContext[ulTopicCount].pcTopicFilter));
                }
                else if (xBackoffAlgStatus == BackoffAlgorithmSuccess)
                {
                    LogWarn(("Server rejected subscription request. Attempting to re-subscribe to topic %s.",
                        xTopicFilterContext[ulTopicCount].pcTopicFilter));
                    /* Backoff before the next re-subscribe attempt. */
                    vTaskDelay(pdMS_TO_TICKS(usNextRetryBackOff));
                }

                break;
            }
        }
        configASSERT(xBackoffAlgStatus != BackoffAlgorithmRetriesExhausted);
    } while ((xFailedSubscribeToTopic == true) && (xBackoffAlgStatus == BackoffAlgorithmSuccess));

}   



static void prvMQTTUnsubscribeFromTopics(MQTTContext_t* pxMQTTContext)
{
    MQTTStatus_t xResult;
    MQTTSubscribeInfo_t xMQTTSubscription = { 0 };
    MQTTUserProperties_t xUserProperties;

    /* Some fields are not used by this demo so start with everything at 0. */
    memset((void*)&xMQTTSubscription, 0x00, sizeof(xMQTTSubscription));
    memset((void*)&xUserProperties, 0x00, sizeof(xUserProperties));

    MqttPropBuilder_t propBuilder;
    uint8_t buf[500];
    size_t bufLength = sizeof(buf);

    xResult = MqttPropertyBuilder_Init(&(propBuilder), buf, bufLength);

    /* Populate subscription list. */
    xUserProperties.count = 1;
    xUserProperties.userProperty[0].pKey = "Key1";
    xUserProperties.userProperty[0].pValue = "Value1";
    xUserProperties.userProperty[0].keyLength = 4;
    xUserProperties.userProperty[0].valueLength = 6;

    xResult = MQTTPropAdd_UserProps(&(propBuilder), &xUserProperties);
    
    xMQTTSubscription.qos = MQTTQoS2;
    xMQTTSubscription.pTopicFilter = "test1";
    xMQTTSubscription.topicFilterLength = 5;

    
    LogInfo(("Unsubscribing from topic %s.\r\n", xMQTTSubscription.pTopicFilter));


    /* Get next unique packet identifier. */
    usUnsubscribePacketIdentifier = MQTT_GetPacketId(pxMQTTContext);
    /* Make sure the packet id obtained is valid. */
    configASSERT(usUnsubscribePacketIdentifier != 0);

    /* Send UNSUBSCRIBE packet. */
    xResult = MQTT_Unsubscribe(pxMQTTContext,
        &xMQTTSubscription,
        1,
        usUnsubscribePacketIdentifier,
        &(propBuilder));

    configASSERT(xResult == MQTTSuccess);
}


static void prvMQTTPublishToTopics( MQTTContext_t * pxMQTTContext )
{
    MQTTStatus_t xResult;
    MQTTPublishInfo_t xMQTTPublishInfo;
    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/
        /* Some fields are not used by this demo so start with everything at 0. */
        ( void ) memset( ( void * ) &xMQTTPublishInfo, 0x00, sizeof( xMQTTPublishInfo ) );
        /* This demo uses QoS0 */
        MQTTUserProperties_t userProperty;
        userProperty.count = 1;
        userProperty.userProperty[0].pKey = "Key1";
        userProperty.userProperty[0].pValue = "Value1";
        userProperty.userProperty[0].keyLength = 4;
        userProperty.userProperty[0].valueLength = 6;

        MqttPropBuilder_t propBuilder;
        uint8_t buf[500];
        size_t bufLength = sizeof(buf);

        xResult = MqttPropertyBuilder_Init(&(propBuilder), buf, bufLength);

        xResult = MQTTPropAdd_UserProps(&(propBuilder), &userProperty);
        xResult = MQTTPropAdd_PubPayloadFormat(&(propBuilder), 1);
        xResult = MQTTPropAdd_PubMessageExpiry(&(propBuilder), 100);
        //xResult = MQTTPropAdd_PubTopicAlias(&(propBuilder), 30);
        xResult = MQTTPropAdd_PubResponseTopic(&(propBuilder), "test", 4);
        xResult = MQTTPropAdd_PubCorrelationData(&(propBuilder), "test", 4);
       /* xResult = MQTTPropAdd_PubSubscriptionId(&(propBuilder),2 ); */
        xResult = MQTTPropAdd_PubContentType(&(propBuilder), "test", 4);

        userProperty.count = 1;
        userProperty.userProperty[0].pKey = "Key2";
        userProperty.userProperty[0].pValue = "Value2";
        userProperty.userProperty[0].keyLength = 4;
        userProperty.userProperty[0].valueLength = 6;

        xResult = MQTTPropAdd_UserProps(&(propBuilder), &userProperty); 

        xMQTTPublishInfo.qos = MQTTQoS2;
        xMQTTPublishInfo.retain = false;
        xMQTTPublishInfo.pTopicName = "test1";
        xMQTTPublishInfo.topicNameLength = 5;
        xMQTTPublishInfo.pPayload = mqttexampleMESSAGE;
        xMQTTPublishInfo.payloadLength = strlen( mqttexampleMESSAGE );

        /* Get a unique packet id. */
        usPublishPacketIdentifier = MQTT_GetPacketId( pxMQTTContext );

        LogInfo( ( "Publishing to the MQTT topic %s.\r\n", xMQTTPublishInfo.pTopicName));
        /* Send PUBLISH packet. */
        xResult = MQTT_Publish( pxMQTTContext, &xMQTTPublishInfo, usPublishPacketIdentifier , &(propBuilder));
        configASSERT( xResult == MQTTSuccess );


        LogInfo(("Attempt to receive publishes from broker.\r\n"));
        xResult = prvProcessLoopWithTimeout(pxMQTTContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS);
        configASSERT(xResult == MQTTSuccess);

        /* Leave connection idle for some time. */
        LogInfo(("Keeping Connection Idle...\r\n\r\n"));
        vTaskDelay(mqttexampleDELAY_BETWEEN_PUBLISHES_TICKS);
    }
