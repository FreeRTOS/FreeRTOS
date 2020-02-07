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
 * 1 tab == 4 spaces!
 */

/*
 * This file contains the common functions for plain text, basic TLS, and mutual
 * authentication MQTT demos. Aside from the difference in security level during
 * connect, the three demos perform the same interaction with a MQTT broker. The
 * demos create a single application task that connects to a MQTT broker,
 * subscribes to a topic, publishes a topic with a message, and disconnect from a
 * MQTT broker. The task subscribes to the same topic it publishes to, receiving
 * the message it sends to the broker. Note that this demo does not terminate, the
 * connect-subscribe-publish-disconnect cycle is repeated for unlimited number of
 * times.
 *
 * The plain text MQTT demo does not authenticate the server nor the client. The
 * basic TLS MQTT demo builds on top of the plain text demo, adding broker
 * authentication and encryption. The mutual authentication MQTT demo builds on top
 * of the basic TLS demo, enabling both server and client authentication.
 *
 * For more information regarding the MQTT library and the demo, please refer to:
 * https://freertos.org/mqtt/index.html
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

/* IoT SDK includes. */
#include "iot_mqtt.h"
#include "iot_taskpool_freertos.h"
#include "platform/iot_network_freertos.h"

/* MQTT Demo Select */
#include "demo_config.h"

/* Select MQTT profile based on the setting in demo_config.h */
#if ( democonfigPROFILE_USE_AWS_IOT == 1 )
	#include "aws_iot_demo_profile.h"
#else
	#include "mqtt_demo_profile.h"
#endif

/* Preprocessor check for configuration */
#include "aws_iot_setup_check.h"

/*
 * Set connection profile based on the setting in demo_config.h. For more
 * information on each variable, please refer to the respective *_profile.h
 * file in FreeRTOS-Labs\Demo\FreeRTOS_IoT_Libraries\include.
 *
 * Note that if you are running mqtt_tls_mutual_auth demo please make sure to
 * visit the following link for setup:
 * https://www.freertos.org/mqtt/preconfiguredexamplesMA.html
 */
#if ( democonfigPROFILE_USE_AWS_IOT == 1 )
	#define mqttexampleBROKER_ENDPOINT			 awsiotdemoprofileAWS_ENDPOINT
	#define mqttexampleBROKER_PORT				 awsiotdemoprofileAWS_MQTT_PORT
	#define mqttexampleBROKER_CERTIFICATE_PEM	 awsiotdemoprofileAWS_CERTIFICATE_PEM
	#define mqttexampleCLIENT_IDENTIFIER		 awsiotdemoprofileCLIENT_IDENTIFIER
	#define mqttexampleCLIENT_CERTIFICATE_PEM	 awsiotdemoprofileCLIENT_CERTIFICATE_PEM
	#define mqttexampleCLIENT_PRIVATE_KEY_PEM	 awsiotdemoprofileCLIENT_PRIVATE_KEY_PEM
#else
	#define mqttexampleBROKER_ENDPOINT			 mqttdemoprofileBROKER_ENDPOINT
	#define mqttexampleBROKER_PORT				 mqttdemoprofileBROKER_PORT
	#define mqttexampleBROKER_CERTIFICATE_PEM	 mqttdemoprofileBROKER_CERTIFICATE_PEM
	#define mqttexampleCLIENT_IDENTIFIER		 mqttdemoprofileCLIENT_IDENTIFIER
#endif /* if ( democonfigPROFILE_USE_AWS_IOT == pdTRUE ) */

/**
 * @brief The keep-alive interval used for this example.
 *
 * An MQTT ping request will be sent periodically at this interval.
 *
 * @note: This value is set to zero to disable MQTT
 * keep alive for the Windows simulator project.
 * The FreeRTOS kernel does not accurately calculate time for the Windows
 * Simulator. Therefore, MQTT PING Request messages may be sent
 * at an incorrect time interval to the broker. If the broker does
 * not receive a ping request within 1.5x the time sent in a
 * connection request, the broker may close the connection.
 * To enable the keep alive feature, set this value
 * to the desired interval in seconds.
 */
#define mqttexampleKEEP_ALIVE_SECONDS	   ( 0 )

/**
 * @brief The timeout for MQTT operations in this example.
 */
#define mqttexampleMQTT_TIMEOUT_MS		   ( 5000 )

/**
 * @brief The topic to subscribe and publish to in the example.
 *
 * The topic starts with the client identifier to ensure that each demo interacts
 * with a unique topic.
 */
#define mqttexampleTOPIC				   mqttexampleCLIENT_IDENTIFIER "/example/topic"

/**
 * @brief The MQTT message published in this example.
 */
#define mqttexampleMESSAGE				   "Hello World!"

/**
 * @brief Parameters to control the retry behavior in case a QoS1 publish
 * message gets lost.
 *
 * Retry every minutes up to a maximum of 5 retries.
 */
#define mqttexamplePUBLISH_RETRY_MS		   ( 1000 )
#define mqttexamplePUBLISH_RETRY_LIMIT	   ( 5 )

/**
 * @brief The bit which is set in the demo task's notification value from the
 * disconnect callback to inform the demo task about the MQTT disconnect.
 */
#define mqttexampleDISCONNECTED_BIT		   ( 1UL << 0UL )

/**
 * @brief The bit which is set in the demo task's notification value from the
 * publish callback to inform the demo task about the message received from the
 * MQTT broker.
 */
#define mqttexampleMESSAGE_RECEIVED_BIT	   ( 1UL << 1UL )

/*-----------------------------------------------------------*/

/**
 * @brief The task used to demonstrate the MQTT API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvMQTTDemoTask( void * pvParameters );

/**
 * @brief The callback invoked by the MQTT library when the MQTT connection gets
 * disconnected.
 *
 * @param[in] pvCallbackContext Callback context as provided at the time of
 * connect.
 * @param[in] pxCallbackParams Contains the reason why the MQTT connection was
 * disconnected.
 */
static void prvExample_OnDisconnect( void * pvCallbackContext,
									 IotMqttCallbackParam_t * pxCallbackParams );

/**
 * @brief The callback invoked by the MQTT library when a message is received on
 * a subscribed topic from the MQTT broker.
 *
 * @param[in] pvCallbackContext Callback context as provided at the time of
 * subscribe.
 * @param[in] pxCallbackParams Contain the details about the received message -
 * topic on which the message was received, the received message.
 */
static void prvExample_OnMessageReceived( void * pvCallbackContext,
										  IotMqttCallbackParam_t * pxCallbackParams );

/**
 * @brief Connects to the MQTT broker as specified in mqttexampleBROKER_ENDPOINT
 * and mqttexampleBROKER_PORT.
 */
static void prvMQTTConnect( void );

/**
 * @brief Subscribes to the topic as specified in mqttexampleTOPIC.
 */
static void prvMQTTSubscribe( void );

/**
 * @brief Publishes a messages mqttexampleMESSAGE on mqttexampleTOPIC topic.
 */
static void prvMQTTPublish( void );

/**
 * @brief Unsubscribes from the mqttexampleTOPIC topic.
 */
static void prvMQTTUnsubscribe( void );

/**
 * @brief Disconnects from the MQTT broker gracefully by sending an MQTT
 * DISCONNECT message.
 */
static void prvMQTTDisconnect( void );

/**
* @brief Initializes the IoT libraries used by this demo.
*/
static void prvInitialiseLibraries( void );

/**
 * @brief The MQTT connection handle used in this example.
 */
static IotMqttConnection_t xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/*-----------------------------------------------------------*/

/**
 * @brief Parameters used to create the system task pool.
 */
static const IotTaskPoolInfo_t xTaskPoolParameters =
{
	/* Minimum number of threads in a task pool.
	 * Note the slimmed down version of the task
	 * pool used by this library does not auto-scale
	 * the number of tasks in the pool so in this
	 * case this sets the number of tasks in the
	 * pool. */
	1,

	/* Maximum number of threads in a task pool.
	 * Note the slimmed down version of the task
	 * pool used by this library does not auto-scale
	 * the number of tasks in the pool so in this
	 * case this parameter is just ignored. */
	1,

	/* Stack size for every task pool thread - in
	 * bytes, hence multiplying by the number of bytes
	 * in a word as configMINIMAL_STACK_SIZE is
	 * specified in words. */
	configMINIMAL_STACK_SIZE * sizeof( portSTACK_TYPE ),
	/* Priority for every task pool thread. */
	tskIDLE_PRIORITY,
};

/*-----------------------------------------------------------*/

static const struct IotNetworkServerInfo xMQTTBrokerInfo =
{
	.pHostName = mqttexampleBROKER_ENDPOINT,
	.port = mqttexampleBROKER_PORT
};

#if ( democonfigENABLE_TLS )
	static struct IotNetworkCredentials xNetworkSecurityCredentials =
	{
		/* Optional TLS extensions. For this demo, they are disabled. */
		.pAlpnProtos = NULL,
		.maxFragmentLength = 0,

		/* SNI is enabled by default. */
		.disableSni = false,

		/* Provide the certificate for validating the server. Only required for
		 * demos using TLS. */
		.pRootCa = mqttexampleBROKER_CERTIFICATE_PEM,
		.rootCaSize = sizeof( mqttexampleBROKER_CERTIFICATE_PEM ),

		/* Strong mutual authentication to authenticate both the broker and
		 * the client. */
		#if ( democonfigENABLE_MUTUAL_AUTH )
			.pClientCert = mqttexampleCLIENT_CERTIFICATE_PEM,
			.clientCertSize = sizeof( mqttexampleCLIENT_CERTIFICATE_PEM ),
			.pPrivateKey = mqttexampleCLIENT_PRIVATE_KEY_PEM,
			.privateKeySize = sizeof( mqttexampleCLIENT_PRIVATE_KEY_PEM )
		#else
			.pClientCert = NULL,
			.clientCertSize = 0,
			.pPrivateKey = NULL,
			.privateKeySize = 0
		#endif /* if ( democonfigENABLE_MUTUAL_AUTH ) */
	};
#endif /* if ( democonfigENABLE_TLS ) */

static IotMqttNetworkInfo_t xNetworkInfo =
{
	/* No connection to the MQTT broker has been established yet and we want to
	 * establish a new connection. */
	.createNetworkConnection = true,
	.u.setup.pNetworkServerInfo = &( xMQTTBrokerInfo ),

	/* Set the TLS credentials for the new MQTT connection. This member is NULL
	 * for the plain text MQTT demo. */
	#if ( democonfigENABLE_TLS )
		.u.setup.pNetworkCredentialInfo = &xNetworkSecurityCredentials,
	#else
		.u.setup.pNetworkCredentialInfo = NULL, /* Not using TLS so no credentials. */
	#endif

	/* Use FreeRTOS+TCP network interface. */
	.pNetworkInterface = IOT_NETWORK_INTERFACE_FREERTOS,

	/* Setup the callback which is called when the MQTT connection is
	 * disconnected. The task handle is passed as the callback context which
	 * is used by the callback to send a task notification to this task.*/
	.disconnectCallback.function = prvExample_OnDisconnect
};

static const IotMqttConnectInfo_t xConnectInfo =
{
	/* Set this flag to true if connecting to the AWS IoT MQTT broker. */
	#if ( democonfigPROFILE_USE_AWS_IOT == 1 )
		.awsIotMqttMode = true,
	#else
		.awsIotMqttMode = false,
	#endif

	/* Start with a clean session i.e. direct the MQTT broker to discard any
	 * previous session data. Also, establishing a connection with clean session
	 * will ensure that the broker does not store any data when this client
	 * gets disconnected. */
	.cleanSession = true,

	/* Since we are starting with a clean session, there are no previous
	 * subscriptions to be restored. */
	.pPreviousSubscriptions = NULL,
	.previousSubscriptionCount = 0,

	/* We do not want to publish Last Will and Testament (LWT) message if the
	 * client gets disconnected. */
	.pWillInfo = NULL,

	/* Send an MQTT PING request every minute to keep the connection open if
	there is no other MQTT traffic. */
	.keepAliveSeconds = mqttexampleKEEP_ALIVE_SECONDS,

	/* The client identifier is used to uniquely identify this MQTT client to
	 * the MQTT broker.  In a production device the identifier can be something
	 * unique, such as a device serial number. */
	.pClientIdentifier = mqttexampleCLIENT_IDENTIFIER,
	.clientIdentifierLength = ( uint16_t ) sizeof( mqttexampleCLIENT_IDENTIFIER ) - 1,

	/* This example does not authenticate the client and therefore username and
	 * password fields are not used. */
	.pUserName = NULL,
	.userNameLength = 0,
	.pPassword = NULL,
	.passwordLength = 0
};
/*-----------------------------------------------------------*/


void vStartSimpleMQTTDemo( void )
{
TickType_t xShortDelay = ( TickType_t ) pdMS_TO_TICKS( ( TickType_t ) 500 );

	/* Wait a short time to allow receipt of the ARP replies. */
	vTaskDelay( xShortDelay );

	/* This example uses a single application task, which in turn is used to
	 * connect, subscribe, publish, unsubscribe and disconnect from the MQTT
	 * broker. */
	xTaskCreate( prvMQTTDemoTask,          /* Function that implements the task. */
				 "MQTTDemo",               /* Text name for the task - only used for debugging. */
				 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,                     /* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void * pvParameters )
{
uint32_t ulNotificationValue = 0, ulPublishCount;
const uint32_t ulMaxPublishCount = 5UL;
const TickType_t xNoDelay = ( TickType_t ) 0;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* One time initialization of the libraries used by this demo. */
	prvInitialiseLibraries();

	for( ; ; )
	{
		/* Notifications are used to send events from the callback functions to this
		 * task.  Don't expect any notifications to be pending at the beginning of the
		 * loop. */
		configASSERT( ulTaskNotifyTake( pdTRUE, xNoDelay ) == 0 );


		/****************************** Connect. ******************************/

		/* Establish a connection to the MQTT broker. This example connects to
		 * the MQTT broker as specified by the compile time constants
		 * mqttexampleBROKER_ENDPOINT and mqttexampleBROKER_PORT.
		 * Please change it to the MQTT broker you want to connect to. */
		configPRINTF( ( "Attempt to connect to %s:%d\r\n", mqttexampleBROKER_ENDPOINT, mqttexampleBROKER_PORT ) );
		prvMQTTConnect();
		configPRINTF( ( "Connected to %s:%d\r\n", mqttexampleBROKER_ENDPOINT, mqttexampleBROKER_PORT ) );


		/**************************** Subscribe. ******************************/

		/* The client is now connected to the broker. Subscribe to the topic
		 * as specified by the mqttexampleTOPIC compile time constant.  This
		 * client will then publish to the same topic it subscribed to, so will
		 * expect all the messages it sends to the broker to be sent back to it
		 * from the broker. */
		configPRINTF( ( "Attempt to subscribed to the topic %s\r\n", mqttexampleTOPIC ) );
		prvMQTTSubscribe();
		configPRINTF( ( "Subscribed to the topic %s\r\n", mqttexampleTOPIC ) );


		/*********************** Publish ulMaxPublishCount messages. **********/

		/* Publish a few messages while connected. */
		for( ulPublishCount = 0; ulPublishCount < ulMaxPublishCount; ulPublishCount++ )
		{
			/* Publish a message on the topic specified by the mqttexampleTOPIC
			 * compile time constant. */
			configPRINTF( ( "Publish %s on the topic %s\r\n", mqttexampleMESSAGE, mqttexampleTOPIC ) );
			prvMQTTPublish();
			configPRINTF( ( "Published %s on the topic %s\r\n", mqttexampleMESSAGE, mqttexampleTOPIC ) );

			/* Since we are subscribed to the same topic as we published on, we
			 * will get the same message back from the MQTT broker. Wait for the
			 * message to be received which is signaled to us by the publish
			 * callback (prvExample_OnMessageReceived) setting the
			 * mqttexampleMESSAGE_RECEIVED_BIT bit in this task's notification
			 * value. Note the bit is then cleared in the task's notification value
			 * to ensure the bit being set can be detected on the next iteration. */
			xTaskNotifyWait( 0UL,                             /* Don't clear any bits on entry. */
							 mqttexampleMESSAGE_RECEIVED_BIT, /* Clear bit on exit. */
							 &( ulNotificationValue ),        /* Obtain the notification value. */
							 pdMS_TO_TICKS( mqttexampleMQTT_TIMEOUT_MS ) );
			configASSERT( ( ulNotificationValue & mqttexampleMESSAGE_RECEIVED_BIT ) == mqttexampleMESSAGE_RECEIVED_BIT );
		}

		/******************* Unsubscribe and Disconnect. **********************/

		/* Unsubscribe from the topic mqttexampleTOPIC and disconnect
		 * gracefully. */
		prvMQTTUnsubscribe();
		prvMQTTDisconnect();
		configPRINTF( ( "Disconnected from %s:%d\r\n\r\n", mqttexampleBROKER_ENDPOINT, mqttexampleBROKER_PORT ) );

		/* Wait for the disconnect operation to complete which is signaled to us
		 * by the disconnect callback (prvExample_OnDisconnect)by setting
		 * the mqttexampleDISCONNECTED_BIT bit in this task's notification value.
		 * Note the bit is cleared in the task's notification value again to ensure
		 * it being set can be detected again on the next iteration. */
		xTaskNotifyWait( 0UL,                         /* Don't clear any bits on entry. */
						 mqttexampleDISCONNECTED_BIT, /* Clear bit on exit. */
						 &( ulNotificationValue ),    /* Obtain the notification value. */
						 pdMS_TO_TICKS( mqttexampleMQTT_TIMEOUT_MS ) );
		configASSERT( ( ulNotificationValue & mqttexampleDISCONNECTED_BIT ) == mqttexampleDISCONNECTED_BIT );

		/* Delay between iterations to avoid broker throttling. */
		configPRINTF( ( "prvMQTTDemoTask() completed an iteration successfully. Total free heap is %u\r\n", xPortGetFreeHeapSize() ) );
		configPRINTF( ( "Demo completed successfully.\r\n" ) );
		configPRINTF( ( "Short delay before starting the next iteration.... \r\n\r\n" ) );
		vTaskDelay( pdMS_TO_TICKS( mqttexampleMQTT_TIMEOUT_MS ) );
	}
}
/*-----------------------------------------------------------*/

static void prvExample_OnDisconnect( void * pvCallbackContext,
									 IotMqttCallbackParam_t * pxCallbackParams )
{
TaskHandle_t xDemoTaskHandle = ( TaskHandle_t ) pvCallbackContext;

	/* Ensure that we initiated the disconnect. */
	configASSERT( pxCallbackParams->u.disconnectReason == IOT_MQTT_DISCONNECT_CALLED );

	/* Inform the demo task about the disconnect. */
	xTaskNotify( xDemoTaskHandle,
				 mqttexampleDISCONNECTED_BIT,
				 eSetBits /* Set the mqttexampleDISCONNECTED_BIT in the demo task's notification value. */
				 );
}
/*-----------------------------------------------------------*/

static void prvExample_OnMessageReceived( void * pvCallbackContext,
										  IotMqttCallbackParam_t * pxCallbackParams )
{
TaskHandle_t xDemoTaskHandle = ( TaskHandle_t ) pvCallbackContext;

	/* Ensure the message is received on the expected topic. */
	configASSERT( pxCallbackParams->u.message.info.topicNameLength == strlen( mqttexampleTOPIC ) );
	configASSERT( strncmp( pxCallbackParams->u.message.info.pTopicName,
						   mqttexampleTOPIC,
						   strlen( mqttexampleTOPIC ) ) == 0 );

	/* Ensure the message itself is as expected. */
	configASSERT( pxCallbackParams->u.message.info.payloadLength == strlen( mqttexampleMESSAGE ) );
	configASSERT( strncmp( pxCallbackParams->u.message.info.pPayload,
						   mqttexampleMESSAGE,
						   strlen( mqttexampleMESSAGE ) ) == 0 );

	/* Ensure the message Quality of Service (QoS) is as expected. */
	configASSERT( pxCallbackParams->u.message.info.qos == IOT_MQTT_QOS_1 );

	/* So as not to worry about string lengths the print message uses the
	 * consts rather than the data from the message, but the asserts above have
	 * already checked the two are equal. */
	configPRINTF( ( "Received %s on the topic %s\r\n", mqttexampleMESSAGE, mqttexampleTOPIC ) );

	/* Inform the demo task about the message received from the MQTT broker by
	 * setting the mqttexampleMESSAGE_RECEIVED_BIT bit in the task's notification
	 * value. */
	xTaskNotify( xDemoTaskHandle,
				 mqttexampleMESSAGE_RECEIVED_BIT,
				 eSetBits /* Set the mqttexampleMESSAGE_RECEIVED_BIT in the demo task's notification value. */
				 );
}
/*-----------------------------------------------------------*/

static void prvMQTTConnect( void )
{
IotMqttError_t xResult;

	/* Set the context to pass into the disconnect callback function. */
	xNetworkInfo.disconnectCallback.pCallbackContext = ( void * ) xTaskGetCurrentTaskHandle();

	/* Establish the connection to the MQTT broker - It is a blocking call and
	 * will return only when connection is complete or a timeout occurs.  The
	 * network and connection structures are declared and initialized at the top
	 * of this file. */
	xResult = IotMqtt_Connect( &( xNetworkInfo ),
							   &( xConnectInfo ),
							   mqttexampleMQTT_TIMEOUT_MS,
							   &( xMQTTConnection ) );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvMQTTDisconnect( void )
{
	/* Send a MQTT DISCONNECT packet to the MQTT broker to do a graceful
	 * disconnect. */
	IotMqtt_Disconnect( xMQTTConnection,
						0 /* flags - 0 means a graceful disconnect by sending MQTT DISCONNECT. */
						);
}
/*-----------------------------------------------------------*/

static void prvMQTTSubscribe( void )
{
IotMqttError_t xResult;
IotMqttSubscription_t xMQTTSubscription;

	/* Subscribe to the mqttexampleTOPIC topic filter. The task handle is passed
	 * as the callback context, which is then used by the callback to send a task
	 * notification to this task.*/
	xMQTTSubscription.qos = IOT_MQTT_QOS_1;
	xMQTTSubscription.pTopicFilter = mqttexampleTOPIC;
	xMQTTSubscription.topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );
	xMQTTSubscription.callback.pCallbackContext = ( void * ) xTaskGetCurrentTaskHandle();
	xMQTTSubscription.callback.function = prvExample_OnMessageReceived;

	/* Use the synchronous API to subscribe - It is a blocking call and only
	 * returns when the subscribe operation is complete or a timeout occurs. */
	xResult = IotMqtt_SubscribeSync( xMQTTConnection,
									 &( xMQTTSubscription ),
									 1, /* We are subscribing to one topic filter. */
									 0, /* flags - currently ignored. */
									 mqttexampleMQTT_TIMEOUT_MS );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvMQTTPublish( void )
{
IotMqttError_t xResult;
IotMqttPublishInfo_t xMQTTPublishInfo;

	/* Publish a message with QoS1 on the mqttexampleTOPIC topic. Since we are
	 * subscribed to the same topic, the MQTT broker will send the same message
	 * back to us. It is verified in the publish callback. */
	xMQTTPublishInfo.qos = IOT_MQTT_QOS_1;
	xMQTTPublishInfo.retain = false;
	xMQTTPublishInfo.pTopicName = mqttexampleTOPIC;
	xMQTTPublishInfo.topicNameLength = ( uint16_t ) strlen( mqttexampleTOPIC );
	xMQTTPublishInfo.pPayload = mqttexampleMESSAGE;
	xMQTTPublishInfo.payloadLength = strlen( mqttexampleMESSAGE );
	xMQTTPublishInfo.retryMs = mqttexamplePUBLISH_RETRY_MS;
	xMQTTPublishInfo.retryLimit = mqttexamplePUBLISH_RETRY_LIMIT;

	/* Use the synchronous API to publish - It is a blocking call and only
	 * returns when the publish operation is complete or a timeout occurs. */
	xResult = IotMqtt_PublishSync( xMQTTConnection,
								   &( xMQTTPublishInfo ),
								   0, /* flags - currently ignored. */
								   mqttexampleMQTT_TIMEOUT_MS );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvMQTTUnsubscribe( void )
{
IotMqttError_t xResult;
IotMqttSubscription_t xMQTTSubscription;

	/* Unsubscribe from the mqttexampleTOPIC topic filter. */
	xMQTTSubscription.pTopicFilter = mqttexampleTOPIC;
	xMQTTSubscription.topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );

	/* The following members of the IotMqttSubscription_t are ignored by the
	 * unsubscribe operation. Just initialize them to avoid "use of uninitialized
	 * variable" warnings. */
	xMQTTSubscription.qos = IOT_MQTT_QOS_1;
	xMQTTSubscription.callback.pCallbackContext = NULL;
	xMQTTSubscription.callback.function = NULL;

	/* Use the synchronous API to unsubscribe - It is a blocking call and only
	 * returns when the unsubscribe operation is complete or a timeout occurs. */
	xResult = IotMqtt_UnsubscribeSync( xMQTTConnection,
									   &( xMQTTSubscription ),
									   1, /* We are unsubscribing from one topic filter. */
									   0, /* flags - currently ignored. */
									   mqttexampleMQTT_TIMEOUT_MS );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvInitialiseLibraries( void )
{
IotTaskPoolError_t xTaskPoolResult;
IotMqttError_t xResult;
IotNetworkError_t xNetworkResult;

	/* The MQTT library needs a task pool, so create the system task pool. */
	xTaskPoolResult = IotTaskPool_CreateSystemTaskPool( &( xTaskPoolParameters ) );
	configASSERT( xTaskPoolResult == IOT_TASKPOOL_SUCCESS );

	/* Initialize the network stack abstraction for FreeRTOS. */
	xNetworkResult = IotNetworkFreeRTOS_Init();
	configASSERT( xNetworkResult == IOT_NETWORK_SUCCESS );

	/* MQTT library must be initialized before it can be used. This is just one
	 * time initialization. */
	xResult = IotMqtt_Init();
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/
