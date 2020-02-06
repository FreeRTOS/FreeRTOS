/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Standard inclues. */
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* IoT SDK includes. */
#include "iot_mqtt.h"
#include "iot_taskpool.h"
#include "platform/iot_network_freertos.h"

/**
 * @brief The keep-alive interval used for this example.
 *
 * An MQTT ping request will be sent periodically at this interval.
 */
#define mqttexampleKEEP_ALIVE_SECONDS		( 60 )

/**
 * @brief The timeout for MQTT operations in this example.
 */
#define mqttexampleMQTT_TIMEOUT_MS			( 50000 )

/**
 * @brief The MQTT client identifier used in this example.
 */
#define mqttexampleCLIENT_IDENTIFIER		"mqttexampleclient"

const char *pcClientIdentifiers[] = { "AAA" };//, "BBB", "CCC", "DDD", "EEE", "FFF", "GGG", "HHH", "III", "JJJ" };

/**
 * @brief Details of the MQTT broker to connect to.
 *
 * @note This example does not use TLS and therefore won't work with AWS IoT.
 *
 */
#define mqttexampleMQTT_BROKER_ENDPOINT		"test.mosquitto.org"
#define mqttexampleMQTT_BROKER_PORT			1883

/**
 * @brief The topic to subscribe and publish to in the example.
 */
#define mqttexampleTOPIC					"example/topic"

/**
 * @brief The MQTT message published in this example.
 */
#define mqttexampleMESSAGE					"Hello World!"

/**
 * @brief Paramters to control the retry behaviour in case a QoS1 publish
 * message gets lost.
 *
 * Retry every minutes up to a maximum of 5 retries.
 */
#define mqttexamplePUBLISH_RETRY_MS			( 1000 )
#define mqttexamplePUBLISH_RETRY_LIMIT		( 5 )

/**
 * @brief The bit which is set in the demo task's notification value from the
 * disconnect callback to inform the demo task about the MQTT disconnect.
 */
#define mqttexampleDISCONNECTED_BIT			( 1UL << 0UL )

/**
 * @brief The bit which is set in the demo task's notification value from the
 * publish callback to inform the demo task about the message received from the
 * MQTT broker.
 */
#define mqttexampleMESSAGE_RECEIVED_BIT		( 1UL << 1UL )
/*-----------------------------------------------------------*/

/**
 * @brief Parameters used to create the system task pool.
 */
static const IotTaskPoolInfo_t xTaskPoolParameters = {
														/* Minimum number of threads in a task pool.
														 * Note the slimmed down version of the task
														 * pool used by this library does not autoscale
														 * the number of tasks in the pool so in this
														 * case this sets the number of tasks in the
														 * pool. */
														2,
														/* Maximum number of threads in a task pool.
														 * Note the slimmed down version of the task
														 * pool used by this library does not autoscale
														 * the number of tasks in the pool so in this
														 * case this parameter is just ignored. */
														2,
														/* Stack size for every task pool thread - in
														 * bytes, hence multiplying by the number of bytes
														 * in a word as configMINIMAL_STACK_SIZE is
														 * specified in words. */
														configMINIMAL_STACK_SIZE * sizeof( portSTACK_TYPE ),
														/* Priority for every task pool thread. */
														tskIDLE_PRIORITY,
													 };
/*-----------------------------------------------------------*/

/**
 * @brief The task used to demonstrate the MQTT API.
 *
 * @param[in] pvParameters Parmaters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvMQTTDemoTask( void *pvParameters );

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
 * @brief Connects to the MQTT broker as specified in mqttexampleMQTT_BROKER_ENDPOINT
 * and mqttexampleMQTT_BROKER_PORT.
 *
 * @note This example does not use TLS and therefore will not work with MQTT.
 */
static void prvMQTTConnect( IotMqttConnection_t *xMQTTConnection, const char *pcClientID );

/**
 * @brief Subscribes to pcTopicString.
 */
static void prvMQTTSubscribe( IotMqttConnection_t xMQTTConnection, const char * const pcTopicString );

/**
 * @brief Publishes a messages mqttexampleMESSAGE on mqttexampleTOPIC topic.
 */
static void prvMQTTPublish( IotMqttConnection_t xMQTTConnection, const char * const pcTopicString );

/**
 * @brief Unsubscribes from the mqttexampleTOPIC topic.
 */
static void prvMQTTUnsubscribe( IotMqttConnection_t xMQTTConnection, const char * const pcTopicString );

/**
 * @brief Disconnects from the MQTT broker gracefully by sending an MQTT
 * DISCONNECT message.
 */
static void prvMQTTDisconnect( IotMqttConnection_t xMQTTConnection );
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

	/* Ensure that the message is received on the expected topic. */
//	configASSERT( pxCallbackParams->u.message.info.topicNameLength == strlen( mqttexampleTOPIC ) );
//	configASSERT( strncmp( pxCallbackParams->u.message.info.pTopicName,
//						   mqttexampleTOPIC,
//						   strlen( mqttexampleTOPIC ) ) == 0 );

	/* Ensure that the expected message is received. */
	configASSERT( pxCallbackParams->u.message.info.payloadLength == strlen( mqttexampleMESSAGE ) );
	configASSERT( strncmp( pxCallbackParams->u.message.info.pPayload,
						   mqttexampleMESSAGE,
						   strlen( mqttexampleMESSAGE ) ) == 0 );

	/* Ensure that the message QoS is as expected. */
	configASSERT( pxCallbackParams->u.message.info.qos == IOT_MQTT_QOS_1 );

	/* Although this print uses the constants rather than the data from the
	 * message payload the asserts above have already checked the message
	 * payload equals the constants, and it is more efficient not to have to
	 * worry about lengths in the print. */
	configPRINTF( ( "Received %s on the topic %s\r\n", mqttexampleMESSAGE, mqttexampleTOPIC ) );

	/* Inform the demo task about the message received from the MQTT broker. */
	xTaskNotify( xDemoTaskHandle,
				 mqttexampleMESSAGE_RECEIVED_BIT,
				 eSetBits /* Set the mqttexampleMESSAGE_RECEIVED_BIT in the demo task's notification value. */
				);
}
/*-----------------------------------------------------------*/

void vStartSimpleMQTTDemo( void )
{
uint32_t x;
const uint32_t ulMax_x = sizeof( pcClientIdentifiers ) / sizeof( char * );

	/* This example uses a single application task, which in turn is used to
	 * connect, subscribe, publish, unsubscribe and disconnect from the MQTT
	 * broker. */
for( x = 0; x < ulMax_x; x++ )
{
	xTaskCreate( prvMQTTDemoTask,			/* Function that implements the task. */
				 "MQTTDemo",				/* Text name for the task - only used for debugging. */
				 configMINIMAL_STACK_SIZE,	/* Size of stack (in words, not bytes) to allocate for the task. */
				 ( void * ) x,						/* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,			/* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );					/* Used to pass out a handle to the created task - not used in this case. */
}
}
/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void *pvParameters )
{
IotMqttError_t xResult;
uint32_t ulNotificationValue = 0, ulPublishCount;
uint32_t ulMaxPublishCount = 0UL;
const TickType_t xNoDelay = ( TickType_t ) 1;
IotMqttConnection_t xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;
uint32_t ulTaskNumber = ( uint32_t ) pvParameters, x;
char cTopicString[ sizeof( mqttexampleTOPIC ) + 5 ];//_RB_ Access by other tasks so must be persistant and will cause memory faults on memory protected systems.
#pragma message ("Access by other tasks so must be persistant and will cause memory faults on memory protected systems.")

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* The MQTT library needs a task pool, so create the system task pool. */
	xResult = IotTaskPool_CreateSystemTaskPool( &( xTaskPoolParameters ) );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* MQTT library must be initialized before it can be used. This is just one
	 * time initialization. */
	xResult = IotMqtt_Init();
	configASSERT( xResult == IOT_MQTT_SUCCESS );

	/* Create a topic string that is unique to the MQTT connection created by
	this task. */
	snprintf( cTopicString, sizeof( cTopicString ), "%s/%s", mqttexampleTOPIC, pcClientIdentifiers[ ulTaskNumber ] );

	for( ; ; )
	{
		/* Don't expect any notifications to be pending yet. */
		ulNotificationValue = ulTaskNotifyTake( pdTRUE, xNoDelay );
		configASSERT( ulNotificationValue == 0 );


		/****************************** Connect. ******************************/

		/* Establish a connection to the MQTT broker. This example connects to
		 * the MQTT broker as specified in mqttexampleMQTT_BROKER_ENDPOINT and
		 * mqttexampleMQTT_BROKER_PORT at the top of this file. Please change
		 * it to the MQTT broker you want to connect to. Note that this example
		 * does not use TLS and therefore will not work with AWS IoT. */
		prvMQTTConnect( &xMQTTConnection, pcClientIdentifiers[ ulTaskNumber ] );
		configPRINTF( ( "Connected to %s\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );


		/**************************** Subscribe. ******************************/

		/* The client is now connected to the broker. Subscribe to the topic
		 * as specified in mqttexampleTOPIC at the top of this file.  This
		 * client will then publish to the same topic it subscribed to, so will
		 * expect all the messages it sends to the broker to be sent back to it
		 * from the broker. */
		prvMQTTSubscribe( xMQTTConnection, cTopicString );
		configPRINTF( ( "Subscribed to the topic %s\r\n", cTopicString ) );


		/*********************** Publish 5 messages. **************************/

		/* Publish a few messages while connected. */
		for( x = 0; x < ( ulTaskNumber + 1UL ); x++ )
		{
			ulMaxPublishCount = uxRand();
		}

		/* Cap ulMaxPublishCount but ensure it is not zero. */
		ulMaxPublishCount %= 10UL;
		ulMaxPublishCount++;

		for( ulPublishCount = 0; ulPublishCount < ulMaxPublishCount; ulPublishCount++ )
		{
			/* Publish a message on the mqttexampleTOPIC topic as specified at
			 * the top of this file. */
			prvMQTTPublish( xMQTTConnection, cTopicString );
			configPRINTF( ( "Published %s on the topic %s\r\n", mqttexampleMESSAGE, cTopicString ) );

			/* Since we are subscribed to the same topic as we published on, we
			 * will get the same message back from the MQTT broker. Wait for the
			 * message to be received which is informed to us by the publish
			 * callback (prvExample_OnMessageReceived) by setting the
			 * mqttexampleMESSAGE_RECEIVED_BIT in this task's notification
			 * value. Note that the bit is cleared in the task's notification
			 * value to ensure that it is ready for next message. */
			xTaskNotifyWait( 0UL, /* Don't clear any bits on entry. */
							 mqttexampleMESSAGE_RECEIVED_BIT, /* Clear bit on exit. */
							 &( ulNotificationValue ), /* Obtain the notification value. */
							 pdMS_TO_TICKS( mqttexampleMQTT_TIMEOUT_MS ) );
			configASSERT( ( ulNotificationValue & mqttexampleMESSAGE_RECEIVED_BIT ) == mqttexampleMESSAGE_RECEIVED_BIT );
		}


		/******************* Unsubscribe and Disconnect. **********************/

		/* Unsubscribe from the topic mqttexampleTOPIC and disconnect
		 * gracefully. */
		prvMQTTUnsubscribe( xMQTTConnection, cTopicString );
		prvMQTTDisconnect( xMQTTConnection );
		configPRINTF( ( "Disconnected from %s\r\n\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );

		/* Wait for the disconnect operation to complete which is informed to us
		 * by the disconnect callback (prvExample_OnDisconnect)by setting
		 * the mqttexampleDISCONNECTED_BIT in this task's notification value.
		 * Note that the bit is cleared in the task's notification value to
		 * ensure that it is ready for the next run. */
		xTaskNotifyWait( 0UL, /* Don't clear any bits on entry. */
						 mqttexampleDISCONNECTED_BIT, /* Clear bit on exit. */
						 &( ulNotificationValue ), /* Obtain the notification value. */
						 pdMS_TO_TICKS( mqttexampleMQTT_TIMEOUT_MS ) );
		configASSERT( ( ulNotificationValue & mqttexampleDISCONNECTED_BIT ) == mqttexampleDISCONNECTED_BIT );

		/* Wait for some time between two iterations to ensure that we do not
		 * bombard the public test mosquitto broker. */
		configPRINTF( ( "prvMQTTDemoTask() completed an iteration without hitting an assert. Total free heap is %u\r\n\r\n", xPortGetFreeHeapSize() ) );
//		vTaskDelay( pdMS_TO_TICKS( 5000 ) );
	}
}
/*-----------------------------------------------------------*/

static void prvMQTTConnect( IotMqttConnection_t *xMQTTConnection, const char *pcClientID )
{
IotMqttError_t xResult;
IotNetworkServerInfo_t xMQTTBrokerInfo;
IotMqttNetworkInfo_t xNetworkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;
IotMqttConnectInfo_t xConnectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
static char c[ 10 ];
static int id = 0;

	/******************* Broker information setup. **********************/

	xMQTTBrokerInfo.pHostName = mqttexampleMQTT_BROKER_ENDPOINT;
	xMQTTBrokerInfo.port = mqttexampleMQTT_BROKER_PORT;


	/******************* Network information setup. **********************/

	/* No connection to the MQTT broker has been established yet and we want to
	 * establish a new connection. */
	xNetworkInfo.createNetworkConnection = true;
	xNetworkInfo.u.setup.pNetworkServerInfo = &( xMQTTBrokerInfo );

	/* This example does not use TLS and therefore pNetworkCredentialInfo must
	 * be set to NULL. */
	xNetworkInfo.u.setup.pNetworkCredentialInfo = NULL;

	/* Use FreeRTOS+TCP network. */
	xNetworkInfo.pNetworkInterface = IOT_NETWORK_INTERFACE_FREERTOS;

	/* Setup the callback which is called when the MQTT connection is
	 * disconnected. The task handle is passed as the callback context which
	 * is used by the callback to send a task notification to this task.*/
	xNetworkInfo.disconnectCallback.pCallbackContext = ( void * ) xTaskGetCurrentTaskHandle();
	xNetworkInfo.disconnectCallback.function = prvExample_OnDisconnect;


	/****************** MQTT Connection information setup. ********************/

	/* Set this flag to true if connecting to the AWS IoT MQTT broker. This
	 * example does not use TLS and therefore won't work with AWS IoT. */
	xConnectInfo.awsIotMqttMode = false;

	/* Start with a clean session i.e. direct the MQTT broker to discard any
	 * previous session data. Also, establishing a connection with clean session
	 * will ensure that the broker does not store any data when this client
	 * gets disconnected. */
	xConnectInfo.cleanSession = true;

	/* Since we are starting with a clean session, there are no previous
	 * subscriptions to be restored. */
	xConnectInfo.pPreviousSubscriptions = NULL;
	xConnectInfo.previousSubscriptionCount = 0;

	/* We do not want to publish Last Will and Testament (LWT) message if the
	 * client gets disconnected. */
	xConnectInfo.pWillInfo = NULL;

	/* Send an MQTT PING request every minute to keep the connection open if
	there is no other MQTT traffic. */
	xConnectInfo.keepAliveSeconds = mqttexampleKEEP_ALIVE_SECONDS;

	/* The client identifier is used to uniquely identify this MQTT client to
	 * the MQTT broker.  In a production device the identifier can be something
	 * unique, such as a device serial number. */
	xConnectInfo.pClientIdentifier = pcClientID;
	xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( pcClientID );

	/* This example does not use any authentication and therefore username and
	 * password fields are not used. */
	xConnectInfo.pUserName = NULL;
	xConnectInfo.userNameLength = 0;
	xConnectInfo.pPassword = NULL;
	xConnectInfo.passwordLength = 0;

	/* Establish the connection to the MQTT broker - It is a blocking call and
	will return only when connection is complete or a timeout occurs. */
	xResult = IotMqtt_Connect( &( xNetworkInfo ),
							   &( xConnectInfo ),
							   mqttexampleMQTT_TIMEOUT_MS,
							   xMQTTConnection );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvMQTTSubscribe( IotMqttConnection_t xMQTTConnection, const char * const pcTopicString )
{
IotMqttError_t xResult;
IotMqttSubscription_t xMQTTSubscription;

	/* Subscribe to the mqttexampleTOPIC topic filter. The task handle is passed
	 * as the callback context which is used by the callback to send a task
	 * notification to this task.*/
	xMQTTSubscription.qos = IOT_MQTT_QOS_1;
	xMQTTSubscription.pTopicFilter = pcTopicString;
	xMQTTSubscription.topicFilterLength = ( uint16_t ) strlen( pcTopicString );
	xMQTTSubscription.callback.pCallbackContext = ( void * ) xTaskGetCurrentTaskHandle();
	xMQTTSubscription.callback.function = prvExample_OnMessageReceived;

	/* Use the synchronous API to subscribe - It is a blocking call and only
	 * returns when the subscribe operation is complete or a timeout occurs. */
	xResult = IotMqtt_TimedSubscribe( xMQTTConnection,
									  &( xMQTTSubscription ),
									  1, /* We are subscribing to one topic filter. */
									  0, /* flags - currently ignored. */
									  mqttexampleMQTT_TIMEOUT_MS );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvMQTTPublish( IotMqttConnection_t xMQTTConnection, const char * const pcTopicString )
{
IotMqttError_t xResult;
IotMqttPublishInfo_t xMQTTPublishInfo;

	/* Publish a message with QoS1 on the mqttexampleTOPIC topic. Since we are
	 * subscribed to the same topic, the MQTT broker will send the same message
	 * back to us. It is verified in the publish callback. */
	xMQTTPublishInfo.qos = IOT_MQTT_QOS_1;
	xMQTTPublishInfo.retain = false;
	xMQTTPublishInfo.pTopicName = pcTopicString;
	xMQTTPublishInfo.topicNameLength = ( uint16_t ) strlen( pcTopicString );
	xMQTTPublishInfo.pPayload = mqttexampleMESSAGE;
	xMQTTPublishInfo.payloadLength = strlen( mqttexampleMESSAGE );
	xMQTTPublishInfo.retryMs = mqttexamplePUBLISH_RETRY_MS;
	xMQTTPublishInfo.retryLimit = mqttexamplePUBLISH_RETRY_LIMIT;

	/* Use the synchronous API to publish - It is a blocking call and only
	 * returns when the publish operation is complete or a timeout occurs. */
	xResult = IotMqtt_TimedPublish( xMQTTConnection,
									&( xMQTTPublishInfo ),
									0, /* flags - currently ignored. */
									mqttexampleMQTT_TIMEOUT_MS );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvMQTTUnsubscribe( IotMqttConnection_t xMQTTConnection, const char * const pcTopicString )
{
IotMqttError_t xResult;
IotMqttSubscription_t xMQTTSubscription;

	/* Unsubscribe from the mqttexampleTOPIC topic filter. */
	xMQTTSubscription.pTopicFilter = pcTopicString;
	xMQTTSubscription.topicFilterLength = ( uint16_t ) strlen( pcTopicString );
	/* The following members of the IotMqttSubscription_t are ignored by the
	 * unsubscribe operation. Just initialize them to avoid "use of uninitialized
	 * variable" warnings. */
	xMQTTSubscription.qos = IOT_MQTT_QOS_1;
	xMQTTSubscription.callback.pCallbackContext = NULL;
	xMQTTSubscription.callback.function = NULL;

	/* Use the synchronous API to unsubscribe - It is a blocking call and only
	 * returns when the unsubscribe operation is complete or a timeout occurs. */
	xResult = IotMqtt_TimedUnsubscribe( xMQTTConnection,
										&( xMQTTSubscription ),
										1, /* We are unsubscribing from one topic filter. */
										0, /* flags - currently ignored. */
										mqttexampleMQTT_TIMEOUT_MS );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvMQTTDisconnect( IotMqttConnection_t xMQTTConnection )
{
	/* Send a MQTT DISCONNECT packet to the MQTT broker to do a graceful
	 * disconnect. */
	IotMqtt_Disconnect( xMQTTConnection,
						0 /* flags - 0 means a graceful disconnect by sending MQTT DISCONNECT. */
						);
}
/*-----------------------------------------------------------*/
