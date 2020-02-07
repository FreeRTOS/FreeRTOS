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
 * Proof of Concept for use of MQTT light weight serializer API.
 * Light weight serializer API lets user to serialize and
 * deserialize MQTT messages into user provided buffer.
 * This API allows use of statically allocated buffer.
 *
 * Example shown below uses this API to create MQTT messages and
 * and send them over connection established using FreeRTOS sockets.
 * The example is single threaded and uses statically allocated memory.
 *
 * !!! NOTE !!!
 * This is work in progress to show how light weight serializer
 * API can be used. This is not a complete demo, and should not
 * be treated as production ready code.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* IoT SDK includes. */
#include "iot_mqtt.h"
#include "iot_mqtt_serialize.h"
#include "platform/iot_network_freertos.h"

/* Demo Specific configs. */
#include "mqtt_demo_profile.h"


/**
 * @brief Time to wait between each cycle of the demo implemented by prvMQTTDemoTask().
 */
#define mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS	( pdMS_TO_TICKS( 5000 ) )

/**
 * @brief Time to wait before sending ping request to keep MQTT connection alive.
 */
#define mqttexampleKEEP_ALIVE_DELAY					( pdMS_TO_TICKS( 1000 ) )


/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.
 */
#define mqttexampleCLIENT_IDENTIFIER	   mqttdemoprofileCLIENT_IDENTIFIER

/**
 * @brief Details of the MQTT broker to connect to.
 */
#define mqttexampleMQTT_BROKER_ENDPOINT	   mqttdemoprofileBROKER_ENDPOINT

/**
 * @brief The port to use for the demo.
 */
#define mqttexampleMQTT_BROKER_PORT		   mqttdemoprofileBROKER_PORT

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
#define mqttexampleMESSAGE				   "Hello Light Weight MQTT World!"

/**
 * @brief Dimensions a file scope buffer currently used to send and receive MQTT data from a
 * socket
 */
#define mqttexampleSHARED_BUFFER_SIZE	   500

/*-----------------------------------------------------------*/

/**
 * @brief MQTT Protocol constants used by this demo.
 * These types are defined in internal MQTT include files.
 * For light-weight demo application, only a few are needed, therefore
 * they are redefined here so that internal files need not be included.
 */

/*  MQTT Control Packet Types.*/
#define MQTT_PACKET_TYPE_CONNACK	   ( ( uint8_t ) 0x20U ) /**< @brief CONNACK (server-to-client). */
#define MQTT_PACKET_TYPE_PUBLISH	   ( ( uint8_t ) 0x30U ) /**< @brief PUBLISH (bi-directional). */
#define MQTT_PACKET_TYPE_SUBACK		   ( ( uint8_t ) 0x90U ) /**< @brief SUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_UNSUBACK	   ( ( uint8_t ) 0xb0U ) /**< @brief UNSUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_PINGRESP	   ( ( uint8_t ) 0xd0U ) /**< @brief PINGRESP (server-to-client). */
/* MQTT Fixed Packet Sizes */
#define MQTT_PACKET_DISCONNECT_SIZE	   ( ( uint8_t ) 2 )     /**< @brief Size of DISCONNECT packet. */
#define MQTT_PACKET_PINGREQ_SIZE	   ( ( uint8_t ) 2 )     /**< @brief Size of PINGREQ packet. */

/*-----------------------------------------------------------*/

/**
 * @brief The task used to demonstrate the MQTT API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvMQTTDemoTask( void * pvParameters );

/**
 * @brief Creates a TCP connection to the MQTT broker as specified in
 * mqttexampleMQTT_BROKER_ENDPOINT and mqttexampleMQTT_BROKER_PORT.
 *
 * @return On success the socket connected to the MQTT broker is returned.  Otherwise
 * FREERTOS_INVALID_SOCKET is returned.
 *
 */
static Socket_t prvCreateTCPConnectionToBroker( void );

/**
 * @brief Sends an MQTT Connect packet over the already connected TCP socket.
 *
 * @param xMQTTSocketis a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 * @return IOT_MQTT_SUCCESS is returned if the reply is a valid connection
 * acknowledgeable (CONNACK) packet, otherwise an error code is returned.
 */
static IotMqttError_t prvCreateMQTTConnectionWithBroker( Socket_t xMQTTSocket );

/**
 * @brief Performs a graceful shutdown and close of the socket passed in as its
 * parameter.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 */
static void prvGracefulShutDown( Socket_t xSocket );

/**
 * @brief Subscribes to the topic as specified in mqttexampleTOPIC.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 * @return IOT_MQTT_SUCCESS is returned if the
 * subscription is successful, otherwise an error code is returned.
 */
static IotMqttError_t prvMQTTSubscribeToTopic( Socket_t xMQTTSocket );

/**
 * @brief  Publishes a messages mqttexampleMESSAGE on mqttexampleTOPIC topic.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 * @return IOT_MQTT_SUCCESS is returned if Publish is successful,
 * otherwise an error code is returned.
 */
static IotMqttError_t prvMQTTPublishToTopic( Socket_t xMQTTSocket );

/**
 * @brief  Process Incoming Publish.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 * @return #IOT_MQTT_SUCCESS is returned if the processing is successful,
 * otherwise an error code is returned.
 */
static IotMqttError_t prvMQTTProcessIncomingPublish( Socket_t xMQTTSocket );

/**
 * @brief Unsubscribes from the previously subscribed topic as specified
 * in mqttexampleTOPIC.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 * @return IOT_MQTT_SUCCESS is returned if the
 * unsubscribe is successful, otherwise an error code is returned.
 */
static IotMqttError_t prvMQTTUnsubscribeFromTopic( Socket_t xMQTTSocket );

/**
 * @brief Send MQTT Ping Request to broker and receive response.
 * Ping request is used to keep connection to broker alive.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 * @return IOT_MQTT_SUCCESS is returned if the successful Ping Response is received.
 * otherwise an error code is returned.
 */
static IotMqttError_t prvMQTTKeepAlive( Socket_t xMQTTSocket );

/**
 * @brief Disconnect From MQTT Broker.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 * @return IOT_MQTT_SUCCESS is returned if the disconnect is successful,
 * otherwise an error code is returned.
 */
static IotMqttError_t prvMQTTDisconnect( Socket_t xMQTTSocket );


/*-----------------------------------------------------------*/

/**
 * @brief Function to receive next byte from network,
 * The declaration must match IotMqttGetNextByte_t.
 *
 * @param[in] pvContext Network Connection context. Implementation in this
 * file uses FreeRTOS socket.
 * @param[in, out] pNextBye Pointer to buffer where the byte will be stored.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_TIMEOUT
 */

IotMqttError_t getNextByte( void * pvContext,
							uint8_t * pNextByte );

/*-----------------------------------------------------------*/

/* @brief Static memory buffer used for sending and receiving MQTT messages */
static uint8_t ucSharedBuffer[ mqttexampleSHARED_BUFFER_SIZE ];

/*-----------------------------------------------------------*/

/*
 * @brief Task for Light Weight MQTT Serializer API Proof of Concept.
 * To run the proof of concept example, in main.c, in function vApplicationIPNetworkEventHook(),
 * replace vStartSimpleMQTTDemo() with vApplicationIPNetworkEventHook().
 */
void vStartLightWeightMQTTDemo( void )
{
TickType_t xShortDelay = ( TickType_t ) pdMS_TO_TICKS( ( TickType_t ) 500 );

	/* Wait a short time to allow receipt of the ARP replies. */
	vTaskDelay( xShortDelay );

	/* This example uses a single application task, which in turn is used to
	 * connect, subscribe, publish, unsubscribe and disconnect from the MQTT
	 * broker. */
	xTaskCreate( prvMQTTDemoTask,          /* Function that implements the task. */
				 "MQTTLWDemo",             /* Text name for the task - only used for debugging. */
				 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,                     /* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvGracefulShutDown( Socket_t xSocket )
{
uint8_t ucDummy[ 20 ];
const TickType_t xShortDelay = pdMS_TO_MIN_TICKS( 250 );

	if( xSocket != ( Socket_t ) 0 )
	{
		if( xSocket != FREERTOS_INVALID_SOCKET )
		{
			/* Initiate graceful shutdown. */
			FreeRTOS_shutdown( xSocket, FREERTOS_SHUT_RDWR );

			/* Wait for the socket to disconnect gracefully (indicated by FreeRTOS_recv()
			 * returning a FREERTOS_EINVAL error) before closing the socket. */
			while( FreeRTOS_recv( xSocket, ucDummy, sizeof( ucDummy ), 0 ) >= 0 )
			{
				/* Wait for shutdown to complete.  If a receive block time is used then
				 * this delay will not be necessary as FreeRTOS_recv() will place the RTOS task
				 * into the Blocked state anyway. */
				vTaskDelay( xShortDelay );

				/* Note ? real applications should implement a timeout here, not just
				 * loop forever. */
			}

			/* The socket has shut down and is safe to close. */
			FreeRTOS_closesocket( xSocket );
		}
	}
}
/*-----------------------------------------------------------*/

IotMqttError_t getNextByte( void * pvContext,
							uint8_t * pNextByte )
{
Socket_t xMQTTSocket = ( Socket_t ) pvContext;
BaseType_t receivedBytes;
IotMqttError_t result;

	/* Receive one byte from network */
	receivedBytes = FreeRTOS_recv( xMQTTSocket, ( void * ) pNextByte, sizeof( uint8_t ), 0 );

	if( receivedBytes == sizeof( uint8_t ) )
	{
		result = IOT_MQTT_SUCCESS;
	}
	else
	{
		result = IOT_MQTT_TIMEOUT;
	}

	return result;
}

/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void * pvParameters )
{
const TickType_t xNoDelay = ( TickType_t ) 0;
Socket_t xMQTTSocket;
IotMqttError_t xReturned;
uint32_t ulPublishCount = 0;
const uint32_t ulMaxPublishCount = 5UL;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	for( ; ; )
	{
		/* Don't expect any notifications to be pending yet. */
		configASSERT( ulTaskNotifyTake( pdTRUE, xNoDelay ) == 0 );

		/****************************** Connect. ******************************/

		/* Establish a TCP connection with the MQTT broker. This example connects to
		 * the MQTT broker as specified in mqttexampleMQTT_BROKER_ENDPOINT and
		 * mqttexampleMQTT_BROKER_PORT at the top of this file. */
		configPRINTF( ( "Create a TCP connection to %s\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
		xMQTTSocket = prvCreateTCPConnectionToBroker();
		configASSERT( xMQTTSocket != FREERTOS_INVALID_SOCKET );
		configPRINTF( ( "Connected to %s\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );

		/* Sends an MQTT Connect packet over the already connected TCP socket
		 * xMQTTSocket, then waits for and interprets the reply. IOT_MQTT_SUCCESS is
		 * returned if the reply is a valid connection acknowledgeable (CONNACK) packet,
		 * otherwise an error code is returned. */
		configPRINTF( ( "Creating an MQTT connection with %s\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
		xReturned = prvCreateMQTTConnectionWithBroker( xMQTTSocket );
		configASSERT( xReturned == IOT_MQTT_SUCCESS );
		configPRINTF( ( "Established an MQTT connection.\r\n" ) );

		/**************************** Subscribe. ******************************/

		/* The client is now connected to the broker. Subscribe to the topic
		 * as specified in mqttexampleTOPIC at the top of this file by sending a
		 * subscribe packet then waiting for a subscribe acknowledgment (SUBACK).
		 * This client will then publish to the same topic it subscribed to, so will
		 * expect all the messages it sends to the broker to be sent back to it
		 * from the broker. */
		configPRINTF( ( "Attempt to subscribed to the MQTT topic %s\r\n", mqttexampleTOPIC ) );
		xReturned = prvMQTTSubscribeToTopic( xMQTTSocket );
		configPRINTF( ( "Subscribed to the topic %s\r\n", mqttexampleTOPIC ) );

		/**************************** Publish. ******************************/
		/* Send publish for with QOS0, Process Keep alive */
		for( ulPublishCount = 0; ulPublishCount < ulMaxPublishCount; ulPublishCount++ )
		{
			configPRINTF( ( "Attempt to publish to the MQTT topic %s\r\n", mqttexampleTOPIC ) );
			xReturned = prvMQTTPublishToTopic( xMQTTSocket );
			configASSERT( xReturned == IOT_MQTT_SUCCESS );
			configPRINTF( ( "Publish successful to the topic %s\r\n", mqttexampleTOPIC ) );

			/* Process incoming publish echo, since application subscribed to the same topic
			 * broker will send publish message back to the application */
			configPRINTF( ( "Attempt to receive publish message from broker\r\n" ) );
			xReturned = prvMQTTProcessIncomingPublish( xMQTTSocket );
			configASSERT( xReturned == IOT_MQTT_SUCCESS );
			configPRINTF( ( "Successfully Received Publish message from broker\r\n" ) );

			/* Leave Connection Idle for some time */
			configPRINTF( ( "Keeping Connection Idle\r\n" ) );
			vTaskDelay( pdMS_TO_TICKS( mqttexampleKEEP_ALIVE_DELAY ) );
			/* Send Ping request to broker and receive ping response */
			configPRINTF( ( "Sending Ping Request to the broker\r\n" ) );
			xReturned = prvMQTTKeepAlive( xMQTTSocket );
			configASSERT( xReturned == IOT_MQTT_SUCCESS );
			configPRINTF( ( "Ping Response successfully received\r\n" ) );
		}

		/************************ Unsubscribe from the topic. **************************/
		configPRINTF( ( "Attempt to unsubscribe from the MQTT topic %s\r\n", mqttexampleTOPIC ) );
		xReturned = prvMQTTUnsubscribeFromTopic( xMQTTSocket );
		configASSERT( xReturned == IOT_MQTT_SUCCESS );
		configPRINTF( ( "Unsubscribe from the topic %s\r\n", mqttexampleTOPIC ) );

		/**************************** Disconnect. ******************************/

		/* Sends an MQTT Disconnect packet over the already connected TCP socket
		 * xMQTTSocket, then waits for and interprets the reply.  IOT_MQTT_SUCCESS is
		 * returned if the reply is a valid connection acknowledgeable (CONNACK) packet,
		 * otherwise an error code is returned. */

		configPRINTF( ( "Creating an MQTT connection with %s\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
		xReturned = prvMQTTDisconnect( xMQTTSocket );
		configASSERT( xReturned == IOT_MQTT_SUCCESS );
		configPRINTF( ( "Established an MQTT connection.\r\n" ) );
		/* Disconnect from broker. */
		prvGracefulShutDown( xMQTTSocket );

		/* Wait for some time between two iterations to ensure that we do not
		 * bombard the public test mosquitto broker. */
		configPRINTF( ( "prvMQTTDemoTask() completed an iteration successfully. Total free heap is %u\r\n", xPortGetFreeHeapSize() ) );
		configPRINTF( ( "Short delay before starting the next iteration.... \r\n\r\n" ) );
		vTaskDelay( pdMS_TO_TICKS( mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS ) );
	}
}
/*-----------------------------------------------------------*/

Socket_t prvCreateTCPConnectionToBroker( void )
{
Socket_t xMQTTSocket;
	struct freertos_sockaddr xBrokerAddress;
	uint32_t ulBrokerIPAddress;

	/* This is the socket used to connect to the MQTT broker. */
	xMQTTSocket = FreeRTOS_socket( FREERTOS_AF_INET,
								   FREERTOS_SOCK_STREAM,
								   FREERTOS_IPPROTO_TCP );

	configASSERT( xMQTTSocket != FREERTOS_INVALID_SOCKET );

	/* Locate then connect to the MQTT broker. */
	ulBrokerIPAddress = FreeRTOS_gethostbyname( mqttexampleMQTT_BROKER_ENDPOINT );

	if( ulBrokerIPAddress != 0 )
	{
		xBrokerAddress.sin_port = FreeRTOS_htons( mqttexampleMQTT_BROKER_PORT );
		xBrokerAddress.sin_addr = ulBrokerIPAddress;

		if( FreeRTOS_connect( xMQTTSocket, &xBrokerAddress, sizeof( xBrokerAddress ) ) != 0 )
		{
			/* Could not connect so delete socket and return an error. */
			FreeRTOS_closesocket( xMQTTSocket );
			xMQTTSocket = FREERTOS_INVALID_SOCKET;
		}
	}

	return xMQTTSocket;
}
/*-----------------------------------------------------------*/

static IotMqttError_t prvCreateMQTTConnectionWithBroker( Socket_t xMQTTSocket )
{
IotMqttConnectInfo_t xConnectInfo;
size_t xRemainingLength = 0;
size_t xPacketSize = 0;
IotMqttError_t xResult;
IotMqttPacketInfo_t xIncomingPacket;

	/* Many fields not used in this demo so start with everything at 0. */
	memset( ( void * ) &xConnectInfo, 0x00, sizeof( xConnectInfo ) );
	memset( ( void * ) &xIncomingPacket, 0x00, sizeof( xIncomingPacket ) );

	/* Start with a clean session i.e. direct the MQTT broker to discard any
	 * previous session data. Also, establishing a connection with clean session
	 * will ensure that the broker does not store any data when this client
	 * gets disconnected. */
	xConnectInfo.cleanSession = true;

	/* The client identifier is used to uniquely identify this MQTT client to
	 * the MQTT broker.  In a production device the identifier can be something
	 * unique, such as a device serial number. */
	xConnectInfo.pClientIdentifier = mqttexampleCLIENT_IDENTIFIER;
	xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( mqttexampleCLIENT_IDENTIFIER );

	/* Get size requirement for the connect packet */
	xResult = IotMqtt_GetConnectPacketSize( &xConnectInfo, &xRemainingLength, &xPacketSize );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
	/* Make sure the packet size is less than static buffer size */
	configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );
	/* Serialize MQTT connect packet into provided buffer */
	xResult = IotMqtt_SerializeConnect( &xConnectInfo, xRemainingLength, ucSharedBuffer, xPacketSize );
	configASSERT( xResult == IOT_MQTT_SUCCESS );

	if( FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 ) == ( BaseType_t ) xPacketSize )
	{
		/* Wait for the connection ack. TODO check the receive timeout value. */

		memset( ( void * ) &xIncomingPacket, 0x00, sizeof( IotMqttPacketInfo_t ) );

		/* Get packet type and remaining length of the received packet
		 * We cannot assume received data is the connection acknowledgment.
		 * Therefore this function reads type and remaining length of the
		 * received packet, before processing entire packet.
		 */
		xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
		configASSERT( xResult == IOT_MQTT_SUCCESS );
		configASSERT( xIncomingPacket.type == MQTT_PACKET_TYPE_CONNACK );
		configASSERT( xIncomingPacket.remainingLength <= mqttexampleSHARED_BUFFER_SIZE );

		if( FreeRTOS_recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 )
			== ( BaseType_t ) xIncomingPacket.remainingLength )
		{
			xIncomingPacket.pRemainingData = ucSharedBuffer;

			if( IotMqtt_DeserializeResponse( &xIncomingPacket ) != IOT_MQTT_SUCCESS )
			{
				xResult = IOT_MQTT_SERVER_REFUSED;
			}
		}
		else
		{
			configPRINTF( ( "Receive Failed while receiving MQTT ConnAck\n" ) );
			xResult = IOT_MQTT_NETWORK_ERROR;
		}
	}
	else
	{
		configPRINTF( ( "Send Failed while connecting to MQTT broker\n" ) );
		xResult = IOT_MQTT_NETWORK_ERROR;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

static IotMqttError_t prvMQTTSubscribeToTopic( Socket_t xMQTTSocket )
{
IotMqttError_t xResult;
IotMqttSubscription_t xMQTTSubscription[ 1 ];
size_t xRemainingLength = 0;
size_t xPacketSize = 0;
uint16_t usPacketIdentifier;
IotMqttPacketInfo_t xIncomingPacket;

	/* Some fields not used by this demo so start with everything at 0. */
	memset( ( void * ) &xMQTTSubscription, 0x00, sizeof( xMQTTSubscription ) );

	/* Subscribe to the mqttexampleTOPIC topic filter. This example subscribes to only one topic */
	xMQTTSubscription[ 0 ].qos = IOT_MQTT_QOS_0;
	xMQTTSubscription[ 0 ].pTopicFilter = mqttexampleTOPIC;
	xMQTTSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );

	xResult = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
												 xMQTTSubscription,
												 sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
												 &xRemainingLength, &xPacketSize );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
	/* Make sure the packet size is less than static buffer size */
	configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );

	/* Serialize subscribe into statically allocated ucSharedBuffer */
	xResult = IotMqtt_SerializeSubscribe( xMQTTSubscription,
										  sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
										  xRemainingLength,
										  &usPacketIdentifier,
										  ucSharedBuffer,
										  xPacketSize );

	configASSERT( xResult == IOT_MQTT_SUCCESS );

	if( FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 ) == ( BaseType_t ) xPacketSize )
	{
		/* Wait for the subscription ack. The socket is already connected to the MQTT broker, so
		 * publishes to this client can occur at any time and we cannot assume received
		 * data is the subscription acknowledgment.  Therefore this function is, at this
		 * time, doing what would otherwise be done wherever incoming packets are
		 * interpreted (in a callback, or whatever). */
		memset( ( void * ) &xIncomingPacket, 0x00, sizeof( IotMqttPacketInfo_t ) );
		xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
		configASSERT( xResult == IOT_MQTT_SUCCESS );
		configASSERT( xIncomingPacket.type == MQTT_PACKET_TYPE_SUBACK );
		configASSERT( xIncomingPacket.remainingLength <= mqttexampleSHARED_BUFFER_SIZE );

		/* Receive the remaining bytes. */
		if( FreeRTOS_recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 ) == ( BaseType_t ) xIncomingPacket.remainingLength )
		{
			xIncomingPacket.pRemainingData = ucSharedBuffer;

			if( IotMqtt_DeserializeResponse( &xIncomingPacket ) != IOT_MQTT_SUCCESS )
			{
				xResult = IOT_MQTT_BAD_RESPONSE;
			}
		}
		else
		{
			xResult = IOT_MQTT_NETWORK_ERROR;
		}
	}
	else
	{
		xResult = IOT_MQTT_NETWORK_ERROR;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

static IotMqttError_t prvMQTTPublishToTopic( Socket_t xMQTTSocket )
{
IotMqttError_t xResult;
IotMqttPublishInfo_t xMQTTPublishInfo;
size_t xRemainingLength = 0;
size_t xPacketSize = 0;
uint16_t usPacketIdentifier;
uint8_t * pusPacketIdentifierHigh;

	/* Some fields not used by this demo so start with everything at 0. */
	memset( ( void * ) &xMQTTPublishInfo, 0x00, sizeof( xMQTTPublishInfo ) );
	xMQTTPublishInfo.qos = IOT_MQTT_QOS_0;
	xMQTTPublishInfo.retain = false;
	xMQTTPublishInfo.pTopicName = mqttexampleTOPIC;
	xMQTTPublishInfo.topicNameLength = ( uint16_t ) strlen( mqttexampleTOPIC );
	xMQTTPublishInfo.pPayload = mqttexampleMESSAGE;
	xMQTTPublishInfo.payloadLength = strlen( mqttexampleMESSAGE );

	/* Find out length of Publish packet size. */
	xResult = IotMqtt_GetPublishPacketSize( &xMQTTPublishInfo, &xRemainingLength, &xPacketSize );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
	/* Make sure the packet size is less than static buffer size */
	configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );

	xResult = IotMqtt_SerializePublish( &xMQTTPublishInfo,
										xRemainingLength,
										&usPacketIdentifier,
										&pusPacketIdentifierHigh,
										ucSharedBuffer,
										xPacketSize );
	configASSERT( xResult == IOT_MQTT_SUCCESS );

	if( FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 ) != ( BaseType_t ) xPacketSize )
	{
		xResult = IOT_MQTT_NETWORK_ERROR;
	}
	else
	{
		/* Send success. Since in this case, we are using IOT_MQTT_QOS_0,
		 * there will not be any PubAck. Publish will be echoed back, which is processed
		 * in prvMQTTProcessIncomingPublish() */
		xResult = IOT_MQTT_SUCCESS;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

static IotMqttError_t prvMQTTProcessIncomingPublish( Socket_t xMQTTSocket )
{
IotMqttError_t xResult;
IotMqttPacketInfo_t xIncomingPacket;

	memset( ( void * ) &xIncomingPacket, 0x00, sizeof( IotMqttPacketInfo_t ) );
	xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
	configASSERT( ( xIncomingPacket.type & 0xf0 ) == MQTT_PACKET_TYPE_PUBLISH );
	configASSERT( xIncomingPacket.remainingLength <= mqttexampleSHARED_BUFFER_SIZE );

	/* Receive the remaining bytes. */
	if( FreeRTOS_recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 ) == ( BaseType_t ) xIncomingPacket.remainingLength )
	{
		xIncomingPacket.pRemainingData = ucSharedBuffer;

		if( IotMqtt_DeserializePublish( &xIncomingPacket ) != IOT_MQTT_SUCCESS )
		{
			xResult = IOT_MQTT_BAD_RESPONSE;
		}
		else
		{
			/* Process incoming Publish */
			configPRINTF( ( "Incoming QOS : %d\n", xIncomingPacket.pubInfo.qos ) );
			configPRINTF( ( "Incoming Publish Topic Name: %.*s\n", xIncomingPacket.pubInfo.topicNameLength, xIncomingPacket.pubInfo.pTopicName ) );
			configPRINTF( ( "Incoming Publish Message : %.*s\n", xIncomingPacket.pubInfo.payloadLength, xIncomingPacket.pubInfo.pPayload ) );
		}
	}
	else
	{
		xResult = IOT_MQTT_NETWORK_ERROR;
	}

	return xResult;
}

/*-----------------------------------------------------------*/

static IotMqttError_t prvMQTTUnsubscribeFromTopic( Socket_t xMQTTSocket )
{
IotMqttError_t xResult;
IotMqttSubscription_t xMQTTSubscription[ 1 ];
size_t xRemainingLength;
size_t xPacketSize;
uint16_t usPacketIdentifier;
IotMqttPacketInfo_t xIncomingPacket;

	/* Some fields not used by this demo so start with everything at 0. */
	memset( ( void * ) &xMQTTSubscription, 0x00, sizeof( xMQTTSubscription ) );

	/* Unsubscribe to the mqttexampleTOPIC topic filter. The task handle is passed
	 * as the callback context which is used by the callback to send a task
	 * notification to this task.*/
	xMQTTSubscription[ 0 ].qos = IOT_MQTT_QOS_0;
	xMQTTSubscription[ 0 ].pTopicFilter = mqttexampleTOPIC;
	xMQTTSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );

	xResult = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_UNSUBSCRIBE,
												 xMQTTSubscription,
												 sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
												 &xRemainingLength,
												 &xPacketSize );
	configASSERT( xResult == IOT_MQTT_SUCCESS );
	/* Make sure the packet size is less than static buffer size */
	configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );

	xResult = IotMqtt_SerializeUnsubscribe( xMQTTSubscription,
											sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
											xRemainingLength,
											&usPacketIdentifier,
											ucSharedBuffer,
											xPacketSize );
	configASSERT( xResult == IOT_MQTT_SUCCESS );

	if( FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 ) == ( BaseType_t ) xPacketSize )
	{
		/* Wait for the subscription ack. The socket is already connected to the MQTT broker, so
		 * publishes to this client can occur at any time and we cannot assume received
		 * data is the subscription acknowledgment.  Therefore this function is, at this
		 * time, doing what would otherwise be done wherever incoming packets are
		 * interpreted (in a callback, or whatever). */
		memset( ( void * ) &xIncomingPacket, 0x00, sizeof( IotMqttPacketInfo_t ) );
		xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
		configASSERT( xResult == IOT_MQTT_SUCCESS );
		configASSERT( xIncomingPacket.type == MQTT_PACKET_TYPE_UNSUBACK );
		configASSERT( xIncomingPacket.remainingLength <= sizeof( ucSharedBuffer ) );

		/* Receive the remaining bytes. */
		if( FreeRTOS_recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 ) == ( BaseType_t ) xIncomingPacket.remainingLength )
		{
			xIncomingPacket.pRemainingData = ucSharedBuffer;

			if( IotMqtt_DeserializeResponse( &xIncomingPacket ) != IOT_MQTT_SUCCESS )
			{
				xResult = IOT_MQTT_BAD_RESPONSE;
			}
		}
		else
		{
			xResult = IOT_MQTT_NETWORK_ERROR;
		}
	}
	else
	{
		xResult = IOT_MQTT_NETWORK_ERROR;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

static IotMqttError_t prvMQTTKeepAlive( Socket_t xMQTTSocket )
{
IotMqttError_t xResult;
IotMqttPacketInfo_t xIncomingPacket;

	/* PingReq is fixed length packet, therefore there is no need to calculate the size,
	 * just makes sure static buffer can accommodate ping request */

	configASSERT( MQTT_PACKET_PINGREQ_SIZE <= mqttexampleSHARED_BUFFER_SIZE );

	xResult = IotMqtt_SerializePingreq( ucSharedBuffer, MQTT_PACKET_PINGREQ_SIZE );
	configASSERT( xResult == IOT_MQTT_SUCCESS );

	if( FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, MQTT_PACKET_PINGREQ_SIZE, 0 ) == ( BaseType_t ) MQTT_PACKET_PINGREQ_SIZE )
	{
		memset( ( void * ) &xIncomingPacket, 0x00, sizeof( IotMqttPacketInfo_t ) );
		xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
		configASSERT( xResult == IOT_MQTT_SUCCESS );
		configASSERT( xIncomingPacket.type == MQTT_PACKET_TYPE_PINGRESP );
		configASSERT( xIncomingPacket.remainingLength <= sizeof( ucSharedBuffer ) );

		/* Receive the remaining bytes. */
		if( FreeRTOS_recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 )
			== ( BaseType_t ) xIncomingPacket.remainingLength )
		{
			xIncomingPacket.pRemainingData = ucSharedBuffer;

			if( IotMqtt_DeserializeResponse( &xIncomingPacket ) != IOT_MQTT_SUCCESS )
			{
				xResult = IOT_MQTT_BAD_RESPONSE;
			}
		}
		else
		{
			xResult = IOT_MQTT_NETWORK_ERROR;
		}
	}
	else
	{
		xResult = IOT_MQTT_NETWORK_ERROR;
	}

	return xResult;
}

/*-----------------------------------------------------------*/

static IotMqttError_t prvMQTTDisconnect( Socket_t xMQTTSocket )
{
IotMqttError_t xResult;

	/* Disconnect is fixed length packet, therefore there is no need to calculate the size,
	 * just makes sure static buffer can accommodate disconnect request */

	configASSERT( MQTT_PACKET_DISCONNECT_SIZE <= mqttexampleSHARED_BUFFER_SIZE );

	xResult = IotMqtt_SerializeDisconnect( ucSharedBuffer, MQTT_PACKET_DISCONNECT_SIZE );
	configASSERT( xResult == IOT_MQTT_SUCCESS );

	if( FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, MQTT_PACKET_DISCONNECT_SIZE, 0 ) == ( BaseType_t ) MQTT_PACKET_DISCONNECT_SIZE )
	{
		xResult = IOT_MQTT_SUCCESS;
	}
	else
	{
		xResult = IOT_MQTT_NETWORK_ERROR;
	}

	return xResult;
}
