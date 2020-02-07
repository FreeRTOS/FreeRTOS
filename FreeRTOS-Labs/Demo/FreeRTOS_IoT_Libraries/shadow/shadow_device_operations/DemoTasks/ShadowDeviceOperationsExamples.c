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

/* A device's Shadow is a JSON document that is used to store and retrieve
 * current state information for a device in AWS (Amazon Web Services) Cloud.
 * Please refer to the AWS documentation for more details about Device Shadow
 * service.
 * https://docs.aws.amazon.com/iot/latest/developerguide/iot-device-shadows.html
 *
 * This demo creates a single application task that loops through a set of
 * examples that demonstrates usage of Shadow library. Please find the list of
 * Shadow operations and callbacks used in this demo below.
 * Shadow Delete           - Deletes the Shadow document of the device.
 * Shadow Update           - Updates the Shadow document with JSON document
 *                           provided.
 * Shadow Delta Callback   - Callback to be invoked when Shadow document is
 *                           updated with different desired and reported
 *                           states.
 * Shadow Updated Callback - Callback to be invoked when a Shadow document is
 *                           updated.
 *
 * The demo program uses Shadow Update and Shadow Delta Callbacks to simulate
 * toggling a remote device's state. It sends a Shadow Update with a new
 * desired state and waits for the device to change its reported state in
 * Shadow Delta Callback as a response to the new desired state. In addition,
 * a Shadow Updated Callback is used to print the changing Shadow states.
 * Shadow Updates are done #shadowexampleUPDATE_COUNT times in each loop.At the
 * end of each loop Shadow document is deleted using Shadow Delete.
 *
 * In this demo both update to the desired state of Shadow document and
 * response to it by updating the reported state is done in the same
 * application. This is to illustrate the capability of the Shadow service and
 * library in a single demo. Ideally the update to the desired state can be
 * from an external application to control the state of the device. This demo
 * is meant to demonstrate the usage of different Shadow library APIs.
 *
 * The Shadow demo uses a MQTT connection to connect to Shadow Service in AWS.
 * Mutual authentication between AWS IoT MQTT Broker and Device is required to
 * run this demo. Please complete configurations in aws_iot_demo_profile.h for
 * mutual authentication.
 * More details for mutual authentication configuration can be found at
 * https://www.freertos.org/mqtt/preconfiguredexamplesMA.html
 *
 * Note: The parser used in this demo is specific for parsing AWS IoT document
 * received through a mutually authenticated connection with AWS IoT MQTT
 * broker. This parser will not check for the correctness of the document as it
 * is designed for low memory footprint rather than checking for correctness of
 * the JSON document. This parser is not meant to be used as a general purpose
 * JSON parser.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

/* IoT SDK includes. */
#include "aws_iot_shadow.h"
#include "aws_iot_demo_profile.h"
#include "iot_mqtt.h"
#include "iot_taskpool_freertos.h"
#include "aws_iot_doc_parser.h"
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"
#include "platform/iot_network_freertos.h"

/* Preprocessor check iot configuration */
#include "aws_iot_setup_check.h"

/* Demo specific includes. */
#include "demo_config.h"

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
#define shadowexampleKEEP_ALIVE_SECONDS            ( 0 )

/**
 * @brief The timeout for MQTT operations in this example.
 */
#define shadowexampleMQTT_TIMEOUT_MS			 ( 5000 )

/**
 * @brief Update count of shadow in a loop in the demo.
 *
 */
#define shadowexampleUPDATE_COUNT				 ( 20 )

/**
 * @brief The task wait period between each Shadow update.
 *
 */
#define shadowexampleUPDATE_PERIOD_MS			 ( 3000 )

/**
 * @brief The task wait period between each demo loop.
 */
#define shadowexampleLOOP_WAIT_PERIOD_MS		 ( 5000 )

/**
 * @brief The timeout period for updates from Shadow Delta Callback before
 * attempting next Shadow Update.
 */
#define shadowexampleWAIT_PERIOD_FOR_DELTA_MS	 ( 5000 )

/**
 * @brief Argument for AwsIotShadow_Init to use the default timeout.
 */
#define shadowexampleUSE_DEFAULT_MQTT_TIMEOUT	 ( 0 )

/**
 * @brief The bit which is set in the demo task's notification value from the
 * disconnect callback to inform the demo task about the MQTT disconnect.
 */
#define shadowexampleDISCONNECTED_BIT			 ( 1UL << 0UL )

/**
 * @brief Compile time calculation of shadowexampleCLIENT_IDENTIFIER_LENGTH.
 */
#define shadowexampleCLIENT_IDENTIFIER_LENGTH	 sizeof( awsiotdemoprofileCLIENT_IDENTIFIER ) - 1

/**
 * @brief Format string representing a Shadow document with a "desired" state.
 *
 * Note the client token, which is required for all Shadow updates. The client
 * token must be unique at any given time, but may be reused once the update is
 * completed. For this demo, a timestamp is used for a client token.
 */
#define shadowexampleDESIRED_JSON \
	"{"							  \
	"\"state\":{"				  \
	"\"desired\":{"				  \
	"\"powerOn\":%01d"			  \
	"}"							  \
	"},"						  \
	"\"clientToken\":\"%06lu\""	  \
	"}"

/**
 * @brief The expected size of #shadowexampleDESIRED_JSON.
 *
 * Because all the format specifiers in #shadowexampleDESIRED_JSON include a
 * length, its full size is known at compile-time.
 */
#define shadowexampleDESIRED_JSON_SIZE    ( sizeof( shadowexampleDESIRED_JSON ) - 3 )

/**
 * @brief Format string representing a Shadow document with a "reported" state.
 *
 * Note the client token, which is required for all Shadow updates. The client
 * token must be unique at any given time, but may be reused once the update is
 * completed. For this demo, a timestamp is used for a client token.
 */
#define shadowexampleREPORTED_JSON \
	"{"							   \
	"\"state\":{"				   \
	"\"reported\":{"			   \
	"\"powerOn\":%01d"			   \
	"}"							   \
	"},"						   \
	"\"clientToken\":\"%06lu\""	   \
	"}"

/**
 * @brief The expected size of #shadowexampleREPORTED_JSON.
 *
 * Because all the format specifiers in #shadowexampleREPORTED_JSON include a
 * length, its full size is known at compile-time.
 */
#define shadowexampleREPORTED_JSON_SIZE    ( sizeof( shadowexampleREPORTED_JSON ) - 3 )

/**
*  @brief This is the current state of the shadow used in this demo.
*/
static int32_t lDevicePowerOnState = 0;

/**
 * @brief This is a Semaphore used to synchronize between delta callback and
 * Shadow updates.
 */
iot_sem_internal_t xDeltaSemaphore = { 0 };

/**
 * @brief The task used to demonstrate Shadow.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 *
 */
static void prvShadowDemoTask( void *pvParameters );

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
 * @brief Connects to the MQTT broker as specified in awsiotdemoprofileAWS_ENDPOINT
 * and awsiotdemoprofileAWS_MQTT_PORT.
 *
 */
static void prvMQTTConnect( void );

/**
 * @brief Disconnects from the MQTT broker gracefully by sending an MQTT
 * DISCONNECT message.
 *
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

/**
 * @brief Set the Shadow callback functions used in this demo.
 *
 * There are 2 Shadow callbacks set by this function. updated callback
 * and delta Callback.
 *
 */
static void prvSetShadowCallbacks( void );

/**
 * @brief Clear the Shadow callbacks.
 *
 * There are 2 Shadow callbacks cleared by this function. updated callback
 * and delta Callback.
 *
 */
static void prvClearShadowCallbacks( void );

/**
 * @brief Try to delete any Shadow document in the cloud.
 *
 */
static void prvClearShadowDocument( void );

/**
 * @brief Send the Shadow updates that will trigger the Shadow callbacks.
 *
 */
static void prvSendShadowUpdates( void );

/**
 * @brief Shadow delta callback, invoked when the desired and updates Shadow
 * states differ.
 *
 * This function simulates a device updating its state in response to a Shadow.
 *
 * @param[in] pCallbackContext Delta semaphore used to synchronize between
 * delta callback and updated callback.
 * @param[in] pxCallbackParam The received Shadow delta document.
 */
static void prvShadowDeltaCallback( void * pCallbackContext,
									AwsIotShadowCallbackParam_t * pxCallbackParam );

/**
 * @brief Shadow updated callback, invoked when the Shadow document changes.
 *
 * This function reports when a Shadow has been updated.
 *
 * @param[in] pCallbackContext Not used.
 * @param[in] pxCallbackParam The received Shadow updated document.
 */
static void prvShadowUpdatedCallback( void * pCallbackContext,
									  AwsIotShadowCallbackParam_t * pxCallbackParam );

/**
 * @brief Parses a key in the "state" section of a Shadow delta document.
 *
 * @param[in] pcDeltaDocument The Shadow delta document to parse.
 * @param[in] xDeltaDocumentLength The length of `pcDeltaDocument`.
 * @param[in] pcDeltaKey The key in the delta document to find. Must be NULL-terminated.
 * @param[out] ppcDelta Set to the first character in the delta key.
 * @param[out] pxDeltaLength The length of the delta key.
 *
 * @return `true` if the given delta key is found; `false` otherwise.
 */
static BaseType_t prvGetDelta( const char * pcDeltaDocument,
							   size_t xDeltaDocumentLength,
							   const char * pcDeltaKey,
							   const char ** ppcDelta,
							   size_t * pxDeltaLength );

/**
 * @brief Parses the "state" key from the "previous" or "current" sections of a
 * Shadow updated document.
 *
 * @param[in] pcUpdatedDocument The Shadow updated document to parse.
 * @param[in] xUpdatedDocumentLength The length of `pcUpdatedDocument`.
 * @param[in] pcSectionKey Either "previous" or "current". Must be NULL-terminated.
 * @param[out] ppcState Set to the first character in "state".
 * @param[out] pxStateLength Length of the "state" section.
 *
 * @return pdTRUE if the "state" was found; pdFALSE otherwise.
 */
static BaseType_t prvGetUpdatedState( const char * pcUpdatedDocument,
									  size_t xUpdatedDocumentLength,
									  const char * pcSectionKey,
									  const char ** ppcState,
									  size_t * pxStateLength );

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
	.pHostName = awsiotdemoprofileAWS_ENDPOINT,
	.port = awsiotdemoprofileAWS_MQTT_PORT
};

static struct IotNetworkCredentials xNetworkSecurityCredentials =
{
	/* Optional TLS extensions. For this demo, they are disabled. */
	.pAlpnProtos = NULL,
	.maxFragmentLength = 0,

	/* SNI is enabled by default. */
	.disableSni = false,

	/* Provide the certificate for validating the server. Only required for
	demos using TLS. */
	.pRootCa = awsiotdemoprofileAWS_CERTIFICATE_PEM,
	.rootCaSize = sizeof( awsiotdemoprofileAWS_CERTIFICATE_PEM ),

	/* Strong mutual authentication to authenticate both the broker and
	* the client. */
	.pClientCert = awsiotdemoprofileCLIENT_CERTIFICATE_PEM,
	.clientCertSize = sizeof( awsiotdemoprofileCLIENT_CERTIFICATE_PEM ),
	.pPrivateKey = awsiotdemoprofileCLIENT_PRIVATE_KEY_PEM,
	.privateKeySize = sizeof( awsiotdemoprofileCLIENT_PRIVATE_KEY_PEM )
};

static IotMqttNetworkInfo_t xNetworkInfo =
{
	/* No connection to the MQTT broker has been established yet and we want to
	 * establish a new connection. */
	.createNetworkConnection = true,
	.u.setup.pNetworkServerInfo = &( xMQTTBrokerInfo ),

	/* Set the TLS credentials for the new MQTT connection. This member is NULL
	 * for the plain text MQTT demo. */
	.u.setup.pNetworkCredentialInfo = &xNetworkSecurityCredentials,

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
	.awsIotMqttMode = true,

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
	.keepAliveSeconds = shadowexampleKEEP_ALIVE_SECONDS,

	/* The client identifier is used to uniquely identify this MQTT client to
	 * the MQTT broker.  In a production device the identifier can be something
	 * unique, such as a device serial number. */
	.pClientIdentifier = awsiotdemoprofileCLIENT_IDENTIFIER,
	.clientIdentifierLength = ( uint16_t ) sizeof( awsiotdemoprofileCLIENT_IDENTIFIER ) - 1,

	/* This example does not authenticate the client and therefore username and
	 * password fields are not used. */
	.pUserName = NULL,
	.userNameLength = 0,
	.pPassword = NULL,
	.passwordLength = 0
};
/*-----------------------------------------------------------*/

void vStartShadowDeviceOperationsDemo( void )
{
TickType_t xShortDelay = ( TickType_t ) pdMS_TO_TICKS( ( TickType_t ) 500 );

	/* Wait a short time to allow receipt of the ARP replies. */
	vTaskDelay( xShortDelay );

	/* This example uses a single application task, which in turn is used to
	 * connect, subscribe, publish, unsubscribe and disconnect from the MQTT
	 * broker. */
	xTaskCreate( prvShadowDemoTask,       /* Function that implements the task. */
				 "ShadowDemo",            /* Text name for the task - only used for debugging. */
				 democonfigDEMO_STACKSIZE,/* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,                    /* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,        /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );                  /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvShadowDemoTask( void *pvParameters )
{
uint32_t ulNotificationValue = 0;
const TickType_t xNoDelay = ( TickType_t ) 0;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* One time initialization of the libraries used by this demo. */
	prvInitialiseLibraries();

	for( ; ; )
	{
		/* Don't expect any notifications to be pending yet. */
		configASSERT( ulTaskNotifyTake( pdTRUE, xNoDelay ) == 0 );

		/****************************** Connect. ******************************/

		/* Establish a connection to the AWS IoT MQTT broker. This example connects to
		 * the MQTT broker as specified in awsiotdemoprofileAWS_ENDPOINT and
		 * awsiotdemoprofileAWS_MQTT_PORT at the top of this file.
		 */
		configPRINTF( ( "Attempt to connect to %s\r\n", awsiotdemoprofileAWS_ENDPOINT ) );
		prvMQTTConnect();
		configPRINTF( ( "Connected to %s\r\n", awsiotdemoprofileAWS_ENDPOINT ) );

		/************************ Create a semaphore **************************/

		/* Creates a semaphore to synchronize between delta callback and
		 * Shadow updates.
		 */
		configPRINTF( ( "Creating delta semaphore\r\n" ) );
		configASSERT( xSemaphoreCreateCountingStatic( 1, 0, &xDeltaSemaphore.xSemaphore ) != NULL );

		/************************ Set shadow callbacks ************************/

		/* Sets the updated callback and delta callback */
		configPRINTF( ( "Setting the updated callback and  delta callback\r\n" ) );
		prvSetShadowCallbacks();

		/************************ Clear shadow document ***********************/

		/* Clears the Shadow document if it exists already */
		configPRINTF( ( "Clearing the Shadow document if it already exits\r\n" ) );
		prvClearShadowDocument();

		/*********************** Send Shadow updates **************************/

		/* Send Shadow updates for shadowexampleUPDATE_COUNT times.
		 * For each Shadow update, it waits on xDeltaSemaphore. xDeltaSemaphore
		 * will be posted by the delta callback.
		 */
		configPRINTF( ( "Sending Shadow updates\r\n" ) );
		prvSendShadowUpdates();

		/************************ Clear shadow document ***********************/

		/* Clears the Shadow document at the end of the demo */
		configPRINTF( ( "Clearing the Shadow document\r\n" ) );
		prvClearShadowDocument();

		/************** Clear callbacks and Disconnect MQTT. ******************/

		/* Clear updated callback and delta callback */
		configPRINTF( ( "Clearing the Shadow updated callback and delta callback\r\n" ) );
		prvClearShadowCallbacks();

		/* Disconnect MQTT gracefully. */
		prvMQTTDisconnect();
		configPRINTF( ( "Disconnected from %s\r\n\r\n", awsiotdemoprofileAWS_ENDPOINT ) );

		/* Wait for the disconnect operation to complete which is informed to us
		 * by the disconnect callback (prvExample_OnDisconnect)by setting
		 * the shadowexampleDISCONNECTED_BIT in this task's notification value.
		 * Note that the bit is cleared in the task's notification value to
		 * ensure that it is ready for the next run. */
		xTaskNotifyWait( 0UL,                           /* Don't clear any bits on entry. */
						 shadowexampleDISCONNECTED_BIT, /* Clear bit on exit. */
						 &( ulNotificationValue ),      /* Obtain the notification value. */
						 pdMS_TO_TICKS( shadowexampleMQTT_TIMEOUT_MS ) );
		configASSERT( ( ulNotificationValue & shadowexampleDISCONNECTED_BIT ) == shadowexampleDISCONNECTED_BIT );

		/* Destroy the delta semaphore*/
		vSemaphoreDelete( ( SemaphoreHandle_t ) &xDeltaSemaphore.xSemaphore );

		/* Clear the current reported shadow state to toggle the reported state. */
		lDevicePowerOnState = 0;

		/* Wait for some time between two iterations to ensure that we do not
		 * bombard the broker. */
		configPRINTF( ( "prvShadowDemoTask() completed an iteration successfully. Total free heap is %u\r\n", xPortGetFreeHeapSize() ) );
		configPRINTF( ( "Demo completed successfully.\r\n" ) );
		configPRINTF( ( "Short delay before starting the next iteration... \r\n\r\n" ) );
		vTaskDelay( pdMS_TO_TICKS( shadowexampleLOOP_WAIT_PERIOD_MS ) );
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
				 shadowexampleDISCONNECTED_BIT,
				 eSetBits /* Set the shadowexampleDISCONNECTED_BIT in the demo task's notification value. */
				 );
}
/*-----------------------------------------------------------*/

static void prvMQTTConnect( void )
{
IotMqttError_t xResult;

	/* Set the context to pass into the disconnect callback function. */
	xNetworkInfo.disconnectCallback.pCallbackContext = ( void * ) xTaskGetCurrentTaskHandle();

	/* Establish the connection to the MQTT broker - It is a blocking call and
	 * will return only when connection is complete or a timeout occurs. */
	xResult = IotMqtt_Connect( &( xNetworkInfo ),
							   &( xConnectInfo ),
							   shadowexampleMQTT_TIMEOUT_MS,
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

static void prvSetShadowCallbacks( void )
{
AwsIotShadowError_t xCallbackStatus = AWS_IOT_SHADOW_STATUS_PENDING;
AwsIotShadowCallbackInfo_t xDeltaCallback = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER,
						   xUpdatedCallback = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;

	/* Set the functions for callbacks. */
	xDeltaCallback.pCallbackContext = &xDeltaSemaphore;
	xDeltaCallback.function = prvShadowDeltaCallback;
	xUpdatedCallback.function = prvShadowUpdatedCallback;

	/************************ Set delta callbacks ****************************/

	/* Set the delta callback, which notifies of different desired and reported
	 * Shadow states. */
	xCallbackStatus = AwsIotShadow_SetDeltaCallback( xMQTTConnection,
													 awsiotdemoprofileCLIENT_IDENTIFIER,
													 shadowexampleCLIENT_IDENTIFIER_LENGTH,
													 0, &xDeltaCallback );
	configASSERT( xCallbackStatus == AWS_IOT_SHADOW_SUCCESS );

	/************************ Set updated callbacks **************************/

	/* Set the updated callback, which notifies when a Shadow document is
	* changed. */
	xCallbackStatus = AwsIotShadow_SetUpdatedCallback( xMQTTConnection,
													   awsiotdemoprofileCLIENT_IDENTIFIER,
													   shadowexampleCLIENT_IDENTIFIER_LENGTH,
													   0, &xUpdatedCallback );

	configASSERT( xCallbackStatus == AWS_IOT_SHADOW_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvClearShadowCallbacks( void )
{
AwsIotShadowError_t xCallbackStatus = AWS_IOT_SHADOW_STATUS_PENDING;

	/************************ Clear delta callbacks **************************/
	xCallbackStatus = AwsIotShadow_SetDeltaCallback( xMQTTConnection,
													 awsiotdemoprofileCLIENT_IDENTIFIER,
													 shadowexampleCLIENT_IDENTIFIER_LENGTH,
													 0, NULL );
	configASSERT( xCallbackStatus == AWS_IOT_SHADOW_SUCCESS );

	/************************ Clear updated callbacks ************************/
	xCallbackStatus = AwsIotShadow_SetUpdatedCallback( xMQTTConnection,
													   awsiotdemoprofileCLIENT_IDENTIFIER,
													   shadowexampleCLIENT_IDENTIFIER_LENGTH,
													   0, NULL );
	configASSERT( xCallbackStatus == AWS_IOT_SHADOW_SUCCESS );
}
/*-----------------------------------------------------------*/

static void prvShadowDeltaCallback( void * pCallbackContext,
									AwsIotShadowCallbackParam_t * pxCallbackParam )
{
BaseType_t xDeltaFound = pdFALSE;
const char * pcDelta = NULL;
size_t xDeltaLength = 0;
IotSemaphore_t * pxDeltaSemaphore = pCallbackContext;
uint32_t ulUpdateDocumentLength = 0;
AwsIotShadowError_t xShadowStatus = AWS_IOT_SHADOW_STATUS_PENDING;
AwsIotShadowDocumentInfo_t xUpdateDocument = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
uint8_t ucNewState = 0;

	configASSERT( pxDeltaSemaphore != NULL );
	configASSERT( pxCallbackParam != NULL );

	/* A buffer containing the update document. It has static duration to prevent
	 * it from being placed on the call stack.This is only safe because there
	 * is only one task in the task pool so this function cannot be called from
	 * two tasks simultaneously. */
	static char cUpdateDocument[ shadowexampleREPORTED_JSON_SIZE + 1 ] = { 0 };

	/****************** Get delta state from Shadow document *****************/
	/* Check if there is a different "powerOn" state in the Shadow. */
	xDeltaFound = prvGetDelta( pxCallbackParam->u.callback.pDocument,
							   pxCallbackParam->u.callback.documentLength,
							   "powerOn",
							   &pcDelta,
							   &xDeltaLength );

	configASSERT( xDeltaFound == pdTRUE );

	/* Change the current state based on the value in the delta document. */
	if( *pcDelta == '0' )
	{
		ucNewState = 0;
	}
	else if( *pcDelta == '1' )
	{
		ucNewState = 1;
	}
	else
	{
		configPRINTF( ( "Unknown powerOn state parsed from delta document.\r\n" ) );

		/* Set new state to current state to ignore the delta document. */
		ucNewState = lDevicePowerOnState;
	}

	if( ucNewState != lDevicePowerOnState )
	{
		/* Toggle state. */
		configPRINTF( ( "%.*s changing state from %d to %d.\r\n",
						pxCallbackParam->thingNameLength,
						pxCallbackParam->pThingName,
						lDevicePowerOnState,
						ucNewState ) );

		lDevicePowerOnState = ucNewState;

		/* Set the common members to report the new state. */
		xUpdateDocument.pThingName = pxCallbackParam->pThingName;
		xUpdateDocument.thingNameLength = pxCallbackParam->thingNameLength;
		xUpdateDocument.u.update.pUpdateDocument = cUpdateDocument;
		xUpdateDocument.u.update.updateDocumentLength = shadowexampleREPORTED_JSON_SIZE;

		/* Generate a Shadow document for the reported state. To keep the client
		 * token within 6 characters, it is modded by 1000000. */
		ulUpdateDocumentLength = snprintf( cUpdateDocument,
										   shadowexampleREPORTED_JSON_SIZE + 1,
										   shadowexampleREPORTED_JSON,
										   ( int ) lDevicePowerOnState,
										   ( long unsigned ) ( IotClock_GetTimeMs() % 1000000 ) );

		/* Check if the reported state document is generated for Shadow update*/
		configASSERT( ( size_t ) ulUpdateDocumentLength == shadowexampleREPORTED_JSON_SIZE );

		/* Send the Shadow update. Its result is not checked by waiting for the
		 * callback, as the Shadow updated callback will report if the Shadow
		 * was successfully updated. As the Shadow is constantly updated
		 * in this demo, the "Keep Subscriptions" flag is passed to this
		 * function. */
		xShadowStatus = AwsIotShadow_UpdateAsync( pxCallbackParam->mqttConnection,
												  &xUpdateDocument,
												  AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS,
												  NULL,
												  NULL );

		configASSERT( xShadowStatus == AWS_IOT_SHADOW_STATUS_PENDING );
		configPRINTF( ( "%.*s sent new state report: %.*s\r\n",
						pxCallbackParam->thingNameLength,
						pxCallbackParam->pThingName,
						shadowexampleREPORTED_JSON_SIZE,
						cUpdateDocument ) );

		/* Post to the delta semaphore to unblock the thread sending Shadow updates. */
		xSemaphoreGive( ( SemaphoreHandle_t ) &pxDeltaSemaphore->xSemaphore );
	}
}
/*-----------------------------------------------------------*/

static void prvShadowUpdatedCallback( void * pCallbackContext,
									  AwsIotShadowCallbackParam_t * pxCallbackParam )
{
BaseType_t xPreviousFound = pdFALSE, xCurrentFound = pdFALSE;
const char * pcPrevious = NULL, * pcCurrent = NULL;
size_t xPreviousLength = 0, xCurrentLength = 0;

	/* Silence warnings about unused parameters. */
	( void ) pCallbackContext;

	configASSERT( pxCallbackParam != NULL );

	/****************** Get previous state from Shadow document **************/
	/* Find the previous Shadow document. */
	xPreviousFound = prvGetUpdatedState( pxCallbackParam->u.callback.pDocument,
										 pxCallbackParam->u.callback.documentLength,
										 "previous",
										 &pcPrevious,
										 &xPreviousLength );

	/****************** Get current state from Shadow document **************/
	/* Find the current Shadow document. */
	xCurrentFound = prvGetUpdatedState( pxCallbackParam->u.callback.pDocument,
										pxCallbackParam->u.callback.documentLength,
										"current",
										&pcCurrent,
										&xCurrentLength );

	configASSERT( ( xPreviousFound == pdTRUE ) || ( xCurrentFound == pdTRUE ) );

	/* Log the previous and current states. */
	configPRINTF( ( "Shadow was updated!\r\n"
					"Previous: {\"state\":%.*s}\r\n"
					"Current:  {\"state\":%.*s}\r\n",
					xPreviousLength,
					pcPrevious,
					xCurrentLength,
					pcCurrent ) );
}
/*-----------------------------------------------------------*/

static BaseType_t prvGetDelta( const char * pcDeltaDocument,
							   size_t xDeltaDocumentLength,
							   const char * pcDeltaKey,
							   const char ** pcDelta,
							   size_t * pcDeltaLength )
{
BaseType_t xStateFound = pdFALSE, xDeltaFound = pdFALSE;
const size_t xDeltaKeyLength = strlen( pcDeltaKey );
const char * pcState = NULL;
size_t xStateLength = 0;

	configASSERT( pcDeltaDocument != NULL );
	configASSERT( pcDeltaKey != NULL );
	/****************** Get state from Shadow document ***********************/

	/* Note: This parser used is specific for parsing AWS IoT document received
	 * through a mutually authenticated connection. This parser will not check
	 * for the correctness of the document as it is designed for low memory
	 * footprint rather than checking for correctness of the document. This
	 * parser is not meant to be used as a general purpose JSON parser.
	 */
	xStateFound = ( BaseType_t ) AwsIotDocParser_FindValue(
		pcDeltaDocument,
		xDeltaDocumentLength,
		"state",
		5,
		&pcState,
		&xStateLength );

	configASSERT( xStateFound == pdTRUE );

	/********** Get delta key from state section of Shadow document **********/

	/* Note: This parser used is specific for parsing AWS IoT document received
	 * through a mutually authenticated connection. This parser will not check
	 * for the correctness of the document as it is designed for low memory
	 * footprint rather than checking for correctness of the document. This
	 * parser is not meant to be used as a general purpose JSON parser.
	 */
	xDeltaFound = ( BaseType_t ) AwsIotDocParser_FindValue(
		pcState,
		xStateLength,
		pcDeltaKey,
		xDeltaKeyLength,
		pcDelta,
		pcDeltaLength );

	return xDeltaFound;
}
/*-----------------------------------------------------------*/

static BaseType_t prvGetUpdatedState( const char * pcUpdatedDocument,
									  size_t xUpdatedDocumentLength,
									  const char * pcSectionKey,
									  const char ** ppcState,
									  size_t * ppcStateLength )
{
BaseType_t xSectionFound = pdFALSE, xStateFound = pdFALSE;
const size_t xSectionKeyLength = strlen( pcSectionKey );
const char * pcSection = NULL;
size_t xSectionLength = 0;

	configASSERT( pcUpdatedDocument != NULL );
	configASSERT( pcSectionKey != NULL );

	/*********** Find the given section in the updated document. *************/

	/* Note: This parser used is specific for parsing AWS IoT document received
	 * through a mutually authenticated connection. This parser will not check
	 * for the correctness of the document as it is designed for low memory
	 * footprint rather than checking for correctness of the document. This
	 * parser is not meant to be used as a general purpose JSON parser.
	 */
	xSectionFound = ( BaseType_t ) AwsIotDocParser_FindValue(
		pcUpdatedDocument,
		xUpdatedDocumentLength,
		pcSectionKey,
		xSectionKeyLength,
		&pcSection,
		&xSectionLength );

	configASSERT( xSectionFound == pdTRUE );

	/*********** Find the state key within the section found *****************/

	/* Find the "state" key within the "previous" or "current" section.
	 *
	 * Note: This parser used is specific for parsing AWS IoT document received
	 * through a mutually authenticated connection. This parser will not check
	 * for the correctness of the document as it is designed for low memory
	 * footprint rather than checking for correctness of the document. This
	 * parser is not meant to be used as a general purpose JSON parser.
	 */
	xStateFound = ( BaseType_t ) AwsIotDocParser_FindValue(
		pcSection,
		xSectionLength,
		"state",
		5,
		ppcState,
		ppcStateLength );

	return xStateFound;
}
/*-----------------------------------------------------------*/

static void prvClearShadowDocument( void )
{
AwsIotShadowError_t xDeleteStatus = AWS_IOT_SHADOW_STATUS_PENDING;

	/************************* Delete Shadow document ************************/
	xDeleteStatus = AwsIotShadow_DeleteSync( xMQTTConnection,
											 awsiotdemoprofileCLIENT_IDENTIFIER,
											 shadowexampleCLIENT_IDENTIFIER_LENGTH,
											 0, shadowexampleMQTT_TIMEOUT_MS );
	configASSERT( ( xDeleteStatus == AWS_IOT_SHADOW_SUCCESS ) || ( xDeleteStatus == AWS_IOT_SHADOW_NOT_FOUND ) );

	configPRINTF( ( "Successfully cleared Shadow of %.*s.\r\n",
					shadowexampleCLIENT_IDENTIFIER_LENGTH,
					awsiotdemoprofileCLIENT_IDENTIFIER ) );
}
/*-----------------------------------------------------------*/

static void prvSendShadowUpdates( void )
{
int32_t lIndex = 0, lDesiredState = 0, lStatus = 0;
AwsIotShadowError_t xShadowStatus = AWS_IOT_SHADOW_STATUS_PENDING;
AwsIotShadowDocumentInfo_t xUpdateDocument = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;

	/* A buffer containing the update document. It has static duration to prevent
	 * it from being placed on the call stack. */
	static char cUpdateDocument[ shadowexampleDESIRED_JSON_SIZE + 1 ] = { 0 };

	/********** Set the common members of Shadow update document *************/
	xUpdateDocument.pThingName = awsiotdemoprofileCLIENT_IDENTIFIER;
	xUpdateDocument.thingNameLength = shadowexampleCLIENT_IDENTIFIER_LENGTH;
	xUpdateDocument.u.update.pUpdateDocument = cUpdateDocument;
	xUpdateDocument.u.update.updateDocumentLength = shadowexampleDESIRED_JSON_SIZE;

	/*************** Publish Shadow updates at a set period. *****************/
	for( lIndex = 1; lIndex <= shadowexampleUPDATE_COUNT; lIndex++ )
	{
		/* Toggle the desired state. */
		lDesiredState = !( lDesiredState );

		/* Generate a Shadow desired state document, using a timestamp for the client
		 * token. To keep the client token within 6 characters, it is modded by 1000000. */
		lStatus = snprintf( cUpdateDocument,
							shadowexampleDESIRED_JSON_SIZE + 1,
							shadowexampleDESIRED_JSON,
							( int ) lDesiredState,
							( long unsigned ) ( IotClock_GetTimeMs() % 1000000 ) );

		/* Check for errors from snprintf. The expected value is the length of
		 * the desired JSON document less the format specifier for the state. */
		configASSERT( lStatus == shadowexampleDESIRED_JSON_SIZE );

		configPRINTF( ( "Sending Shadow update %d of %d: %s\r\n",
						lIndex,
						shadowexampleUPDATE_COUNT,
						cUpdateDocument ) );

		/* Send the Shadow update. Because the Shadow is constantly updated in
		 * this demo, the "Keep Subscriptions" flag is passed to this function.
		 * Note that this flag only needs to be passed on the first call, but
		 * passing it for subsequent calls is fine.
		 */
		xShadowStatus = AwsIotShadow_UpdateSync( xMQTTConnection,
												 &xUpdateDocument,
												 AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS,
												 shadowexampleMQTT_TIMEOUT_MS );

		configASSERT( xShadowStatus == AWS_IOT_SHADOW_SUCCESS );

		configPRINTF( ( "Successfully sent Shadow update %d of %d.\r\n",
						lIndex,
						shadowexampleUPDATE_COUNT ) );

		/* Wait for the delta callback to change its state before continuing. */
		configASSERT( xSemaphoreTake( ( SemaphoreHandle_t ) &xDeltaSemaphore.xSemaphore,
									  pdMS_TO_TICKS( shadowexampleWAIT_PERIOD_FOR_DELTA_MS ) ) == pdTRUE );

		IotClock_SleepMs( shadowexampleUPDATE_PERIOD_MS );
	}

	/* Remove persistent subscriptions. In the AwsIotShadow_UpdateSync call, we have used the */
	xShadowStatus = AwsIotShadow_RemovePersistentSubscriptions( xMQTTConnection,
																awsiotdemoprofileCLIENT_IDENTIFIER,
																shadowexampleCLIENT_IDENTIFIER_LENGTH,
																AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS );

	configASSERT( xShadowStatus == AWS_IOT_SHADOW_SUCCESS );
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

	/* Initialize Shadow library*/
	xResult = AwsIotShadow_Init( shadowexampleUSE_DEFAULT_MQTT_TIMEOUT );
	configASSERT( xResult == AWS_IOT_SHADOW_SUCCESS );
}
/*-----------------------------------------------------------*/
