/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* This demo executes Jobs obtained from AWS IoT. An AWS IoT Job is used to define
 * a set of remote operations that are sent to and executed on one or more devices
 * connected to AWS IoT. Please refer to AWS documentation for more information
 * about AWS IoT Jobs.
 * https://docs.aws.amazon.com/iot/latest/developerguide/iot-jobs.html
 *
 * This demo creates a single application task that sets a callback for the
 * jobs/notify-next topic and executes Jobs created from the AWS IoT console or AWS
 * CLI. Please refer to AWS CLI documentation for more information in creating a
 * Job document.
 * https://docs.aws.amazon.com/cli/latest/reference/iot/create-job.html
 *
 * This demo expects Job documents to have an "action" JSON key. Actions can
 * be one "print", "publish", or "exit".
 * Print Jobs log a message to the local console, and must contain a "message",
 * e.g. { "action": "print", "message": "Hello World!" }.
 * Publish Jobs publish a message to an MQTT Topic. The Job document must
 * contain a "message" and "topic" to publish to, e.g.
 * { "action": "publish", "topic": "demo/jobs", "message": "Hello World!" }.
 * The exit Job exits the demo. Sending { "action": "exit" } will end the program.
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
#include "aws_iot_jobs.h"
#include "aws_iot_demo_profile.h"
#include "iot_mqtt.h"
#include "iot_taskpool_freertos.h"
#include "aws_iot_doc_parser.h"
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"
#include "platform/iot_network_freertos.h"

#include "atomic.h"

/* Preprocessor check iot configuration. */
#include "aws_iot_setup_check.h"

/* Demo specific includes. */
#include "demo_config.h"

/*-----------------------------------------------------------*/

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
#define jobsexampleKEEP_ALIVE_SECONDS          ( 0 )

/**
 * @brief The timeout for MQTT operations in this example.
 */
#define jobsexampleMQTT_TIMEOUT_MS             ( 5000 )

/**
 * @brief Use default timeout when calling AwsIotJobs_Init.
 */
#define jobsexampleUSE_DEFAULT_MQTT_TIMEOUT    ( 0 )

/**
 * @brief The bit which is set in the demo task's notification value from the
 * disconnect callback to inform the demo task about the MQTT disconnect.
 */
#define jobsexampleDISCONNECTED_BIT            ( 1UL << 0UL )

/**
 * @brief The bit which is set in the demo task's notification value from the
 * operation complete callback to inform the demo task to exit.
 */
#define jobsexampleEXIT_BIT                    ( 1UL << 1UL )

/**
 * @brief Length of the client identifier for this demo.
 */
#define jobsexampleCLIENT_IDENTIFIER_LENGTH    ( sizeof( awsiotdemoprofileCLIENT_IDENTIFIER ) - 1 )

/**
 * @brief The JSON key of the Job ID.
 *
 * Job documents are in JSON documents received from the AWS IoT Jobs service.
 * All such JSON documents will contain this key, whose value represents the unique
 * identifier of a Job.
 */
#define jobsexampleID_KEY                      "jobId"

/**
 * @brief The length of #jobsexampleID_KEY.
 */
#define jobsexampleID_KEY_LENGTH               ( sizeof( jobsexampleID_KEY ) - 1 )

/**
 * @brief The JSON key of the Job document.
 *
 * Job documents are in JSON documents received from the AWS IoT Jobs service.
 * All such JSON documents will contain this key, whose value is an application-specific
 * Job document.
 */
#define jobsexampleDOC_KEY                     "jobDocument"

/**
 * @brief The length of #jobsexampleDOC_KEY.
 */
#define jobsexampleDOC_KEY_LENGTH              ( sizeof( jobsexampleDOC_KEY ) - 1 )

/**
 * @brief The JSON key whose value represents the action this demo should take.
 *
 * This demo program expects this key to be in the Job document. It is a key
 * specific to this demo.
 */
#define jobsexampleACTION_KEY                  "action"

/**
 * @brief The length of #jobsexampleACTION_KEY.
 */
#define jobsexampleACTION_KEY_LENGTH           ( sizeof( jobsexampleACTION_KEY ) - 1 )

/**
 * @brief A message associated with the Job action.
 *
 * This demo program expects this key to be in the Job document if the "action"
 * is either "publish" or "print". It represents the message that should be
 * published or printed, respectively.
 */
#define jobsexampleMESSAGE_KEY                 "message"

/**
 * @brief The length of #jobsexampleMESSAGE_KEY.
 */
#define jobsexampleMESSAGE_KEY_LENGTH          ( sizeof( jobsexampleMESSAGE_KEY ) - 1 )

/**
 * @brief An MQTT topic associated with the Job "publish" action.
 *
 * This demo program expects this key to be in the Job document if the "action"
 * is "publish". It represents the MQTT topic on which the message should be
 * published.
 */
#define jobsexampleTOPIC_KEY                   "topic"

/**
 * @brief The length of #jobsexampleTOPIC_KEY.
 */
#define jobsexampleTOPIC_KEY_LENGTH            ( sizeof( jobsexampleTOPIC_KEY ) - 1 )

/**
 * @brief The minimum length of a string in a JSON Job document.
 *
 * At the very least the Job ID must have the quotes that identify it as a JSON
 * string and 1 character for the string itself (the string must not be empty).
 */
#define jobsexampleJSON_STRING_MIN_LENGTH      ( ( size_t ) 3 )

/**
 * @brief The maximum length of a Job ID.
 *
 * This limit is defined by AWS service limits. See the following page for more
 * information.
 *
 * https://docs.aws.amazon.com/general/latest/gr/aws_service_limits.html#job-limits
 */
#define jobsexampleID_MAX_LENGTH               ( ( size_t ) 64 )

/**
 * @brief A value passed as context to #prvOperationCompleteCallback to specify that
 * it should notify the demo task of an exit request.
 */
#define jobsexampleSHOULD_EXIT                 ( ( void * ) ( ( intptr_t ) 1 ) )

/**
 * @brief Time to wait before exiting demo.
 *
 * The milliseconds to wait before exiting. This is because the MQTT Broker
 * will disconnect us if we are idle too long, and we have disabled keep alive.
 */
#define jobsexampleMS_BEFORE_EXIT              ( 10 * 60 * 1000 )

/*-----------------------------------------------------------*/

/**
 * @brief Currently supported actions that a Job document can specify.
 */
typedef enum _jobAction
{
	JOB_ACTION_PRINT,   /**< Print a message. */
	JOB_ACTION_PUBLISH, /**< Publish a message to an MQTT topic. */
	JOB_ACTION_EXIT,    /**< Exit the demo. */
	JOB_ACTION_UNKNOWN  /**< Unknown action. */
} _jobAction_t;

/**
 * @brief The task used to demonstrate Jobs.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvJobsDemoTask( void * pvParameters );

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
 * @brief Connects to the MQTT broker as specified in awsiotdemoprofileAWS_ENDPOINT
 * and awsiotdemoprofileAWS_MQTT_PORT.
 */
static void prvMQTTConnect( void );

/**
 * @brief Disconnects from the MQTT broker gracefully by sending an MQTT
 * DISCONNECT message.
 */
static void prvMQTTDisconnect( void );

/**
 * @brief Set callback for publishes to the jobs/notify-next topic.
 */
static void prvSetNotifyNextCallback( void );

/**
 * @brief Converts a string in a Job document to a #_jobAction_t.
 *
 * @param[in] pcAction The Job action as a string.
 * @param[in] xActionLength The length of `pcAction`.
 *
 * @return A #_jobAction_t equivalent to the given string.
 */
static _jobAction_t prvGetAction( const char * pcAction,
								  size_t xActionLength );

/**
 * @brief Extracts a JSON string from the Job document.
 *
 * @param[in] pcJsonDoc The JSON document to search.
 * @param[in] xJsonDocLength Length of `pcJsonDoc`.
 * @param[in] pcKey The JSON key to search for.
 * @param[in] xKeyLength Length of `pcKey`.
 * @param[out] ppcValue The extracted JSON value.
 * @param[out] pxValueLength Length of ppcValue.
 *
 * @return `pdTRUE` if the key was found and the value is valid; `pdFALSE` otherwise.
 */
static BaseType_t prvGetJsonString( const char * pcJsonDoc,
									size_t xJsonDocLength,
									const char * pcKey,
									size_t xKeyLength,
									const char ** ppcValue,
									size_t * pxValueLength );

/**
 * @brief Job operation completion callback. This function is invoked when an
 * asynchronous Job operation finishes.
 *
 * @param[in] pvCallbackContext Set to a non-NULL value to exit the demo.
 * @param[in] pxCallbackParam Information on the Job operation that completed.
 */
static void prvOperationCompleteCallback( void * pvCallbackContext,
										  AwsIotJobsCallbackParam_t * pxCallbackParam );


/**
 * @brief Process an action with a message, such as "print" or "publish".
 *
 * @param[in] xMqttConnection The MQTT connection to use if the action is "publish".
 * @param[in] xAction Either #JOB_ACTION_PRINT or #JOB_ACTION_PUBLISH.
 * @param[in] pcJobDoc A pointer to the Job document.
 * @param[in] xJobDocLength The length of the Job document.
 *
 * @return #AWS_IOT_JOB_STATE_SUCCEEDED on success; #AWS_IOT_JOB_STATE_FAILED otherwise.
 */
static AwsIotJobState_t prvProcessMessage( IotMqttConnection_t xMqttConnection,
										   _jobAction_t xAction,
										   const char * pcJobDoc,
										   size_t xJobDocLength );

/**
 * @brief Process a Job received from the Notify Next callback.
 *
 * @param[in] pxJobInfo The parameter to the Notify Next callback that contains
 * information about the received Job.
 * @param[in] pcJobId A pointer to the Job ID.
 * @param[in] xJobIdLength The length of the Job ID.
 * @param[in] pcJobDoc A pointer to the Job document.
 * @param[in] xJobDocLength The length of the Job document.
 */
static void prvProcessJob( const AwsIotJobsCallbackParam_t * pxJobInfo,
						   const char * pcJobId,
						   size_t xJobIdLength,
						   const char * pcJobDoc,
						   size_t xJobDocLength );

/**
 * @brief Jobs Notify Next callback. This function is invoked when a new Job is
 * received from the Jobs service.
 *
 * @param[in] pCallbackContext Ignored.
 * @param[in] pxCallbackInfo Contains the received Job.
 */
static void prvJobsCallback( void * pCallbackContext,
							 AwsIotJobsCallbackParam_t * pxCallbackInfo );

/*-----------------------------------------------------------*/

/**
 * @brief The MQTT connection handle used in this example.
 */
static IotMqttConnection_t xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/*
 * @brief The main task handle in this demo.
 */
static TaskHandle_t xMainTaskHandle;

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

/***************** Structures that define the connection. *********************/


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

	/* Set the TLS credentials for the new MQTT connection. */
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
	.awsIotMqttMode = false,

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
	 * there is no other MQTT traffic. */
	.keepAliveSeconds = jobsexampleKEEP_ALIVE_SECONDS,

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

static void prvExample_OnDisconnect( void * pvCallbackContext,
									 IotMqttCallbackParam_t * pxCallbackParams )
{
TaskHandle_t xDemoTaskHandle = ( TaskHandle_t ) pvCallbackContext;

	/* Ensure that we initiated the disconnect. */
	configASSERT( pxCallbackParams->u.disconnectReason == IOT_MQTT_DISCONNECT_CALLED );

	/* Inform the demo task about the disconnect. */
	xTaskNotify( xDemoTaskHandle,
				 jobsexampleDISCONNECTED_BIT,
				 eSetBits /* Set the jobsexampleDISCONNECTED_BIT in the demo task's notification value. */
				 );
}
/*-----------------------------------------------------------*/

void vStartJobsDemo( void )
{
TickType_t xShortDelay = ( TickType_t ) pdMS_TO_TICKS( ( TickType_t ) 500 );

	/* Wait a short time to allow receipt of the ARP replies. */
	vTaskDelay( xShortDelay );

	/* This example uses a single application task, which in turn is used to
	 * connect, subscribe, publish, unsubscribe and disconnect from the MQTT
	 * broker. */
	xTaskCreate( prvJobsDemoTask,		  /* Function that implements the task. */
				 "JobsDemo",			   /* Text name for the task - only used for debugging. */
				 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,					 /* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,		 /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );				   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvJobsDemoTask( void * pvParameters )
{
IotMqttError_t xResult;
IotNetworkError_t xNetworkInit;
uint32_t ulNotificationValue = 0;
const TickType_t xNoDelay = ( TickType_t ) 0;
AwsIotJobsError_t xStatus = AWS_IOT_JOBS_SUCCESS;
AwsIotJobsCallbackInfo_t xCallbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
AwsIotJobsRequestInfo_t xRequestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	xMainTaskHandle = xTaskGetCurrentTaskHandle();

	/* The MQTT library needs a task pool, so create the system task pool. */
	xResult = IotTaskPool_CreateSystemTaskPool( &( xTaskPoolParameters ) );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Initialize the network stack abstraction for FreeRTOS. */
	xNetworkInit = IotNetworkFreeRTOS_Init();
	configASSERT( xNetworkInit == IOT_NETWORK_SUCCESS );

	/* MQTT library must be initialized before it can be used. This is just one
	 * time initialization. */
	xResult = IotMqtt_Init();
	configASSERT( xResult == IOT_MQTT_SUCCESS );

	/* Initialize Jobs library. */
	xResult = AwsIotJobs_Init( jobsexampleUSE_DEFAULT_MQTT_TIMEOUT );
	configASSERT( xResult == AWS_IOT_JOBS_SUCCESS );

	/****************************** Connect. ******************************/

	/* Establish a connection to the AWS IoT MQTT broker. This example connects to
	 * the MQTT broker as specified in awsiotdemoprofileAWS_ENDPOINT and
	 * awsiotdemoprofileAWS_MQTT_PORT at the top of this file.
	 */
	configPRINTF( ( "Attempt to connect to %s\r\n", awsiotdemoprofileAWS_ENDPOINT ) );
	prvMQTTConnect();
	configPRINTF( ( "Connected to %s\r\n", awsiotdemoprofileAWS_ENDPOINT ) );

	/* Don't expect any notifications to be pending yet. */
	configASSERT( ulTaskNotifyTake( pdTRUE, xNoDelay ) == 0 );

	configPRINTF( ( "Setting callback for jobs/notify-next\r\n" ) );
	prvSetNotifyNextCallback();

	/* Call DescribeAsync to see if there are any pending jobs. */
	xRequestInfo.mqttConnection = xMQTTConnection;
	xRequestInfo.pThingName = awsiotdemoprofileCLIENT_IDENTIFIER;
	xRequestInfo.thingNameLength = jobsexampleCLIENT_IDENTIFIER_LENGTH;
	xRequestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
	xRequestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;

	/* Use the same callback as notify-next so any pending jobs will be
	 * executed the same way. */
	xCallbackInfo.function = prvJobsCallback;

	xStatus = AwsIotJobs_DescribeAsync( &xRequestInfo, AWS_IOT_JOBS_NO_EXECUTION_NUMBER, true, 0, &xCallbackInfo, NULL );
	configPRINTF( ( "Describe queued with result %s.\r\n", AwsIotJobs_strerror( xStatus ) ) );

	/* Print out a short user guide to the console. The default logging
	 * limit of 255 characters can be changed in demo_logging.c, but breaking
	 * up the only instance of a 1000+ character string is more practical. */
	configPRINTF( (
					  "\r\n"
					  "/*-----------------------------------------------------------*/\r\n"
					  "\r\n"
					  "The Jobs demo is now ready to accept Jobs.\r\n"
					  "Jobs may be created using the AWS IoT console or AWS CLI.\r\n"
					  "See the following link for more information.\r\n"
					  "\r\n" ) );
	configPRINTF( (
					  "\r"
					  "https://docs.aws.amazon.com/cli/latest/reference/iot/create-job.html\r\n"
					  "\r\n"
					  "This demo expects Job documents to have an \"action\" JSON key.\r\n"
					  "The following actions are currently supported:\r\n" ) );
	configPRINTF( (
					  "\r"
					  " - print          \r\n"
					  "   Logs a message to the local console. The Job document must also contain a \"message\".\r\n"
					  "   For example: { \"action\": \"print\", \"message\": \"Hello world!\"} will cause\r\n"
					  "   \"Hello world!\" to be printed on the console.\r\n" ) );
	configPRINTF( (
					  "\r"
					  " - publish        \r\n"
					  "   Publishes a message to an MQTT topic. The Job document must also contain a \"message\" and \"topic\".\r\n" ) );
	configPRINTF( (
					  "\r"
					  "   For example: { \"action\": \"publish\", \"topic\": \"demo/jobs\", \"message\": \"Hello world!\"} will cause\r\n"
					  "   \"Hello world!\" to be published to the topic \"demo/jobs\".\r\n" ) );
	configPRINTF( (
					  "\r"
					  " - exit           \r\n"
					  "   Exits the demo program. This program will run until { \"action\": \"exit\" } is received.\r\n"
					  "\r\n"
					  "/*-----------------------------------------------------------*/\r\n" ) );

	/* Wait for an exit job to be received. If an exit job is not received within
	 * jobsexampleMS_BEFORE_EXIT, exit anyway. This is because we have disabled
	 * keep-alive, and the server will disconnect as after some time. */
	xTaskNotifyWait( 0UL,					   /* Don't clear any bits on entry. */
					 jobsexampleEXIT_BIT,	   /* Clear bit on exit. */
					 &( ulNotificationValue ), /* Obtain the notification value. */
					 pdMS_TO_TICKS( jobsexampleMS_BEFORE_EXIT) );
	/* Check was due to receiving an exit job. */
	if( ( ulNotificationValue & jobsexampleEXIT_BIT ) != jobsexampleEXIT_BIT )
	{
		configPRINTF( ( "Disconnecting as %u milliseconds have elapsed.\r\n", jobsexampleMS_BEFORE_EXIT ) );
	}

	/* Disconnect MQTT gracefully. */
	prvMQTTDisconnect();
	configPRINTF( ( "Disconnected from %s\r\n\r\n", awsiotdemoprofileAWS_ENDPOINT ) );

	/* Wait for the disconnect operation to complete which is informed to us
	 * by the disconnect callback (prvExample_OnDisconnect)by setting
	 * the jobsexampleDISCONNECTED_BIT in this task's notification value. */
	xTaskNotifyWait( 0UL,						  /* Don't clear any bits on entry. */
					 jobsexampleDISCONNECTED_BIT, /* Clear bit on exit. */
					 &( ulNotificationValue ),	  /* Obtain the notification value. */
					 pdMS_TO_TICKS( jobsexampleMQTT_TIMEOUT_MS ) );
	configASSERT( ( ulNotificationValue & jobsexampleDISCONNECTED_BIT ) == jobsexampleDISCONNECTED_BIT );

	configPRINTF( ( "prvJobsDemoTask() completed successfully. Total free heap is %u\r\n", xPortGetFreeHeapSize() ) );
	configPRINTF( ( "Demo completed successfully.\r\n" ) );

	/* Clean up initialized libraries. */
	AwsIotJobs_Cleanup();
	IotMqtt_Cleanup();
	IotNetworkFreeRTOS_Cleanup();

	/* FreeRTOS Tasks must _vTaskDelete( NULL )_ before exiting the function. */
	vTaskDelete( NULL );
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
							   jobsexampleMQTT_TIMEOUT_MS,
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

static void prvSetNotifyNextCallback( void )
{
AwsIotJobsError_t xCallbackStatus = AWS_IOT_JOBS_SUCCESS;
AwsIotJobsCallbackInfo_t xCallbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;

	/* Set the jobs callback function. */
	xCallbackInfo.function = prvJobsCallback;

	/************************ Set notify-next callbacks **********************/

	xCallbackStatus = AwsIotJobs_SetNotifyNextCallback( xMQTTConnection,
														awsiotdemoprofileCLIENT_IDENTIFIER,
														jobsexampleCLIENT_IDENTIFIER_LENGTH,
														0,
														&xCallbackInfo );

	configASSERT( xCallbackStatus == AWS_IOT_JOBS_SUCCESS );
}
/*-----------------------------------------------------------*/

static _jobAction_t prvGetAction( const char * pcAction,
								  size_t xActionLength )
{
_jobAction_t xAction = JOB_ACTION_UNKNOWN;

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
/*-----------------------------------------------------------*/

static BaseType_t prvGetJsonString( const char * pcJsonDoc,
									size_t xJsonDocLength,
									const char * pcKey,
									size_t xKeyLength,
									const char ** ppcValue,
									size_t * pxValueLength )
{
BaseType_t xKeyFound = pdFALSE;

	configASSERT( pcJsonDoc != NULL );
	configASSERT( pcKey != NULL );

	/*
	 * Note: This parser used is specific for parsing AWS IoT document received
	 * through a mutually authenticated connection. This parser will not check
	 * for the correctness of the document as it is designed for low memory
	 * footprint rather than checking for correctness of the document. This
	 * parser is not meant to be used as a general purpose JSON parser.
	 */
	xKeyFound = ( BaseType_t ) AwsIotDocParser_FindValue(
		pcJsonDoc,
		xJsonDocLength,
		pcKey,
		xKeyLength,
		ppcValue,
		pxValueLength );

	if( xKeyFound == pdTRUE )
	{
		/* Exclude empty strings. */
		if( *pxValueLength < jobsexampleJSON_STRING_MIN_LENGTH )
		{
			xKeyFound = pdFALSE;
		}
		else
		{
			/* Adjust the value to remove the quotes. */
			( *ppcValue )++;
			( *pxValueLength ) -= 2;
		}
	}

	return xKeyFound;
}
/*-----------------------------------------------------------*/

static void prvOperationCompleteCallback( void * pvCallbackContext,
										  AwsIotJobsCallbackParam_t * pxCallbackParam )
{
	configASSERT( pxCallbackParam != NULL );

	/* This function is invoked when either a StartNext or Update completes. */
	if( pxCallbackParam->callbackType == AWS_IOT_JOBS_START_NEXT_COMPLETE )
	{
		configPRINTF( ( "Job StartNext complete with result %s.\r\n",
						AwsIotJobs_strerror( pxCallbackParam->u.operation.result ) ) );
	}
	else
	{
		configPRINTF( ( "Job Update complete with result %s.\r\n",
						AwsIotJobs_strerror( pxCallbackParam->u.operation.result ) ) );
	}

	/* If a non-NULL context is given, set the flag to exit the demo. */
	if( pvCallbackContext != NULL )
	{
		xTaskNotify( xMainTaskHandle,
					 jobsexampleEXIT_BIT,
					 eSetBits /* Set the jobsexampleEXIT_BIT in the demo task's notification value. */
					 );
	}
}
/*-----------------------------------------------------------*/

static AwsIotJobState_t prvProcessMessage( IotMqttConnection_t xMqttConnection,
										   _jobAction_t xAction,
										   const char * pcJobDoc,
										   size_t xJobDocLength )
{
AwsIotJobState_t xStatus = AWS_IOT_JOB_STATE_SUCCEEDED;
IotMqttError_t xMqttStatus = IOT_MQTT_STATUS_PENDING;
IotMqttPublishInfo_t xPublishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
const char * pcMessage = NULL, * pcTopic = NULL;
size_t xMessageLength = 0, xTopicLength = 0;

	configASSERT( pcJobDoc != NULL );

	/* Both "print" and "publish" require a "message" key. Search the Job
	 * document for this key. */
	if( prvGetJsonString( pcJobDoc,
						  xJobDocLength,
						  jobsexampleMESSAGE_KEY,
						  jobsexampleMESSAGE_KEY_LENGTH,
						  &pcMessage,
						  &xMessageLength ) == pdFALSE )
	{
		configPRINTF( ( "Job document for \"print\" or \"publish\" does not contain a %s key.\r\n",
						jobsexampleMESSAGE_KEY ) );

		xStatus = AWS_IOT_JOB_STATE_FAILED;
	}

	if( xStatus == AWS_IOT_JOB_STATE_SUCCEEDED )
	{
		if( xAction == JOB_ACTION_PRINT )
		{
			/* Print the given message if the action is "print". */
			configPRINTF( (
							  "\r\n"
							  "/*-----------------------------------------------------------*/\r\n"
							  "\r\n"
							  "%.*s\r\n"
							  "\r\n"
							  "/*-----------------------------------------------------------*/\r\n"
							  "\r\n", xMessageLength, pcMessage ) );
		}
		else
		{
			/* Extract the topic if the action is "publish". */
			if( prvGetJsonString( pcJobDoc,
								  xJobDocLength,
								  jobsexampleTOPIC_KEY,
								  jobsexampleTOPIC_KEY_LENGTH,
								  &pcTopic,
								  &xTopicLength ) == pdFALSE )
			{
				configPRINTF( ( "Job document for action \"publish\" does not contain a %s key.\r\n",
								jobsexampleTOPIC_KEY ) );

				xStatus = AWS_IOT_JOB_STATE_FAILED;
			}

			if( xStatus == AWS_IOT_JOB_STATE_SUCCEEDED )
			{
				xPublishInfo.qos = IOT_MQTT_QOS_0;
				xPublishInfo.pTopicName = pcTopic;
				xPublishInfo.topicNameLength = ( uint16_t ) xTopicLength;
				xPublishInfo.pPayload = pcMessage;
				xPublishInfo.payloadLength = xMessageLength;

				xMqttStatus = IotMqtt_PublishAsync( xMqttConnection, &xPublishInfo, 0, NULL, NULL );

				if( xMqttStatus != IOT_MQTT_SUCCESS )
				{
					xStatus = AWS_IOT_JOB_STATE_FAILED;
				}
			}
		}
	}

	return xStatus;
}
/*-----------------------------------------------------------*/

static void prvProcessJob( const AwsIotJobsCallbackParam_t * pxJobInfo,
						   const char * pcJobId,
						   size_t xJobIdLength,
						   const char * pcJobDoc,
						   size_t xJobDocLength )
{
AwsIotJobsError_t xStatus = AWS_IOT_JOBS_SUCCESS;
AwsIotJobsUpdateInfo_t xUpdateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
AwsIotJobsCallbackInfo_t xCallbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
const char * pcAction = NULL;
size_t xActionLength = 0;
_jobAction_t xAction = JOB_ACTION_UNKNOWN;
AwsIotJobsRequestInfo_t xRequestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;

	configASSERT( pxJobInfo != NULL );
	configASSERT( pcJobId != NULL );
	configASSERT( pcJobDoc != NULL );

	configPRINTF( ( "Job document received: %.*s\r\n", xJobDocLength, pcJobDoc ) );

	xRequestInfo.mqttConnection = pxJobInfo->mqttConnection;
	xRequestInfo.pThingName = pxJobInfo->pThingName;
	xRequestInfo.thingNameLength = pxJobInfo->thingNameLength;
	xRequestInfo.pJobId = pcJobId;
	xRequestInfo.jobIdLength = xJobIdLength;

	/* Tell the Jobs service that the device has started working on the Job.
	 * Use the StartNext API to set the Job's status to IN_PROGRESS. */
	xCallbackInfo.function = prvOperationCompleteCallback;

	xStatus = AwsIotJobs_StartNextAsync( &xRequestInfo, &xUpdateInfo, 0, &xCallbackInfo, NULL );

	configPRINTF( ( "Jobs StartNext queued with result %s.\r\n", AwsIotJobs_strerror( xStatus ) ) );

	/* Get the action for this device. */
	if( prvGetJsonString( pcJobDoc,
						  xJobDocLength,
						  jobsexampleACTION_KEY,
						  jobsexampleACTION_KEY_LENGTH,
						  &pcAction,
						  &xActionLength ) == pdTRUE )
	{
		xAction = prvGetAction( pcAction, xActionLength );

		switch( xAction )
		{
			case JOB_ACTION_EXIT:
				xCallbackInfo.pCallbackContext = jobsexampleSHOULD_EXIT;
				xUpdateInfo.newStatus = AWS_IOT_JOB_STATE_SUCCEEDED;
				break;

			case JOB_ACTION_PRINT:
			case JOB_ACTION_PUBLISH:
				xUpdateInfo.newStatus = prvProcessMessage( pxJobInfo->mqttConnection,
														   xAction,
														   pcJobDoc,
														   xJobDocLength );
				break;

			default:
				configPRINTF( ( "Received Job document with unknown action %.*s.\r\n",
								xActionLength,
								pcAction ) );

				xUpdateInfo.newStatus = AWS_IOT_JOB_STATE_FAILED;
				break;
		}
	}
	else
	{
		configPRINTF( ( "Received Job document does not contain an %s key.\r\n",
						jobsexampleACTION_KEY ) );

		/* The given Job document is not valid for this demo. */
		xUpdateInfo.newStatus = AWS_IOT_JOB_STATE_FAILED;
	}

	configPRINTF( ( "Setting state of %.*s to %s.\r\n",
					xJobIdLength,
					pcJobId,
					AwsIotJobs_StateName( xUpdateInfo.newStatus ) ) );

	/* Tell the Jobs service that the device has finished the Job. */
	xStatus = AwsIotJobs_UpdateAsync( &xRequestInfo, &xUpdateInfo, 0, &xCallbackInfo, NULL );

	configPRINTF( ( "Jobs Update queued with result %s.\r\n", AwsIotJobs_strerror( xStatus ) ) );
}
/*-----------------------------------------------------------*/

static void prvJobsCallback( void * pCallbackContext,
							 AwsIotJobsCallbackParam_t * pxCallbackInfo )
{
BaseType_t xIdKeyFound = pdFALSE, xDocKeyFound = pdFALSE;
const char * pcJobId = NULL;
size_t xJobIdLength = 0;
const char * pcJobDoc = NULL;
size_t xJobDocLength = 0;
const char * pcRawDocument = NULL;
size_t xRawDocumentLength = 0;

	/* Silence warnings about unused parameters. */
	( void ) pCallbackContext;

	configASSERT( pxCallbackInfo != NULL );

	/* Check if this callback was called from a describe operation or
	 * due to notify-next. */
	if( pxCallbackInfo->callbackType == AWS_IOT_JOBS_DESCRIBE_COMPLETE )
	{
		pcRawDocument = pxCallbackInfo->u.operation.pResponse;
		xRawDocumentLength = pxCallbackInfo->u.operation.responseLength;
	}
	else
	{
		pcRawDocument = pxCallbackInfo->u.callback.pDocument;
		xRawDocumentLength = pxCallbackInfo->u.callback.documentLength;
	}

	/* Get the Job ID. */
	xIdKeyFound = prvGetJsonString( pcRawDocument,
									xRawDocumentLength,
									jobsexampleID_KEY,
									jobsexampleID_KEY_LENGTH,
									&pcJobId,
									&xJobIdLength );

	if( xIdKeyFound == pdTRUE )
	{
		if( xJobIdLength > jobsexampleID_MAX_LENGTH )
		{
			configPRINTF( ( "Received Job ID %.*s longer than %lu, which is the "
							"maximum allowed by AWS IoT. Ignoring Job.\r\n",
							xJobIdLength,
							pcJobId,
							( unsigned long ) jobsexampleID_MAX_LENGTH ) );

			xIdKeyFound = pdFALSE;
		}
		else
		{
			configPRINTF( ( "Job %.*s received.\r\n", xJobIdLength, pcJobId ) );
		}
	}

	/* Get the Job document.
	 *
	 * Note: This parser used is specific for parsing AWS IoT document received
	 * through a mutually authenticated connection. This parser will not check
	 * for the correctness of the document as it is designed for low memory
	 * footprint rather than checking for correctness of the document. This
	 * parser is not meant to be used as a general purpose JSON parser.
	 */
	xDocKeyFound = ( BaseType_t ) AwsIotDocParser_FindValue(
		pcRawDocument,
		xRawDocumentLength,
		jobsexampleDOC_KEY,
		jobsexampleDOC_KEY_LENGTH,
		&pcJobDoc,
		&xJobDocLength );

	/* When both the Job ID and Job document are available, process the Job. */
	if( ( xIdKeyFound == pdTRUE ) && ( xDocKeyFound == pdTRUE ) )
	{
		/* Process the Job document. */
		prvProcessJob( pxCallbackInfo,
					   pcJobId,
					   xJobIdLength,
					   pcJobDoc,
					   xJobDocLength );
	}
	else
	{
		/* The Jobs service sends an empty Job document when all Jobs are complete. */
		if( ( xIdKeyFound == pdFALSE ) && ( xDocKeyFound == pdFALSE ) )
		{
			configPRINTF( (
							  "\r\n"
							  "/*-----------------------------------------------------------*/\r\n"
							  "\r\n"
							  "All available Jobs complete.\r\n"
							  "\r\n"
							  "/*-----------------------------------------------------------*/\r\n"
							  "\r\n" ) );
		}
		else
		{
			configPRINTF( ( "Received an invalid Job document: %.*s\r\n",
							xRawDocumentLength,
							pcRawDocument ) );
		}
	}
}
/*-----------------------------------------------------------*/
