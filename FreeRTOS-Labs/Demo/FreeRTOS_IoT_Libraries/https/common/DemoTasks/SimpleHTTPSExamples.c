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
 * authentication HTTPS demos. Aside from the difference in security level during
 * connect, the three demos perform the same interaction with a HTTPS host. The
 * demo creates a singe application task that loops through a set of examples
 * demonstrating how to the connect to the server, send a few types of requests to
 * the server (GET, HEAD, PUT, POST), and disconnect from the server again. All
 * of the responses and their associated HTTPS response status codes are printed
 * to the console.
 *
 * The plain text HTTP demo does not authenticate the server nor the client. The
 * basic TLS HTTPS demo builds on top of the plain text demo, adding broker
 * authentication and encryption. The mutual authentication HTTPS demo builds on
 * top of the basic TLS demo, enabling both server and client authentication.
 *
 * For more information regarding the HTTPS library and the demo, please refer to:
 * https://www.freertos.org/https/index.html
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
#include "iot_https_client.h"
#include "iot_taskpool_freertos.h"
#include "platform/iot_network_freertos.h"

/* HTTPS Demo Select */
#include "demo_config.h"

/* Select HTTPS profile based on the setting in demo_config.h */
#if ( democonfigPROFILE_USE_AWS_IOT == 1 )
	#include "aws_iot_demo_profile.h"
#else
	#include "https_demo_profile.h"
#endif

/* Preprocessor check iot configuration */
#include "aws_iot_setup_check.h"

/*
 * Set the connection profile based on settings in demo_config.h. For more
 * information on each variable, please refer to the respective *_profile.h
 * file in FreeRTOS-Labs\Demo\FreeRTOS_IoT_Libraries\include.
 *
 * Note that if you are running the https_tls_mutual_auth demo please make sure
 * to visit the following link for setup:
 * https://www.freertos.org/https/preconfiguredexamplesMA.html
 */
#if defined( AWS_IOT_DEMO_PROFILE_H )
	#define httpsexampleHTTPS_SERVER_ADDRESS		awsiotdemoprofileAWS_ENDPOINT
	#define httpsexampleHTTPS_SERVER_PORT			awsiotdemoprofileAWS_HTTPS_PORT
	#define httpsexampleHTTPS_SERVER_CERTIFICATE	awsiotdemoprofileAWS_CERTIFICATE_PEM
	#define httpsexampleCLIENT_CERTIFICATE_PEM		awsiotdemoprofileCLIENT_CERTIFICATE_PEM
	#define httpsexampleCLIENT_PRIVATE_KEY_PEM		awsiotdemoprofileCLIENT_PRIVATE_KEY_PEM
#elif defined( HTTPS_DEMO_PROFILE_H )
	#define httpsexampleHTTPS_SERVER_ADDRESS		httpsdemoprofileSERVER_ADDRESS
	#define httpsexampleHTTPS_SERVER_PORT			httpsdemoprofileSERVER_PORT
	#define httpsexampleHTTPS_SERVER_CERTIFICATE	httpsdemoprofileSERVER_CERTIFICATE_PEM
#endif

/*
 * Each preconfigured host supports different request paths. In this demo, we
 * are using httpbin and AWS IoT.
 *
 * In the demos that uses httpbin.org see http://httpbin.org/#/HTTP_Methods for
 * details on supported REST API.
 **/
#if defined( AWS_IOT_DEMO_PROFILE_H )
	#define httpsexampleHTTPS_POST_PATH	   "/topics/" awsiotdemoprofileCLIENT_IDENTIFIER
#elif defined( HTTPS_DEMO_PROFILE_H )
	#define httpsexampleHTTPS_GET_PATH	   "/ip"
	#define httpsexampleHTTPS_HEAD_PATH	   "/ip"
	#define httpsexampleHTTPS_PUT_PATH	   "/put"
	#define httpsexampleHTTPS_POST_PATH	   "/post"
#endif

/**
 * @brief The length in bytes of the user buffer to store the HTTPS Client library
 * connection context.
 *
 * The minimum size can be found in @ref connectionUserBufferMinimumSize.
 */
#define httpsexampleCONNECTION_USER_BUFFER_LENGTH	 ( 512 )

/**
 * @brief The length in bytes of the user buffer to store the HTTPS Client library
 * request context.
 *
 * The minimum size can be found in @ref requestUserBufferMinimumSize.
 */
#define httpsexampleREQUEST_USER_BUFFER_LENGTH		 ( 512 )

/**
 * @brief The length in bytes of the user buffer to store the HTTPS Client library
 * response context.
 */
#define httpsexampleRESPONSE_USER_BUFFER_LENGTH		 ( 512 )

/**
 * @brief Some text to send as the request body for a PUT and POST request in
 * this examples.
 */
#define httpsexampleREQUEST_BODY_TEXT				 "Hello, world!"

/**
 * @brief The length in bytes of the buffer used to receive the response body.
 */
#define httpsexampleRESPONSE_BODY_BUFFER_LENGTH		 ( 512 )

/**
 * @brief Timeout in ms for HTTPS operations in this example.
 */
#define httpsexampleHTTPS_TIMEOUT_MS				 ( 5000 )

/*-----------------------------------------------------------*/

/**
 * @brief The HTTPS connection handle used in this example.
 */
static IotHttpsConnectionHandle_t xHTTPSConnection = IOT_HTTPS_CONNECTION_HANDLE_INITIALIZER;

/**
 * @brief A buffer used to store the HTTPS Client library's connection context.
 */
static uint8_t ucHTTPSConnectionUserBuffer[ httpsexampleCONNECTION_USER_BUFFER_LENGTH ] = { 0 };

/**
 * @brief A buffer used to store the HTTPS Client library's request context and
 * some headers.
 */
static uint8_t ucHTTPSRequestUserBuffer[ httpsexampleREQUEST_USER_BUFFER_LENGTH ] = { 0 };

/**
 * @brief A buffer used to store the HTTPS Client library's response context and
 * some headers.
 */
static uint8_t ucHTTPSResponseUserBuffer[ httpsexampleRESPONSE_USER_BUFFER_LENGTH ] = { 0 };

/**
 * @brief The request body.
 */
static char cHTTPSRequestBodyBuffer[] = httpsexampleREQUEST_BODY_TEXT;

/**
 * @brief A buffer used to receive the HTTPS Client library's response body.
 */
static uint8_t ucHTTPSResponseBodyBuffer[ httpsexampleRESPONSE_BODY_BUFFER_LENGTH ] = { 0 };

/**
 * @brief The task used to demonstrate the HTTPS Client API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 *            used in this example.
 */
static void prvHTTPSDemoTask( void * pvParameters );

/**
 * @brief Connects to the HTTPS server as specified in httpsexampleHTTPS_SERVER_ADDRESS
 * and httpsexampleHTTPS_SERVER_PORT.
 */
static void prvHTTPSConnect( void );

/**
 * @brief Creates and sends an HTTPS request to the HTTPS server specified in
 * httpsexampleHTTPS_SERVER_ADDRESS and httpsexampleHTTPS_SERVER_PORT.
 *
 * @param[in] xMethod The HTTPS method to use. Please #IotHttpsMethod_t for
 *            possible parameters.
 * @param[in] pcPath The path for the HTTPS request.
 * @param[in] ulPathLength The length of the input pcPath.
 */
static void prvHTTPSRequest( IotHttpsMethod_t xMethod,
							 const char * pcPath,
							 uint32_t ulPathLength );

/**
 * @brief Disconnects from the HTTPS server.
 */
static void prvHTTPSDisconnect( void );

/**
* @brief Initializes the IoT libraries used by this demo.
*/
static void prvInitialiseLibraries( void );

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

static const IotHttpsConnectionInfo_t xConnectionInfo =
{
	/* No connection to the HTTPS server has been established yet and we want to
	 * establish a new connection. */
	.pAddress = httpsexampleHTTPS_SERVER_ADDRESS,
	.addressLen = sizeof( httpsexampleHTTPS_SERVER_ADDRESS ) - 1,
	.port = httpsexampleHTTPS_SERVER_PORT,
	.userBuffer.pBuffer = ucHTTPSConnectionUserBuffer,
	.userBuffer.bufferLen = sizeof( ucHTTPSConnectionUserBuffer ),

	/* Use FreeRTOS+TCP network. */
	.pNetworkInterface = IOT_NETWORK_INTERFACE_FREERTOS,

	/* The HTTPS Client library uses TLS by default as indicated by the "S"
	 * postfixed to "HTTP" in the name of the library and its types and
	 * functions. There are no configurations in the flags to enable TLS. */
	.flags = 0,

	/* Optional TLS extensions. For this demo, they are disabled. */
	.pAlpnProtocols = NULL,
	.alpnProtocolsLen = 0,

	/* Provide the certificate for authenticating the server. */
	#if ( democonfigENABLE_TLS == 1 )
		.pCaCert = httpsexampleHTTPS_SERVER_CERTIFICATE,
		.caCertLen = sizeof( httpsexampleHTTPS_SERVER_CERTIFICATE ),
	#else
		.pCaCert = NULL,
		.caCertLen = 0,
	#endif

	/* The HTTPS server at httpbin.org:443 does not require client certificates,
	 * but AWS IoT does.
	 * If the server were to require a client certificate, the following members
	 * need to be set. */
	#if ( democonfigENABLE_MUTUAL_AUTH == 1 )
		.pClientCert = httpsexampleCLIENT_CERTIFICATE_PEM,
		.clientCertLen = sizeof( httpsexampleCLIENT_CERTIFICATE_PEM ),
		.pPrivateKey = httpsexampleCLIENT_PRIVATE_KEY_PEM,
		.privateKeyLen = sizeof( httpsexampleCLIENT_PRIVATE_KEY_PEM )
	#else
		.pClientCert = NULL,
		.clientCertLen = 0,
		.pPrivateKey = NULL,
		.privateKeyLen = 0
	#endif
};
/*-----------------------------------------------------------*/

void vStartSimpleHTTPSDemo( void )
{
	/* This example uses a single application task, which in turn is used to
	* connect, send a few requests, and disconnect from the HTTPS server. */
	xTaskCreate( prvHTTPSDemoTask,         /* Function that implements the task. */
				 "HTTPSDemo",              /* Text name for the task - only used for debugging. */
				 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,                     /* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvHTTPSDemoTask( void * pvParameters )
{
	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* One time initialization of the libraries used by this demo. */
	prvInitialiseLibraries();

	for( ; ; )
	{
		/****************************** Connect. ******************************/

		/* Establish a connection to the HTTPS server. This example connects to
		 * the HTTPS server as specified in httpsexampleHTTPS_SERVER_ADDRESS and
		 * httpsexampleHTTPS_SERVER_PORT at the top of this file. Please change
		 * it to the HTTPS server you want to connect to. */
		configPRINTF( ( "Attempt to connect to %s:%d\r\n", httpsexampleHTTPS_SERVER_ADDRESS, httpsexampleHTTPS_SERVER_PORT ) );
		prvHTTPSConnect();
		configPRINTF( ( "Connected to %s:%d\r\n", httpsexampleHTTPS_SERVER_ADDRESS, httpsexampleHTTPS_SERVER_PORT ) );

		/*********************** Send HTTPS requests. ************************/

		/* The client is now connected to the server. This example will send a
		 * GET, HEAD, PUT, and POST request. For AWS IoT profile, the example will
		 * only send a POST request.
		 **/
		#if defined( httpsexampleHTTPS_GET_PATH )
			configPRINTF( ( "Sending HTTPS GET request...\r\n" ) );
			prvHTTPSRequest( IOT_HTTPS_METHOD_GET,
							 httpsexampleHTTPS_GET_PATH,
							 sizeof( httpsexampleHTTPS_GET_PATH ) - 1 );
		#endif
		#if defined( httpsexampleHTTPS_HEAD_PATH )
			configPRINTF( ( "Sending HTTPS HEAD request...\r\n" ) );
			prvHTTPSRequest( IOT_HTTPS_METHOD_HEAD,
							 httpsexampleHTTPS_HEAD_PATH,
							 sizeof( httpsexampleHTTPS_HEAD_PATH ) - 1 );
		#endif
		#if defined( httpsexampleHTTPS_PUT_PATH )
			configPRINTF( ( "Sending HTTPS PUT request...\r\n" ) );
			prvHTTPSRequest( IOT_HTTPS_METHOD_PUT,
							 httpsexampleHTTPS_PUT_PATH,
							 sizeof( httpsexampleHTTPS_PUT_PATH ) - 1 );
		#endif
		#if defined( httpsexampleHTTPS_POST_PATH )
			configPRINTF( ( "Sending HTTPS POST request...\r\n" ) );
			prvHTTPSRequest( IOT_HTTPS_METHOD_POST,
							 httpsexampleHTTPS_POST_PATH,
							 sizeof( httpsexampleHTTPS_POST_PATH ) - 1 );
		#endif

		/**************************** Disconnect. *****************************/

		prvHTTPSDisconnect();
		configPRINTF( ( "Disconnected from %s:%d\r\n\r\n", httpsexampleHTTPS_SERVER_ADDRESS, httpsexampleHTTPS_SERVER_PORT ) );

		/* Wait between iterations to avoid server throttling. */

		configPRINTF( ( "prvHTTPSDemoTask() completed an iteration successfully. "
						"Total free heap is %u\r\n",
						xPortGetFreeHeapSize() ) );
		configPRINTF( ( "Demo completed successfully.\r\n" ) );
		configPRINTF( ( "Short delay before starting the next iteration.... \r\n\r\n" ) );
		vTaskDelay( pdMS_TO_TICKS( httpsexampleHTTPS_TIMEOUT_MS ) );
	}
}

/*-----------------------------------------------------------*/

static void prvHTTPSConnect( void )
{
IotHttpsReturnCode_t xHTTPSClientResult;

	/* Establish the connection to the HTTPS server - It is a blocking call and
	 * will return only when the connection is complete or a timeout occurs. */
	xHTTPSClientResult = IotHttpsClient_Connect( &( xHTTPSConnection ),
												 &( xConnectionInfo ) );
	configASSERT( xHTTPSClientResult == IOT_HTTPS_OK );
}

/*-----------------------------------------------------------*/

static void prvHTTPSRequest( IotHttpsMethod_t xMethod,
							 const char * pcPath,
							 uint32_t ulPathLength )
{
IotHttpsReturnCode_t xHTTPSClientResult;
IotHttpsRequestInfo_t xHTTPSRequestInfo = IOT_HTTPS_REQUEST_INFO_INITIALIZER;
IotHttpsResponseInfo_t xHTTPSResponseInfo = IOT_HTTPS_RESPONSE_INFO_INITIALIZER;
IotHttpsRequestHandle_t xHTTPSRequest = IOT_HTTPS_REQUEST_HANDLE_INITIALIZER;
IotHttpsResponseHandle_t xHTTPSResponse = IOT_HTTPS_RESPONSE_HANDLE_INITIALIZER;
IotHttpsSyncInfo_t xHTTPSSyncRequestInfo = IOT_HTTPS_SYNC_INFO_INITIALIZER;
IotHttpsSyncInfo_t xHTTPSSyncResponseInfo = IOT_HTTPS_SYNC_INFO_INITIALIZER;
uint16_t usResponseStatus = 0;

	configASSERT( pcPath != NULL );

	/************************** HTTPS request setup. ***************************/

	if( ( xMethod == IOT_HTTPS_METHOD_PUT ) || ( xMethod == IOT_HTTPS_METHOD_POST ) )
	{
		xHTTPSSyncRequestInfo.pBody = ( uint8_t * ) cHTTPSRequestBodyBuffer;
		xHTTPSSyncRequestInfo.bodyLen = sizeof( cHTTPSRequestBodyBuffer );
	}
	else
	{
		xHTTPSSyncRequestInfo.pBody = NULL;
		xHTTPSSyncRequestInfo.bodyLen = 0;
	}

	xHTTPSRequestInfo.pHost = httpsexampleHTTPS_SERVER_ADDRESS;
	xHTTPSRequestInfo.hostLen = sizeof( httpsexampleHTTPS_SERVER_ADDRESS ) - 1;
	xHTTPSRequestInfo.pPath = pcPath;
	xHTTPSRequestInfo.pathLen = ulPathLength;
	xHTTPSRequestInfo.method = xMethod;
	xHTTPSRequestInfo.isNonPersistent = false;
	xHTTPSRequestInfo.userBuffer.pBuffer = ucHTTPSRequestUserBuffer;
	xHTTPSRequestInfo.userBuffer.bufferLen = sizeof( ucHTTPSRequestUserBuffer ) - 1;
	xHTTPSRequestInfo.isAsync = false;
	xHTTPSRequestInfo.u.pSyncInfo = &xHTTPSSyncRequestInfo;

	xHTTPSClientResult = IotHttpsClient_InitializeRequest( &( xHTTPSRequest ),
														   &( xHTTPSRequestInfo ) );
	configASSERT( xHTTPSClientResult == IOT_HTTPS_OK );

	/************************** HTTPS response setup. **************************/

	memset( ucHTTPSResponseBodyBuffer, 0, sizeof( ucHTTPSResponseBodyBuffer ) );

	if( xMethod == IOT_HTTPS_METHOD_HEAD )
	{
		xHTTPSSyncResponseInfo.pBody = NULL;
		xHTTPSSyncResponseInfo.bodyLen = 0;
	}
	else
	{
		xHTTPSSyncResponseInfo.pBody = ucHTTPSResponseBodyBuffer;
		xHTTPSSyncResponseInfo.bodyLen = sizeof( ucHTTPSResponseBodyBuffer );
	}

	xHTTPSResponseInfo.userBuffer.pBuffer = ucHTTPSResponseUserBuffer;
	xHTTPSResponseInfo.userBuffer.bufferLen = sizeof( ucHTTPSResponseUserBuffer );
	xHTTPSResponseInfo.pSyncInfo = &xHTTPSSyncResponseInfo;

	/*************************** Send HTTPS request. ***************************/

	/* This synchronous send function blocks until the full response is received
	 * from the network. */
	xHTTPSClientResult = IotHttpsClient_SendSync( xHTTPSConnection,
												  xHTTPSRequest,
												  &( xHTTPSResponse ),
												  &( xHTTPSResponseInfo ),
												  httpsexampleHTTPS_TIMEOUT_MS );
	configASSERT( xHTTPSClientResult == IOT_HTTPS_OK );

	/* The response status is only available if the httpsexampleRESPONSE_USER_BUFFER
	 * is large enough to fit not only the HTTPS Client response context, but
	 * also the Status-Line of the response. The Status-Line and the response
	 * headers are stored in the provided ucHTTPSResponseUserBuffer right after
	 * the HTTPS Client response context. */
	xHTTPSClientResult = IotHttpsClient_ReadResponseStatus( xHTTPSResponse,
															&usResponseStatus );
	configASSERT( xHTTPSClientResult == IOT_HTTPS_OK );

	configPRINTF( ( "Response status: %d\r\n", usResponseStatus ) );
	configPRINTF( ( "Response body: \r\n%s\r\n", ucHTTPSResponseBodyBuffer ) );

	/* The response body may be too large for the print buffer. These extra
	 * carriage returns and newlines help with clobbering. */
	configPRINTF( ( "\r\n\r\n" ) );
}

/*-----------------------------------------------------------*/

static void prvHTTPSDisconnect( void )
{
IotHttpsReturnCode_t xHTTPSClientResult;

	/* The application must always explicitly disconnect from the server with
	 * this API if the last request sent on the connection was a persistent
	 * request. */
	xHTTPSClientResult = IotHttpsClient_Disconnect( xHTTPSConnection );
	configASSERT( xHTTPSClientResult == IOT_HTTPS_OK );
}


static void prvInitialiseLibraries( void )
{
IotTaskPoolError_t xTaskPoolResult;
IotHttpsReturnCode_t xHTTPSClientResult;
IotNetworkError_t xNetworkResult;

	/* The HTTPS Client library needs a task pool, so create the system task pool. */
	xTaskPoolResult = IotTaskPool_CreateSystemTaskPool( &( xTaskPoolParameters ) );
	configASSERT( xTaskPoolResult == IOT_TASKPOOL_SUCCESS );

	/* Initialize the network stack abstraction for FreeRTOS. */
	xNetworkResult = IotNetworkFreeRTOS_Init();
	configASSERT( xNetworkResult == IOT_NETWORK_SUCCESS );

	/* HTTPS Client library must be initialized before it can be used. This is
	 * just one time initialization. */
	xHTTPSClientResult = IotHttpsClient_Init();
	configASSERT( xHTTPSClientResult == IOT_HTTPS_OK );
}
