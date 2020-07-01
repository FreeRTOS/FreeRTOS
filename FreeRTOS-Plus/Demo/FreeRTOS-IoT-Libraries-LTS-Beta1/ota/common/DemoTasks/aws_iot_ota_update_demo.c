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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file aws_ota_update_demo.c
 * @brief A simple OTA update example.
 *
 * This example initializes the OTA agent to enable OTA updates via the
 * MQTT broker. It simply connects to the MQTT broker with the users
 * credentials and spins in an indefinite loop to allow MQTT messages to be
 * forwarded to the OTA agent for possible processing. The OTA agent does all
 * of the real work; checking to see if the message topic is one destined for
 * the OTA agent. If not, it is simply ignored.
 */
/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* IoT SDK includes. */
#include "iot_mqtt.h"
#include "platform/iot_network_freertos.h"
#include "platform/iot_clock.h"

/* Required to get the broker address and port. */
#include "aws_iot_demo_profile.h"

/* FreeRTOS OTA agent includes. */
#include "aws_iot_ota_agent.h"

/* Required for demo task stack and priority */
#include "demo_config.h"
#include "aws_application_version.h"

/* Preprocessor check for configuration */
#include "aws_iot_setup_check.h"

/**
 * @brief Callback invoked when a OTA finishes.
 */
static void App_OTACompleteCallback( OTA_JobEvent_t eEvent );

/**
 * @brief Initializes the IoT libraries used by this demo.
 */
static void prvInitialiseLibraries( void );

/**
 * @brief Delay before retrying network connection up to a maximum interval.
 */
static void _connectionRetryDelay( void );

/**
 * @brief Callback invoked when MQTT library detects a disconnection.
 *
 */

static void prvNetworkDisconnectCallback( void * param,
										  IotMqttCallbackParam_t * mqttCallbackParams );


/**
 * @brief Establish a new connection to the MQTT server.
 *
 * @param[in] awsIotMqttMode Specify if this demo is running with the AWS IoT
 * MQTT server. Set this to `false` if using another MQTT server.
 * @param[in] pIdentifier NULL-terminated MQTT client identifier.
 * @param[in] pNetworkServerInfo Passed to the MQTT connect function when
 * establishing the MQTT connection.
 * @param[in] pNetworkCredentialInfo Passed to the MQTT connect function when
 * establishing the MQTT connection.
 * @param[in] pNetworkInterface The network interface to use for this demo.
 * @param[out] pMqttConnection Set to the handle to the new MQTT connection.
 *
 * @return `IOT_MQTT_SUCCESS` if the connection is successfully established; Otherwise
 * error code returned by `IotMqtt_Connect`.
 */
static IotMqttError_t _establishMqttConnection( bool awsIotMqttMode,
									 IotMqttConnection_t * pMqttConnection );
/*-----------------------------------------------------------*/

#define otaDemoCONN_TIMEOUT_MS					   ( 2000UL )

#define otaDemoKEEPALIVE_SECONDS				   ( 120 )

#define otaDemoCONN_RETRY_BASE_INTERVAL_SECONDS	   ( 4U )

#define otaDemoCONN_RETRY_MAX_INTERVAL_SECONDS	   ( 360U )

#define otaDemoTASK_DELAY_SECONDS				   ( 1UL )

/**
 * @brief OTA state machine string.
 */
static const char * pcStateStr[ eOTA_AgentState_All ] =
{
	"Init",
	"Ready",
	"RequestingJob",
	"WaitingForJob",
	"CreatingFile",
	"RequestingFileBlock",
	"WaitingForFileBlock",
	"ClosingFile",
	"ShuttingDown",
	"Stopped"
};

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
	 * demos using TLS. */
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
	.disconnectCallback.function = prvNetworkDisconnectCallback
};

/**
 * @brief The MQTT connection handle used in this example.
 */
static IotMqttConnection_t xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/**
 * @brief The MQTT connection info used for MQTT connection.
 */
IotMqttConnectInfo_t xConnectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

/**
 * @brief Flag used to unset, during disconnection of currently connected network. This will
 * trigger a reconnection from the OTA demo task.
 */
volatile static bool _networkConnected = false;

/**
 * @brief Connection retry interval in seconds.
 */
static int _retryInterval = otaDemoCONN_RETRY_BASE_INTERVAL_SECONDS;
/*-----------------------------------------------------------*/


void vOTAUpdateDemoTask( void * pvParameters )
{
OTA_State_t eState;
OTA_ConnectionContext_t xOTAConnectionCtx = { 0 };

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* One time initialization of the libraries used by this demo. */
	prvInitialiseLibraries();

	configPRINTF( ( "OTA demo version %u.%u.%u\r\n",
					xAppFirmwareVersion.u.x.ucMajor,
					xAppFirmwareVersion.u.x.ucMinor,
					xAppFirmwareVersion.u.x.usBuild ) );
	configPRINTF( ( "Creating MQTT Client...\r\n" ) );

	/* Create the MQTT Client. */

	for( ; ; )
	{
		configPRINTF( ( "Connecting to broker...\r\n" ) );

		/* Establish a new MQTT connection. */
		if( _establishMqttConnection( true,
									  &xMQTTConnection ) == IOT_MQTT_SUCCESS )
		{
			configPRINTF( ( "Connected to broker.\r\n" ) );
			xOTAConnectionCtx.pvControlClient = xMQTTConnection;
			xOTAConnectionCtx.pxNetworkInterface = ( void * ) IOT_NETWORK_INTERFACE_FREERTOS;
			xOTAConnectionCtx.pvNetworkCredentials = &xNetworkSecurityCredentials;

			/* Set the base interval for connection retry.*/
			_retryInterval = otaDemoCONN_RETRY_BASE_INTERVAL_SECONDS;

			/* Update the connection available flag.*/
			_networkConnected = true;

			/* Check if OTA Agent is suspended and resume.*/
			if( ( eState = OTA_GetAgentState() ) == eOTA_AgentState_Suspended )
			{
				OTA_Resume( &xOTAConnectionCtx );
			}

			/* Check if OTA Agent is suspended and resume.*/
			if( ( eState = OTA_GetAgentState() ) == eOTA_AgentState_Suspended )
			{
				OTA_Resume( &xOTAConnectionCtx );
			}

			/* Initialize the OTA Agent , if it is resuming the OTA statistics will be cleared for new connection.*/
			OTA_AgentInit( ( void * ) ( &xOTAConnectionCtx ), ( const uint8_t * ) ( awsiotdemoprofileCLIENT_IDENTIFIER ), App_OTACompleteCallback, ( TickType_t ) ~0 );

			while( ( ( eState = OTA_GetAgentState() ) != eOTA_AgentState_Stopped ) && _networkConnected )
			{
				/* Wait forever for OTA traffic but allow other tasks to run and output statistics only once per second. */
				IotClock_SleepMs( otaDemoTASK_DELAY_SECONDS * 1000 );

				configPRINTF( ( "State: %s  Received: %u   Queued: %u   Processed: %u   Dropped: %u\r\n", pcStateStr[ eState ],
								OTA_GetPacketsReceived(), OTA_GetPacketsQueued(), OTA_GetPacketsProcessed(), OTA_GetPacketsDropped() ) );
			}

			/* Check if we got network disconnect callback and suspend OTA Agent.*/
			if( _networkConnected == false )
			{
				/* Suspend OTA agent.*/
				if( OTA_Suspend() == kOTA_Err_None )
				{
					while( ( eState = OTA_GetAgentState() ) != eOTA_AgentState_Suspended )
					{
						/* Wait for OTA Agent to process the suspend event. */
						IotClock_SleepMs( otaDemoTASK_DELAY_SECONDS * 1000 );
					}
				}
			}
			else
			{
				IotMqtt_Disconnect( xMQTTConnection, false );
			}
		}
		else
		{
			configPRINTF( ( "ERROR:  Failed to connect to MQTT broker.\r\n" ) );
		}

		/* After failure to connect or a disconnect, delay for retrying connection. */
		_connectionRetryDelay();
	}
}


/* The OTA agent has completed the update job or determined that we're in
 * self test mode. If it was accepted, we want to activate the new image.
 * This typically means we should reset the device to run the new firmware.
 * If now is not a good time to reset the device, it may be activated later
 * by your user code. If the update was rejected, just return without doing
 * anything and we'll wait for another job. If it reported that we should
 * start test mode, normally we would perform some kind of system checks to
 * make sure our new firmware does the basic things we think it should do
 * but we'll just go ahead and set the image as accepted for demo purposes.
 * The accept function varies depending on your platform. Refer to the OTA
 * PAL implementation for your platform in aws_ota_pal.c to see what it
 * does for you.
 */

static void App_OTACompleteCallback( OTA_JobEvent_t eEvent )
{
OTA_Err_t xErr = kOTA_Err_Uninitialized;


	/* OTA job is completed. so delete the MQTT and network connection. */
	if( eEvent == eOTA_JobEvent_Activate )
	{
		configPRINTF( ( "Received eOTA_JobEvent_Activate callback from OTA Agent.\r\n" ) );
		IotMqtt_Disconnect( xMQTTConnection, 0 );
		OTA_ActivateNewImage();

		/* We should never get here as new image activation must reset the device.*/
		for( ; ; )
		{
			IotClock_SleepMs( otaDemoTASK_DELAY_SECONDS * 1000 );
		}
	}
	else if( eEvent == eOTA_JobEvent_Fail )
	{
		configPRINTF( ( "Received eOTA_JobEvent_Fail callback from OTA Agent.\r\n" ) );
		/* Nothing special to do. The OTA agent handles it. */
	}
	else if( eEvent == eOTA_JobEvent_StartTest )
	{
		/* This demo just accepts the image since it was a good OTA update and networking
		 * and services are all working (or we wouldn't have made it this far). If this
		 * were some custom device that wants to test other things before calling it OK,
		 * this would be the place to kick off those tests before calling OTA_SetImageState()
		 * with the final result of either accepted or rejected. */
		configPRINTF( ( "Received eOTA_JobEvent_StartTest callback from OTA Agent.\r\n" ) );
		xErr = OTA_SetImageState( eOTA_ImageState_Accepted );

		if( xErr != kOTA_Err_None )
		{
			OTA_LOG_L1( " Error! Failed to set image state as accepted.\r\n" );
		}
	}
}
/*-----------------------------------------------------------*/

void vStartOTAUpdateDemo( void )
{
	xTaskCreate( vOTAUpdateDemoTask,       /* Function that implements the task. */
				 "OTAUpdateDemo",          /* Text name for the task - only used for debugging. */
				 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,                     /* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvInitialiseLibraries( void )
{
IotMqttError_t xResult;
IotNetworkError_t xNetworkResult;

	/* Initialize the network stack abstraction for FreeRTOS. */
	xNetworkResult = IotNetworkFreeRTOS_Init();
	configASSERT( xNetworkResult == IOT_NETWORK_SUCCESS );

	/* MQTT library must be initialized before it can be used. This is just one
	 * time initialization. */
	xResult = IotMqtt_Init();
	configASSERT( xResult == IOT_MQTT_SUCCESS );
}
/*-----------------------------------------------------------*/

static void _connectionRetryDelay( void )
{
unsigned int retryIntervalwithJitter = 0;

	if( ( _retryInterval * 2 ) >= otaDemoCONN_RETRY_MAX_INTERVAL_SECONDS )
	{
		/* Retry interval is already max.*/
		_retryInterval = otaDemoCONN_RETRY_MAX_INTERVAL_SECONDS;
	}
	else
	{
		/* Double the retry interval time.*/
		_retryInterval *= 2;
	}

	/* Add random jitter upto current retry interval .*/
	retryIntervalwithJitter = _retryInterval + ( rand() % _retryInterval );

	configPRINTF( ( "Retrying network connection in %d Secs ", retryIntervalwithJitter ) );

	/* Delay for the calculated time interval .*/
	IotClock_SleepMs( retryIntervalwithJitter * 1000 );
}
/*-----------------------------------------------------------*/

static void prvNetworkDisconnectCallback( void * param,
										  IotMqttCallbackParam_t * mqttCallbackParams )
{
	( void ) param;

	/* Log the reason for MQTT disconnect.*/
	switch( mqttCallbackParams->u.disconnectReason )
	{
		case IOT_MQTT_DISCONNECT_CALLED:
			configPRINTF( ( "Mqtt disconnected due to invoking diconnect function.\r\n" ) );
			break;

		case IOT_MQTT_BAD_PACKET_RECEIVED:
			configPRINTF( ( "Mqtt disconnected due to invalid packet received from the network.\r\n" ) );
			break;

		case IOT_MQTT_KEEP_ALIVE_TIMEOUT:
			configPRINTF( ( "Mqtt disconnected due to Keep-alive response not received.\r\n" ) );
			break;

		default:
			configPRINTF( ( "Mqtt disconnected due to unknown reason." ) );
			break;
	}

	/* Clear the flag for network connection status.*/
	_networkConnected = false;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _establishMqttConnection( bool awsIotMqttMode,
												IotMqttConnection_t * pMqttConnection )
{
IotMqttError_t connectStatus = IOT_MQTT_STATUS_PENDING;

	/* Set the members of the connection info not set by the initializer. */
	memset( &xConnectInfo, 0, sizeof( xConnectInfo ) );
	xConnectInfo.awsIotMqttMode = awsIotMqttMode;
	xConnectInfo.cleanSession = true;
	xConnectInfo.keepAliveSeconds = otaDemoKEEPALIVE_SECONDS;
	xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( awsiotdemoprofileCLIENT_IDENTIFIER );
	xConnectInfo.pClientIdentifier = awsiotdemoprofileCLIENT_IDENTIFIER;

	/* Establish the MQTT connection. */
	configPRINTF( ( "MQTT demo client identifier is %.*s (length %hu).",
					xConnectInfo.clientIdentifierLength,
					xConnectInfo.pClientIdentifier,
					xConnectInfo.clientIdentifierLength ) );

	connectStatus = IotMqtt_Connect( &xNetworkInfo,
									 &xConnectInfo,
									 otaDemoCONN_TIMEOUT_MS,
									 pMqttConnection );

	if( connectStatus != IOT_MQTT_SUCCESS )
	{
		configPRINTF( ( "MQTT CONNECT returned error %s.",
						IotMqtt_strerror( connectStatus ) ) );
	}

	return connectStatus;
}
/*-----------------------------------------------------------*/
