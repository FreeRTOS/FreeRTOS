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

/*-----------------------------------------------------------*/

#define otaDemoCONN_TIMEOUT_MS			( 2000UL )

#define otaDemoKEEPALIVE_SECONDS		( 1200 )

#define myappONE_SECOND_DELAY_IN_TICKS	pdMS_TO_TICKS( 1000UL )

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
	.disconnectCallback.function = NULL
};

/**
 * @brief The MQTT connection handle used in this example.
 */
static IotMqttConnection_t xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;
/*-----------------------------------------------------------*/


void vOTAUpdateDemoTask( void * pvParameters )
{
IotMqttConnectInfo_t xConnectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
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
		memset( &xConnectInfo, 0, sizeof( xConnectInfo ) );

		xConnectInfo.awsIotMqttMode = true;
		xConnectInfo.keepAliveSeconds = otaDemoKEEPALIVE_SECONDS;

		xConnectInfo.cleanSession = true;
		xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( awsiotdemoprofileCLIENT_IDENTIFIER );
		xConnectInfo.pClientIdentifier = awsiotdemoprofileCLIENT_IDENTIFIER;

		/* Connect to the broker. */
		if( IotMqtt_Connect( &( xNetworkInfo ),
							 &xConnectInfo,
							 otaDemoCONN_TIMEOUT_MS, &xMQTTConnection ) == IOT_MQTT_SUCCESS )
		{
			configPRINTF( ( "Connected to broker.\r\n" ) );
			xOTAConnectionCtx.pvControlClient = xMQTTConnection;
			xOTAConnectionCtx.pxNetworkInterface = ( void * ) IOT_NETWORK_INTERFACE_FREERTOS;
			xOTAConnectionCtx.pvNetworkCredentials = &xNetworkSecurityCredentials;

			OTA_AgentInit( ( void * ) ( &xOTAConnectionCtx ), ( const uint8_t * ) ( awsiotdemoprofileCLIENT_IDENTIFIER ), App_OTACompleteCallback, ( TickType_t ) ~0 );

			while( ( eState = OTA_GetAgentState() ) != eOTA_AgentState_Stopped )
			{
				/* Wait forever for OTA traffic but allow other tasks to run and output statistics only once per second. */
				vTaskDelay( myappONE_SECOND_DELAY_IN_TICKS );
				configPRINTF( ( "State: %s  Received: %u   Queued: %u   Processed: %u   Dropped: %u\r\n", pcStateStr[ eState ],
								OTA_GetPacketsReceived(), OTA_GetPacketsQueued(), OTA_GetPacketsProcessed(), OTA_GetPacketsDropped() ) );
			}

			IotMqtt_Disconnect( xMQTTConnection, false );
		}
		else
		{
			configPRINTF( ( "ERROR:  Failed to connect to MQTT broker.\r\n" ) );
		}

		/* After failure to connect or a disconnect, wait an arbitrary one second before retry. */
		vTaskDelay( myappONE_SECOND_DELAY_IN_TICKS );
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
