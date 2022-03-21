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

#ifndef DEMO_CONFIG_H
#define DEMO_CONFIG_H

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Include logging header files and define logging macros in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for DEMO.
 * 3. Include the header file "logging_stack.h", if logging is enabled for DEMO.
 */

#include "logging_levels.h"

/* Logging configuration for the Demo. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "MQTTDemo"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

/* Prototype for the function used to print to console on Windows simulator
 * of FreeRTOS.
 * The function prints to the console before the network is connected;
 * then a UDP port after the network has connected. */
extern void vLoggingPrintf( const char * pcFormatString,
                            ... );

/* Map the SdkLog macro to the logging function to enable logging
 * on Windows simulator. */
#ifndef SdkLog
    #define SdkLog( message )    vLoggingPrintf message
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.
 *
 *!!! Please note a #defined constant is used for convenience of demonstration
 *!!! only.  Production devices can use something unique to the device that can
 *!!! be read by software, such as a production serial number, instead of a
 *!!! hard coded constant.
 *
 * #define democonfigCLIENT_IDENTIFIER				"insert here."
 */


/**
 * @brief Endpoint of the MQTT broker to connect to.
 *
 * This demo application can be run with any MQTT broker, although it is
 * recommended to use one that supports mutual authentication. If mutual
 * authentication is not used, then #democonfigUSE_TLS should be set to 0.
 *
 * For AWS IoT MQTT broker, this is the Thing's REST API Endpoint.
 *
 * @note Your AWS IoT Core endpoint can be found in the AWS IoT console under
 * Settings/Custom Endpoint, or using the describe-endpoint REST API (with
 * AWS CLI command line tool).
 *
 * #define democonfigMQTT_BROKER_ENDPOINT				"insert here."
 */


/**
 * @brief The port to use for the demo.
 *
 * In general, port 8883 is for secured MQTT connections, and port 1883 if not
 * using TLS.
 *
 * @note Port 443 requires use of the ALPN TLS extension with the ALPN protocol
 * name. Using ALPN with this demo would require additional changes, including
 * setting the `pAlpnProtos` member of the `NetworkCredentials_t` struct before
 * forming the TLS connection. When using port 8883, ALPN is not required.
 *
 * #define democonfigMQTT_BROKER_PORT    ( insert here. )
 */

/**
 * @brief Server's root CA certificate.
 *
 * For AWS IoT MQTT broker, this certificate is used to identify the AWS IoT
 * server and is publicly available. Refer to the AWS documentation available
 * in the link below.
 * https://docs.aws.amazon.com/iot/latest/developerguide/server-authentication.html#server-authentication-certs
 *
 * @note This certificate should be PEM-encoded.
 *
 * @note If you would like to setup an MQTT broker for running this demo,
 * please see `mqtt_broker_setup.txt`.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"\
 * "...base64 data...\n"\
 * "-----END CERTIFICATE-----\n"
 *
 * #define democonfigROOT_CA_PEM    "...insert here..."
 */

/**
 * @brief Client certificate.
 *
 * For AWS IoT MQTT broker, refer to the AWS documentation below for details
 * regarding client authentication.
 * https://docs.aws.amazon.com/iot/latest/developerguide/client-authentication.html
 *
 * @note This certificate should be PEM-encoded.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"\
 * "...base64 data...\n"\
 * "-----END CERTIFICATE-----\n"
 *
 * #define democonfigCLIENT_CERTIFICATE_PEM    "...insert here..."
 */

/**
 * @brief Client's private key.
 *
 *!!! Please note pasting a key into the header file in this manner is for
 *!!! convenience of demonstration only and should not be done in production.
 *!!! Never paste a production private key here!.  Production devices should
 *!!! store keys securely, such as within a secure element.  Additionally,
 *!!! we provide the corePKCS library that further enhances security by
 *!!! enabling securely stored keys to be used without exposing them to
 *!!! software.
 *
 * For AWS IoT MQTT broker, refer to the AWS documentation below for details
 * regarding clientauthentication.
 * https://docs.aws.amazon.com/iot/latest/developerguide/client-authentication.html
 *
 * @note This private key should be PEM-encoded.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN RSA PRIVATE KEY-----\n"\
 * "...base64 data...\n"\
 * "-----END RSA PRIVATE KEY-----\n"
 *
 * #define democonfigCLIENT_PRIVATE_KEY_PEM    "...insert here..."
 */

/**
 * @brief An option to disable Server Name Indication.
 *
 * @note When using a local Mosquitto server setup, SNI needs to be disabled
 * for an MQTT broker that only has an IP address but no hostname. However,
 * SNI should be enabled whenever possible.
 */
#define democonfigDISABLE_SNI    ( pdFALSE )

/**
 * @brief Configuration that indicates if the demo connection is made to the AWS IoT Core MQTT broker.
 *
 * If username/password based authentication is used, the demo will use appropriate TLS ALPN and
 * SNI configurations as required for the Custom Authentication feature of AWS IoT.
 * For more information, refer to the following documentation:
 * https://docs.aws.amazon.com/iot/latest/developerguide/custom-auth.html#custom-auth-mqtt
 *
 * #define democonfigUSE_AWS_IOT_CORE_BROKER    ( 1 )
 */

/**
 * @brief The username value for authenticating client to the MQTT broker when
 * username/password based client authentication is used.
 *
 * For AWS IoT MQTT broker, refer to the AWS IoT documentation below for
 * details regarding client authentication with a username and password.
 * https://docs.aws.amazon.com/iot/latest/developerguide/custom-authentication.html
 * An authorizer setup needs to be done, as mentioned in the above link, to use
 * username/password based client authentication.
 *
 * #define democonfigCLIENT_USERNAME    "...insert here..."
 */

/**
 * @brief The password value for authenticating client to the MQTT broker when
 * username/password based client authentication is used.
 *
 * For AWS IoT MQTT broker, refer to the AWS IoT documentation below for
 * details regarding client authentication with a username and password.
 * https://docs.aws.amazon.com/iot/latest/developerguide/custom-authentication.html
 * An authorizer setup needs to be done, as mentioned in the above link, to use
 * username/password based client authentication.
 *
 * #define democonfigCLIENT_PASSWORD    "...insert here..."
 */

/**
 * @brief The name of the operating system that the application is running on.
 * The current value is given as an example. Please update for your specific
 * operating system.
 */
#define democonfigOS_NAME                   "FreeRTOS"

/**
 * @brief The version of the operating system that the application is running
 * on. The current value is given as an example. Please update for your specific
 * operating system version.
 */
#define democonfigOS_VERSION                tskKERNEL_VERSION_NUMBER

/**
 * @brief The name of the hardware platform the application is running on. The
 * current value is given as an example. Please update for your specific
 * hardware platform.
 */
#define democonfigHARDWARE_PLATFORM_NAME    "WinSim"

/**
 * @brief The name of the MQTT library used and its version, following an "@"
 * symbol.
 */
#include "core_mqtt.h" /* Include coreMQTT header for MQTT_LIBRARY_VERSION macro. */
#define democonfigMQTT_LIB                              "core-mqtt@"MQTT_LIBRARY_VERSION

/**
 * @brief Whether to use mutual authentication. If this macro is not set to 1
 * or not defined, then plaintext TCP will be used instead of TLS over TCP.
 */
#define democonfigUSE_TLS                               1

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE                        configMINIMAL_STACK_SIZE

/**
 * @brief The number of simple sub-pub tasks to create.
 */
#define democonfigNUM_SIMPLE_SUB_PUB_TASKS_TO_CREATE    2
#define democonfigSIMPLE_SUB_PUB_TASK_STACK_SIZE        ( configMINIMAL_STACK_SIZE )

/**
 * @brief The length of the queue used to hold commands for the coreMQTT Agent.
 */
#define MQTT_AGENT_COMMAND_QUEUE_LENGTH                 10



/**********************************************************************************
* Error checks and derived values only below here - do not edit below here. -----*
**********************************************************************************/


/* Compile time error for some undefined configs, and provide default values
 * for others. */
#ifndef democonfigMQTT_BROKER_ENDPOINT
    #error "Please define democonfigMQTT_BROKER_ENDPOINT in demo_config.h."
#endif

#ifndef democonfigCLIENT_IDENTIFIER

/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.  Using a #define is for convenience
 * of demonstration only - production devices should use something unique to the
 * device that can be read from software - such as a production serial number.
 */
    #error  "Please define democonfigCLIENT_IDENTIFIER in demo_config.h to something unique for this device."
#endif


#if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
    #ifndef democonfigROOT_CA_PEM
        #error "Please define Root CA certificate of the MQTT broker(democonfigROOT_CA_PEM) in demo_config.h."
    #endif

/* If no username is defined, then a client certificate/key is required. */
    #ifndef democonfigCLIENT_USERNAME

/*
 *!!! Please note democonfigCLIENT_PRIVATE_KEY_PEM in used for
 *!!! convenience of demonstration only.  Production devices should
 *!!! store keys securely, such as within a secure element.
 */

        #ifndef democonfigCLIENT_CERTIFICATE_PEM
            #error "Please define client certificate(democonfigCLIENT_CERTIFICATE_PEM) in demo_config.h."
        #endif
        #ifndef democonfigCLIENT_PRIVATE_KEY_PEM
            #error "Please define client private key(democonfigCLIENT_PRIVATE_KEY_PEM) in demo_config.h."
        #endif
    #else

/* If a username is defined, a client password also would need to be defined for
 * client authentication. */
        #ifndef democonfigCLIENT_PASSWORD
            #error "Please define client password(democonfigCLIENT_PASSWORD) in demo_config.h for client authentication based on username/password."
        #endif

/* AWS IoT MQTT broker port needs to be 443 for client authentication based on
 * username/password. */
        #if defined( democonfigUSE_AWS_IOT_CORE_BROKER ) && democonfigMQTT_BROKER_PORT != 443
            #error "Broker port(democonfigMQTT_BROKER_PORT) should be defined as 443 in demo_config.h for client authentication based on username/password in AWS IoT Core."
        #endif
    #endif /* ifndef democonfigCLIENT_USERNAME */

    #ifndef democonfigMQTT_BROKER_PORT
        #define democonfigMQTT_BROKER_PORT    ( 8883 )
    #endif
#else /* if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 ) */
    #ifndef democonfigMQTT_BROKER_PORT
        #define democonfigMQTT_BROKER_PORT    ( 1883 )
    #endif
#endif /* if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 ) */

/**
 * @brief ALPN (Application-Layer Protocol Negotiation) protocol name for AWS IoT MQTT.
 *
 * This will be used if democonfigMQTT_BROKER_PORT is configured as 443 for the AWS IoT MQTT broker.
 * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
 * in the link below.
 * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
 */
#define AWS_IOT_MQTT_ALPN           "\x0ex-amzn-mqtt-ca"

/**
 * @brief This is the ALPN (Application-Layer Protocol Negotiation) string
 * required by AWS IoT for password-based authentication using TCP port 443.
 */
#define AWS_IOT_CUSTOM_AUTH_ALPN    "\x04mqtt"

/**
 * Provide default values for undefined configuration settings.
 */
#ifndef democonfigOS_NAME
    #define democonfigOS_NAME    "FreeRTOS"
#endif

#ifndef democonfigOS_VERSION
    #define democonfigOS_VERSION    tskKERNEL_VERSION_NUMBER
#endif

#ifndef democonfigHARDWARE_PLATFORM_NAME
    #define democonfigHARDWARE_PLATFORM_NAME    "WinSim"
#endif

#ifndef democonfigMQTT_LIB
    #include "core_mqtt.h" /* Include coreMQTT header for MQTT_LIBRARY_VERSION macro. */
    #define democonfigMQTT_LIB    "core-mqtt@"MQTT_LIBRARY_VERSION
#endif

/**
 * @brief The MQTT metrics string expected by AWS IoT.
 */
#define AWS_IOT_METRICS_STRING                                 \
    "?SDK=" democonfigOS_NAME "&Version=" democonfigOS_VERSION \
    "&Platform=" democonfigHARDWARE_PLATFORM_NAME "&MQTTLib=" democonfigMQTT_LIB

/**
 * @brief The length of the MQTT metrics string expected by AWS IoT.
 */
#define AWS_IOT_METRICS_STRING_LENGTH    ( ( uint16_t ) ( sizeof( AWS_IOT_METRICS_STRING ) - 1 ) )

#ifdef democonfigCLIENT_USERNAME

/**
 * @brief Append the username with the metrics string if #democonfigCLIENT_USERNAME is defined.
 *
 * This is to support both metrics reporting and username/password based client
 * authentication by AWS IoT.
 */
    #define CLIENT_USERNAME_WITH_METRICS    democonfigCLIENT_USERNAME AWS_IOT_METRICS_STRING
#endif

/**
 * @brief Length of client identifier.
 */
#define democonfigCLIENT_IDENTIFIER_LENGTH    ( ( uint16_t ) ( sizeof( democonfigCLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief Length of MQTT server host name.
 */
#define democonfigBROKER_ENDPOINT_LENGTH      ( ( uint16_t ) ( sizeof( democonfigMQTT_BROKER_ENDPOINT ) - 1 ) )


#endif /* DEMO_CONFIG_H */
