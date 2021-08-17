/*
 * FreeRTOS V202107.00
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

/* FreeRTOS config include. */
#include "FreeRTOSConfig.h"

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
    #define LIBRARY_LOG_NAME    "MQTT-wolfSSL"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

/* Prototype for the function used to print to console on Windows simulator
 * of FreeRTOS.
 * The function prints to the console before the network is connected;
 * then a UDP port after the network has connected. */
extern void vLoggingPrintf(const char* pcFormatString,
    ...);

/* Map the SdkLog macro to the logging function to enable logging
 * on Windows simulator. */
#ifndef SdkLog
#define SdkLog( message )    vLoggingPrintf message
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique; so edit as required to ensure that no two clients connecting to
 * the same broker use the same client identifier.
 *
 * #define democonfigCLIENT_IDENTIFIER    "insert here."
 */

/**
 * @brief Endpoint of the MQTT broker to connect to.
 *
 * This demo application can be run with any MQTT broker, that supports mutual
 * authentication.
 *
 * For AWS IoT MQTT broker, this is the Thing's REST API Endpoint.
 *
 * @note Your AWS IoT Core endpoint can be found in the AWS IoT console under
 * Settings/Custom Endpoint, or using the describe-endpoint REST API (with
 * AWS CLI command line tool).
 *
 * #define democonfigMQTT_BROKER_ENDPOINT    "...insert here..."
 */

/**
 * @brief The port to use for the demo.
 *
 * In general, port 8883 is for secured MQTT connections.
 *
 * @note Port 443 requires use of the ALPN TLS extension with the ALPN protocol
 * name. When using port 8883, ALPN is not required.
 *
 * #define democonfigMQTT_BROKER_PORT    "...insert here..."
 */

/**
 * @brief Credentials source.
 *
 * Users can choose either a file or a buffer to pass to the TLS component
 * as a source of credentials such as certificates and private keys. By default,
 * following macros expect to have file paths:
 * - democonfigROOT_CA_PEM
 * - democonfigCLIENT_CERTIFICATE_PEM
 * - democonfigCLIENT_PRIVATE_KEY_PEM
 * If users want to pass those credentials not via files but buffers,
 * enable democonfigCREDENTIALS_IN_BUFFER macro below and set buffer
 * containing the credential data to each of the above three macros.
 *
 * @note This macro affects for all said three macros, do not mix file path
 * and buffer to those macros.
 *
 * #define democonfigCREDENTIALS_IN_BUFFER
 */

 /**
 * @brief Server's root CA certificate.
 *
 * For AWS IoT MQTT broker, this certificate is used to identify the AWS IoT
 * server and is publicly available. Refer to the AWS documentation available
 * in the link below.
 * https://docs.aws.amazon.com/iot/latest/developerguide/server-authentication.html#server-authentication-certs
 *
 *
 * @note This certificate should be PEM-encoded.
 * @note If democonfigCREDENTIALS_IN_BUFFER is defined, define the certificate data.
 * Otherwise, define the path to the certificate.
 * @warning If wolfSSL cannot verify the peer when connecting to AWS IoT, try
 * using the root CA of Starfield Services found at
 * https://www.amazontrust.com/repository/SFSRootCAG2.pem.
 * wolfSSL requires that the whole CA certificate chain is trusted. AWS
 * certificates are cross signed by this CA.
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
 * @note If democonfigCREDENTIALS_IN_BUFFER is defined, define the certificate data.
 * Otherwise, define the path to the certificate.
 *
 * #define democonfigCLIENT_CERTIFICATE_PEM    "...insert here..."
 */

/**
 * @brief Client's private key.
 *
 * For AWS IoT MQTT broker, refer to the AWS documentation below for details
 * regarding clientauthentication.
 * https://docs.aws.amazon.com/iot/latest/developerguide/client-authentication.html
 *
 * @note This private key should be PEM-encoded.
 * @note If democonfigCREDENTIALS_IN_BUFFER is defined, define the key data.
 * Otherwise, define the path to the key file.
 *
 * #define democonfigCLIENT_PRIVATE_KEY_PEM    "...insert here..."
 */

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE         configMINIMAL_STACK_SIZE

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define democonfigNETWORK_BUFFER_SIZE    ( 1024U )

#endif /* DEMO_CONFIG_H */
