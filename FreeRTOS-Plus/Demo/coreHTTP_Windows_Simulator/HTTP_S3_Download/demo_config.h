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

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the demo. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "HTTPDemo"
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
 * @brief HTTP server port number.
 *
 * For this demo, an X.509 certificate is used to verify the client.
 */
#ifndef democonfigHTTPS_PORT
    #define democonfigHTTPS_PORT    443
#endif

/**
 * @brief Server's root CA certificate for TLS authentication with S3.
 *
 * The Baltimore Cybertrust root CA certificate is often used for authentication
 * with S3. It can be found at:
 * https://baltimore-cybertrust-root.chain-demos.digicert.com/info/index.html.
 *
 * S3 has started migrating certificates to Amazon Trust Services. If
 * authentication errors persist, re-attempt the connection with an Amazon root
 * CA certificate: https://www.amazontrust.com/repository.
 *
 * @note This certificate should be PEM-encoded.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"\
 * "...base64 data...\n"\
 * "-----END CERTIFICATE-----\n"
 *
 * #define democonfigS3_ROOT_CA_PEM   "...insert here..." 
 */

/**
 * @brief Server's root CA certificate for TLS authentication with IoT
 * credential provider.
 *
 * The CA can be found at https://www.amazontrust.com/repository.
 *
 * @note This certificate should be PEM-encoded.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"\
 * "...base64 data...\n"\
 * "-----END CERTIFICATE-----\n"
 * #define democonfigIOT_CRED_PROVIDER_ROOT_CA_PEM   "...insert here..." 
 */


/**
 * @brief Client certificate.
 *
 * @note This certificate should be PEM-encoded.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----
" * "...base64 data...
" * "-----END CERTIFICATE-----
"
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
 * @brief Endpoint for the AWS IoT credential provider.
 *
 * @note Can be found with
 * `aws iot describe-endpoint --endpoint-type iot:CredentialProvider` from
 * the AWS CLI.
 *
 * #define democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT    "...insert here..."
 */

/**
 * @brief Role alias name for accessing the credential provider.
 * 
 * @note This is the name of the role alias created in AWS IoT
 * while setting up AWS resources before running the demo.
 * Refer to the demo setup instructions in the README.md file
 * within the same directory as this file in the repository.

 * #define democonfigIOT_CREDENTIAL_PROVIDER_ROLE   "...insert here..."
 */


/**
 * @brief Define AWS IoT thing name.
 *
 * #define democonfigIOT_THING_NAME   "...insert here..."
 */


/**
 * @brief Name of bucket in AWS S3 from where file needs to be downloaded.
 *
 * #define democonfigS3_BUCKET_NAME   "...insert here..."
 */


/**
 * @brief AWS Region where the bucket resides.
 * #define democonfigS3_BUCKET_REGION   "...insert here..."
 */

/**
 * @brief Name of file that needs to be downloaded from AWS S3.
 * #define democonfigS3_OBJECT_NAME   "...insert here..."
 */

/**
 * @brief An option to disable Server Name Indication.
 *
 * @note When using a local server setup, SNI needs to be disabled for a server
 * that only has an IP address but no hostname. However, SNI should be enabled
 * whenever possible.
 */
#define democonfigDISABLE_SNI                       ( pdFALSE )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )

/**
 * @brief The length in bytes of the user buffer.
 */
#define democonfigUSER_BUFFER_LENGTH                ( 4096 )

/**
 * @brief The size of the range of the file to download, with each request.
 *
 * @note This should account for the response headers that will also be stored
 * in the user buffer. We don't expect S3 to send more than 1024 bytes of
 * headers.
 */
#define democonfigRANGE_REQUEST_LENGTH              ( 2048 )

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE                    configMINIMAL_STACK_SIZE

#endif /* ifndef DEMO_CONFIG_H */
