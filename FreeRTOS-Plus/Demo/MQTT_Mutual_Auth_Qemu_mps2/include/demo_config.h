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
    #define LIBRARY_LOG_NAME    "MQTTDemo"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_DEBUG
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
 * must be unique; so edit as required to ensure that no two clients connecting to
 * the same broker use the same client identifier.
 *
 *!!! Please note a #defined constant is used for convenience of demonstration
 *!!! only.  Production devices can use something unique to the device that can
 *!!! be read by software, such as a production serial number, instead of a
 *!!! hard coded constant.
 */
#define democonfigCLIENT_IDENTIFIER				"qemu-test-thing-1"

  
 

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
 * @note If you would like to setup an MQTT broker for running this demo,
 * please see `mqtt_broker_setup.txt`.
 */ 
#define democonfigMQTT_BROKER_ENDPOINT "a3rfn6tgdpv9oo-ats.iot.us-east-1.amazonaws.com"


 


/**
 * @brief The port to use for the demo.
 *
 * In general, port 8883 is for secured MQTT connections.
 *
 * @note Port 443 requires use of the ALPN TLS extension with the ALPN protocol
 * name. Using ALPN with this demo would require additional changes, including
 * setting the `pAlpnProtos` member of the `NetworkCredentials_t` struct before
 * forming the TLS connection. When using port 8883, ALPN is not required.
 */ 
#define democonfigMQTT_BROKER_PORT ( 8883 )

 

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
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"\
 * "...base64 data...\n"\
 * "-----END CERTIFICATE-----\n"
 */
#define democonfigROOT_CA_PEM \
"-----BEGIN CERTIFICATE-----\n" \
"MIIDQTCCAimgAwIBAgITBmyfz5m/jAo54vB4ikPmljZbyjANBgkqhkiG9w0BAQsF\n" \
"ADA5MQswCQYDVQQGEwJVUzEPMA0GA1UEChMGQW1hem9uMRkwFwYDVQQDExBBbWF6\n" \
"b24gUm9vdCBDQSAxMB4XDTE1MDUyNjAwMDAwMFoXDTM4MDExNzAwMDAwMFowOTEL\n" \
"MAkGA1UEBhMCVVMxDzANBgNVBAoTBkFtYXpvbjEZMBcGA1UEAxMQQW1hem9uIFJv\n" \
"b3QgQ0EgMTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBALJ4gHHKeNXj\n" \
"ca9HgFB0fW7Y14h29Jlo91ghYPl0hAEvrAIthtOgQ3pOsqTQNroBvo3bSMgHFzZM\n" \
"9O6II8c+6zf1tRn4SWiw3te5djgdYZ6k/oI2peVKVuRF4fn9tBb6dNqcmzU5L/qw\n" \
"IFAGbHrQgLKm+a/sRxmPUDgH3KKHOVj4utWp+UhnMJbulHheb4mjUcAwhmahRWa6\n" \
"VOujw5H5SNz/0egwLX0tdHA114gk957EWW67c4cX8jJGKLhD+rcdqsq08p8kDi1L\n" \
"93FcXmn/6pUCyziKrlA4b9v7LWIbxcceVOF34GfID5yHI9Y/QCB/IIDEgEw+OyQm\n" \
"jgSubJrIqg0CAwEAAaNCMEAwDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8BAf8EBAMC\n" \
"AYYwHQYDVR0OBBYEFIQYzIU07LwMlJQuCFmcx7IQTgoIMA0GCSqGSIb3DQEBCwUA\n" \
"A4IBAQCY8jdaQZChGsV2USggNiMOruYou6r4lK5IpDB/G/wkjUu0yKGX9rbxenDI\n" \
"U5PMCCjjmCXPI6T53iHTfIUJrU6adTrCC2qJeHZERxhlbI1Bjjt/msv0tadQ1wUs\n" \
"N+gDS63pYaACbvXy8MWy7Vu33PqUXHeeE6V/Uq2V8viTO96LXFvKWlJbYK8U90vv\n" \
"o/ufQJVtMVT8QtPHRh8jrdkPSHCa2XV4cdFyQzR1bldZwgJcJmApzyMZFo6IQ6XU\n" \
"5MsI+yMRQ+hDKXJioaldXgjUkK642M4UwtBV8ob2xJNDd2ZhwLnoQdeXeGADbkpy\n" \
"rqXRfboQnoZsG4q5WTP468SQvvG5\n" \
"-----END CERTIFICATE-----" 

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
 */
#define democonfigCLIENT_CERTIFICATE_PEM \
"-----BEGIN CERTIFICATE-----\n" \
"MIIDWjCCAkKgAwIBAgIVAP5iJdCE2apiDOCxJHxBTlTI+xBgMA0GCSqGSIb3DQEB\n" \
"CwUAME0xSzBJBgNVBAsMQkFtYXpvbiBXZWIgU2VydmljZXMgTz1BbWF6b24uY29t\n" \
"IEluYy4gTD1TZWF0dGxlIFNUPVdhc2hpbmd0b24gQz1VUzAeFw0yMjEyMjkwMDQ0\n" \
"MTRaFw00OTEyMzEyMzU5NTlaMB4xHDAaBgNVBAMME0FXUyBJb1QgQ2VydGlmaWNh\n" \
"dGUwggEiMA0GCSqGSIb3DQEBAQUAA4IBDwAwggEKAoIBAQDhVD6LvyKJjEn+muov\n" \
"KMftsMVIA6rPFf1xg2zlLSfMUr0JgLyXAZ5vn3y8ssAMoUAvLJ9fz5LiveaSBOJr\n" \
"SYs0qOi876flUEJ+czQq00Fo1JDbzZ827zghQvvVhVIJ1L9k3g73h2AodhZBvzs5\n" \
"ZMKGFAFJl64pCBD35Ksb0qvG45n9K4DZqQw0W+4TAizX82oCSjtx/AMpRV1FPc2U\n" \
"taQt8TBlsB4Rp0nEYGgcny7jQSCwLj4SDxvOv+CcYS7uAK3Z/LqC6u9QVnKZTIqA\n" \
"oOLXEW5Lvww9uHWCtYroFGQ5R5W2UULKN4W8aREno6zgfJuOse5za1EqU6dL7JwS\n" \
"ShWdAgMBAAGjYDBeMB8GA1UdIwQYMBaAFLiqkXT4E73LxVdiC8yWLI41VBBnMB0G\n" \
"A1UdDgQWBBS/4Dd7GOSeOwMYVgV5tr2y7NZjRDAMBgNVHRMBAf8EAjAAMA4GA1Ud\n" \
"DwEB/wQEAwIHgDANBgkqhkiG9w0BAQsFAAOCAQEABh4KOr4E+OYI3jXTMYTk7eKV\n" \
"UPk4NZkd6/MpIvw/QV+P/i/t4s51VIAz2569EFF+M8C61vKcJkklHY/gV39WC/1r\n" \
"JAiV7vQEARyXiCMH7NhjFcZIJmR0fC9TllgjwbWYRdnNHo6cz1OCcdePVq9DZR3J\n" \
"P3x1PBB0ec/QpaQlV/dH6cCMEmBnSNBoaPyn2pNkSiDZRm0Q3+HS+42nkmlpY36o\n" \
"biCJPzrdR/TYNTvBhxFrnBE6eUA7llsYBgCy7T7Qxl5py2Nlbylzf0FrsJuXEHxE\n" \
"ZQvj5GMfHZPWSqREVPIq4r65jxIDW5q6bdJZmLFmKesdy2AtjQPfDqYX/hizAQ==\n" \
"-----END CERTIFICATE-----"
 
 /**
 * @brief Client Private Key.
 * 
 * !!! Please note pasting a key into the header file in this manner is for
 * !!! convenience of demonstration only and should not be done in production.
 * !!! Never paste a production private key here!.  Production devices should
 * !!! store keys securely, such as within a secure element.  Additionally,
 * !!! we provide the corePKCS library that further enhances security by
 * !!! enabling securely stored keys to be used without exposing them to
 * !!! software.
 * 
 * For AWS IoT MQTT broker, refer to the AWS documentation below for details
 * regarding client authentication.
 * https://docs.aws.amazon.com/iot/latest/developerguide/client-authentication.html
 *
 * @note This private key should be PEM-encoded.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN RSA PRIVATE KEY-----\n"\
 * "...base64 data...\n"\
 * "-----END RSA PRIVATE KEY-----\n"
 */
#define democonfigCLIENT_PRIVATE_KEY_PEM \
"-----BEGIN RSA PRIVATE KEY-----\n" \
"MIIEowIBAAKCAQEA4VQ+i78iiYxJ/prqLyjH7bDFSAOqzxX9cYNs5S0nzFK9CYC8\n" \
"lwGeb598vLLADKFALyyfX8+S4r3mkgTia0mLNKjovO+n5VBCfnM0KtNBaNSQ282f\n" \
"Nu84IUL71YVSCdS/ZN4O94dgKHYWQb87OWTChhQBSZeuKQgQ9+SrG9KrxuOZ/SuA\n" \
"2akMNFvuEwIs1/NqAko7cfwDKUVdRT3NlLWkLfEwZbAeEadJxGBoHJ8u40EgsC4+\n" \
"Eg8bzr/gnGEu7gCt2fy6gurvUFZymUyKgKDi1xFuS78MPbh1grWK6BRkOUeVtlFC\n" \
"yjeFvGkRJ6Os4HybjrHuc2tRKlOnS+ycEkoVnQIDAQABAoIBAHBMYheXnIjcqAwB\n" \
"/PCf7HQjg07OtRQcK4GlNGJLTOhh2+Cejl7b6bBL1gjdNSWWP7zDCnLfqp7iccUY\n" \
"NheuQXhvLf7rmcuJYnpOxBML0i+CsOc65TyloF3DWmsh1K8dnn2QxfjLOTsxDwqZ\n" \
"WdTSyLe1xKZ+t8evQ3WoOzbUmdO2r5kBiQvhbponybpq0F20wywWv952eu+dolX7\n" \
"B0uXz/a7F4GSCJAunc0m2tU/gRuVEOFzlSq4IzbX36ewTk30JBP9f6RwEpDBi5bC\n" \
"dgVyu/H6jXEXcMw4Wp9ixi9PhohjaNEcxhLErsEz0W8mng4FMeLPlLucGJduBZ0y\n" \
"uliUHWkCgYEA9MsIq80nDTUDTKxzzE80t4qxvlfQvaqqCRTH1A6yRG7VaglEjJIq\n" \
"R9pMynO2cwPr5GVJej9RSObe4vqmaBGhrFUifros+ipVDIoMdByatDE5vN8ltO6U\n" \
"P0VuMm+n1wtEkUz7Av4XpmFo20WZl8VhuxZKM10woWZ2PsbEJJYquXcCgYEA66UX\n" \
"w8dfybQJfBc/nb5k3lI1r11eOOP6IsxUUxr0gFD+eZ+MFCdBlLwgQCdEs1IT6UUb\n" \
"C4mGlUrkz8ymZf+jUgdDE1dgpd6yH7hkDp3EfXWu0Ls8ss+YSK0RIG3YXsfCdIkl\n" \
"aPslTM3eMG+XM48MZKndwb1bbnq/ocYhlrNcLosCgYEAqHymtzk5S8nVP4zjFxjd\n" \
"PAdmV5CxyBoTdrSq5bZH1PpEQfunBuoD1/jVKfOC/J8SWd2tOUsjc34Uoz3KE48v\n" \
"LCJc38Tc+ELyzvKlp7WYdbX7+5fLqEEeIH51XpmjeEv1Id1OV7z0Ijyho2rAUMo2\n" \
"fkLVR404z55qfMLqdhQ1y/kCgYAivLKVJMXlGQow5ch1+4QpFdteH5htMIZGLPLd\n" \
"UWLrq4Tn7vIaYnMTduwWKPPCr33J7GsBN2PEjEbQry10acvsoq9roXzY1sxRSsBN\n" \
"O0qk5/0+PevDvECJriGRM0ArMK1kunbuU996w/pWD40th4/fIv9SuRRKZAPt2CRJ\n" \
"b+VN4wKBgHDgpOGMdgDUh98rkOND2e6ZGtb3wQSzpNOIUCXBgZucF8kSXi/1ZClY\n" \
"MezZNJ+sl+GEWdDWIIrgsaD7Q/b1Pz4cvHsIoX2Kn8ENhd61NxF2bsqKwxSYuTnE\n" \
"0I8Yda8ZHpQsS/bxiHGdINqz/Xj33xOv/H7YiHq956nLByOCLRUo\n" \
"-----END RSA PRIVATE KEY-----"

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
 */
// #define democonfigUSE_AWS_IOT_CORE_BROKER    ( 1 )


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
#define democonfigHARDWARE_PLATFORM_NAME    "QEMUMPS2" 

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
