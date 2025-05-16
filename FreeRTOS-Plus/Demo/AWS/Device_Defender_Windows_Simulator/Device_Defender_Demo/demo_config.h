/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
    #define LIBRARY_LOG_NAME    "DefenderDemo"
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
 * @brief The Thing resource registered on your AWS IoT account to use in the demo.
 * A Thing resource is required to communicate with the AWS IoT Device Shadow service.
 *
 * @note The Things associated with your AWS account can be found in the
 * AWS IoT console under Manage/Things, or using the ListThings REST API (that can
 * be called with the AWS CLI command line tool).
 *
 * #define democonfigTHING_NAME    "...insert here..."
 */

#define democonfigTHING_NAME				"MQTTV5-Thing"

#ifndef democonfigCLIENT_IDENTIFIER

/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.
 *
 * @note Appending __TIME__ to the client id string will reduce the possibility of a
 * client id collision in the broker. Note that the appended time is the compilation
 * time. This client id can cause collision, if more than one instance of the same
 * binary is used at the same time to connect to the broker.
 */
    #define democonfigCLIENT_IDENTIFIER    "testClient"__TIME__
#endif

/**
 * @brief The AWS IoT broker endpoint to connect to in the demo.
 *
 * @note Your AWS IoT Core endpoint can be found in the AWS IoT console under
 * Settings/Custom Endpoint, or using the DescribeEndpoint REST API (that can
 * be called with AWS CLI command line tool).
 *
 * #define democonfigMQTT_BROKER_ENDPOINT    "...insert here..."
 */
#define democonfigMQTT_BROKER_ENDPOINT    "arfk9u1wy8ods-ats.iot.ap-south-1.amazonaws.com"

/**
 * @brief The port to use for the demo.
 *
 * In general, port 8883 is for secured MQTT connections.
 *
 * @note Port 443 requires use of the ALPN TLS extension with the ALPN protocol
 * name. Using ALPN with this demo would require additional changes, including
 * setting the `pAlpnProtos` member of the `NetworkCredentials_t` struct before
 * forming the TLS connection. When using port 8883, ALPN is not required.
 *
 * #define democonfigMQTT_BROKER_PORT    ( insert here. )
 */

#define democonfigMQTT_BROKER_PORT    ( 8883 )

/**
 * @brief AWS root CA certificate.
 *
 * This certificate is used to identify the AWS IoT server and is publicly available.
 * Refer to the link below.
 * https://www.amazontrust.com/repository/AmazonRootCA1.pem
 *
 * @note This certificate should be PEM-encoded.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"\
 * "...base64 data...\n"\
 * "-----END CERTIFICATE-----\n"
 *
 * #define democonfigROOT_CA_PEM    "...insert here..."
 */

#define democonfigROOT_CA_PEM                                             \
    "-----BEGIN CERTIFICATE-----\n"                                      \
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
    "rqXRfboQnoZsG4q5WTP468SQvvG5\n"                                     \
    "-----END CERTIFICATE-----\n"

/**
 * @brief Client certificate.
 *
 * Please refer to the AWS documentation below for details
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

#define democonfigCLIENT_CERTIFICATE_PEM                                  \
    "-----BEGIN CERTIFICATE-----\n" \
    "MIIDWTCCAkGgAwIBAgIURBhRmf6dARjpTUHv+2gY0/qYDUIwDQYJKoZIhvcNAQEL\n" \
    "BQAwTTFLMEkGA1UECwxCQW1hem9uIFdlYiBTZXJ2aWNlcyBPPUFtYXpvbi5jb20g\n" \
    "SW5jLiBMPVNlYXR0bGUgU1Q9V2FzaGluZ3RvbiBDPVVTMB4XDTI1MDQwODA3MDcy\n" \
    "MloXDTQ5MTIzMTIzNTk1OVowHjEcMBoGA1UEAwwTQVdTIElvVCBDZXJ0aWZpY2F0\n" \
    "ZTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAPiEG2pM5zP743aVrS7w\n" \
    "1RkU/A4ANkTIq0E52RALNL86LXDxVWWTYAO5jjTP+0UoQdxdVhP4KahGmlRxVa/u\n" \
    "F7WGz7UtLQSeOYKqwylTR1HL1CQ20oD7y5Y3AjGJLaXqUHrxVyWd0DZJLjohvnEc\n" \
    "pU2FmWJQFS82yAU+86/k05LMgvdLz5n21skw48T6FDhPXlyPTIn09asszhu2Rd9Y\n" \
    "JaqdiNRL25OxeNqmZ7yX5W4NhtRpXCQErvSXLKrtF3Znj/zIlNG7AJnq/IIteFoC\n" \
    "nVKvq9ntIL+KW097U8kVvo+T382IFPPWSwJvKFLe2c/90SjWyz9ZuWvOpBWXgH7m\n" \
    "DMUCAwEAAaNgMF4wHwYDVR0jBBgwFoAUjQddXuF4MNAB8/d7wARB8d2fJNUwHQYD\n" \
    "VR0OBBYEFOMUeyX1HJaEqYtIA1zREq+VqswpMAwGA1UdEwEB/wQCMAAwDgYDVR0P\n" \
    "AQH/BAQDAgeAMA0GCSqGSIb3DQEBCwUAA4IBAQBIgrk3Vxi+/DSv2EVbArzVj1e3\n" \
    "YhBJ66GyjH7JZNiCcJ/PLoH1jyrghjwhdHqHqQLT4uM1d3t6I1H/iUTMnD3AbmHl\n" \
    "zyxrmb1MRVQ09uRfo/4HZLuwj7YaErOArUq3y4QtR5JJtvH8710Wy4pc4Rpw2NPI\n" \
    "dez/ZI5gg1i0lZOFTVNtJNBBZkJmXo0cyj9Ur4q6e3qE6tSEs5lstbqzpCgQxLTz\n" \
    "EqdYwtFqFhFTxcXSHSgTrUFSKTd6sSYw4Z7ZmOoVYNi4QZWyZK6TAEJEpRAohsE3\n" \
    "mHWPa7GWJb/ElBdroZxhf1xuCli6r6dC0h/vcmX9WBKzpjIVg3AZKlYokR6g\n" \
    "-----END CERTIFICATE-----\n"

/**
 * @brief Client's private key.
 *
 * Please refer to the AWS documentation below for details
 * regarding client authentication.
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

#define democonfigCLIENT_PRIVATE_KEY_PEM                                  \
    "-----BEGIN RSA PRIVATE KEY-----\n" \
    "MIIEpAIBAAKCAQEA+IQbakznM/vjdpWtLvDVGRT8DgA2RMirQTnZEAs0vzotcPFV\n" \
    "ZZNgA7mONM/7RShB3F1WE/gpqEaaVHFVr+4XtYbPtS0tBJ45gqrDKVNHUcvUJDbS\n" \
    "gPvLljcCMYktpepQevFXJZ3QNkkuOiG+cRylTYWZYlAVLzbIBT7zr+TTksyC90vP\n" \
    "mfbWyTDjxPoUOE9eXI9MifT1qyzOG7ZF31glqp2I1Evbk7F42qZnvJflbg2G1Glc\n" \
    "JASu9Jcsqu0XdmeP/MiU0bsAmer8gi14WgKdUq+r2e0gv4pbT3tTyRW+j5PfzYgU\n" \
    "89ZLAm8oUt7Zz/3RKNbLP1m5a86kFZeAfuYMxQIDAQABAoIBACU7zcu4Z+9+7s6G\n" \
    "kGL3DEZswXLrjzXxBs+H9kCUHTwFYGeKkOveD8WfGHJLMu9in7N/fHUTelJO+bJr\n" \
    "JJZuSrkU0Kvpb9RATIeKRCE96/KSYl9mo1VV5GPGLBr13ZP9Lj+tRwxIv7hScI2f\n" \
    "HqRd0VpzCM8VBoeDYqZ+jw4sb5KPq/42lP42Yp+kp2SdNwodM6dBMddxIWVli1cK\n" \
    "U/YpnM4otu1I7HDsfhCST5qS0nppjWUNRY5zwYipqWM8v8/D6/Mf+aYDIacVLJ8g\n" \
    "M7gjCCOkYg4YTEoDfVqxyhgaiU2jsBT6UtaDkEGUzvUhzXtir935hh1E5ndLnAzX\n" \
    "hVMC7CECgYEA/ibPcpeq+/Tw4g2vlqel6RZkYBASFQeWSl/W6QyDm3YI5kY+RX68\n" \
    "8E9PtfUreTDhf6e/VqxuvoWOl4Sb+Qdie2OKJB/7R8c2sGn2EQh2AvTU64wmcUXn\n" \
    "logzrqbtxoReB+Xx9VE3jKt7UcEN5xKTWeQI6wkjvasYOYSXqtPj2f0CgYEA+lLN\n" \
    "4oChgVl/DDCdHxJqXsMbsfrxYLDBfOnzQWIUksNPis2sIvp3x5Wgk+CmZ8ZIh5bC\n" \
    "aKbfOkjVRZSzpLDHtvJ2wuzpa2+itNf617SnrzuOa6l2N7FUxywYneoPHJ464ezK\n" \
    "TFpP7yR5wWaYYdp7TT/rJvnuqFf60edVqLTHdGkCgYEAkSctV+9Tkm9EnHbgkBTT\n" \
    "5xoI3eyPxz78ESJHpfalu8ZgMtRvgFVwJ3fEuNF7sM3AHJ574068OUgiNltgkYws\n" \
    "LPiezx8M7uPSUlNSXEwOyoV2jckPs6YPLKRBkEB6kOTMp4om9MscBNVzqy+tdwne\n" \
    "6noYtdQUe6EaRs95p/E4sykCgYEAifKf6zafyjybuwf/TmRDoj07QfXcl0BRIJl8\n" \
    "qId4dviTGRcGya/l2mMmvteKXJ300mPOdwWe9uu0PEgaR6P0K2mq8PjGGaLHs4li\n" \
    "fwTbc8IKVmJo94AODETMvBmEgmzgXiizwyfx7QPY5S+4whQ45vVWjYAmeTcizhIC\n" \
    "LpqRYCECgYA33SEpJsZjgVsr9EQRzCivjeadVy9xfAU8o11CDWSDO3HCvgvPVm73\n" \
    "J2lMXpaQScI56axGvh1uZqwSRmAONIWQ4azDL4ytRFgoL9FPEz58QcWxKzy98s1i\n" \
    "Imo3yZB4YrvdMD9TH1XrGDhy9d0Q1nwVJo5arT6OGehXfMobUh9hEQ==\n" \
    "-----END RSA PRIVATE KEY-----\n"

/**
 * @brief The username value for authenticating client to the MQTT broker when
 * username/password based client authentication is used.
 *
 * Please refer to the AWS IoT documentation below for
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
 * Please refer to the AWS IoT documentation below for
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
#define democonfigMQTT_LIB                               "core-mqtt@"MQTT_LIBRARY_VERSION

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE                         configMINIMAL_STACK_SIZE

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define democonfigNETWORK_BUFFER_SIZE                    ( 1024U )

/**
 * @brief Size of the open TCP ports array.
 *
 * A maximum of these many open TCP ports will be sent in the device defender
 * report.
 */
#define democonfigOPEN_TCP_PORTS_ARRAY_SIZE              10

/**
 * @brief Size of the open UDP ports array.
 *
 * A maximum of these many open UDP ports will be sent in the device defender
 * report.
 */
#define democonfigOPEN_UDP_PORTS_ARRAY_SIZE              10

/**
 * @brief Size of the established connections array.
 *
 * A maximum of these many established connections will be sent in the device
 * defender report.
 */
#define democonfigESTABLISHED_CONNECTIONS_ARRAY_SIZE     10

/**
 * @brief Size of the task numbers array.
 *
 * This must be at least the number of tasks used.
 */
#define democonfigCUSTOM_METRICS_TASKS_ARRAY_SIZE        10

/**
 * @brief Size of the buffer which contains the generated device defender report.
 *
 * If the generated report is larger than this, it is rejected.
 */
#define democonfigDEVICE_METRICS_REPORT_BUFFER_SIZE      1000

/**
 * @brief Major version number of the device defender report.
 */
#define democonfigDEVICE_METRICS_REPORT_MAJOR_VERSION    1

/**
 * @brief Minor version number of the device defender report.
 */
#define democonfigDEVICE_METRICS_REPORT_MINOR_VERSION    0

#endif /* DEMO_CONFIG_H */
