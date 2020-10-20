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
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif
#include "logging_stack.h"

/************ End of logging configuration ****************/

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
#define democonfigMQTT_BROKER_ENDPOINT    "a36385mjytouy4-ats.iot.us-west-2.amazonaws.com"

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
    * #define democonfigMQTT_BROKER_PORT    "...insert here..."
    */
#define democonfigMQTT_BROKER_PORT        ( 8883 )

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
     *
     * #define democonfigROOT_CA_PEM    "...insert here..."
     */
#define democonfigROOT_CA_PEM                                            \
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
      *
      * #define democonfigCLIENT_CERTIFICATE_PEM    "...insert here..."
      */
#define democonfigCLIENT_CERTIFICATE_PEM                                 \
    "-----BEGIN CERTIFICATE-----\n"                                      \
    "MIIDWjCCAkKgAwIBAgIVAI0Z2tK9liQaF0/dS4w5qz49BI6lMA0GCSqGSIb3DQEB\n" \
    "CwUAME0xSzBJBgNVBAsMQkFtYXpvbiBXZWIgU2VydmljZXMgTz1BbWF6b24uY29t\n" \
    "IEluYy4gTD1TZWF0dGxlIFNUPVdhc2hpbmd0b24gQz1VUzAeFw0yMDAzMTcxOTI4\n" \
    "MjFaFw00OTEyMzEyMzU5NTlaMB4xHDAaBgNVBAMME0FXUyBJb1QgQ2VydGlmaWNh\n" \
    "dGUwggEiMA0GCSqGSIb3DQEBAQUAA4IBDwAwggEKAoIBAQCoQ7uCdhzfJ/0Ow+L/\n" \
    "7vJkIYnmtS5TgPIqJQzX4soOQk54ajAoqXr/KrdEJNzxQbRmDMV4TgYueACKEqQR\n" \
    "Qek+GZlFqnmAhxR1RoIsw2ghfS/oP1nsfCAn7ouujJkNO09XrfJHrjV03jI1nzdP\n" \
    "156jS3j7qi469LIHgklVuDRAHbnw+IN5IGYNDyVeFuBcoiCNapytnYJrNA3f8tuc\n" \
    "MoyYSY3t1e3xw405lFe1/zXD9R4M0p+dbUUE192ovbDSoZdHCLGbVI1+irZmcNQU\n" \
    "qQuqtD2UOHDn30Ik8UAl7nCQipMX+GODtIEsialr+ZYec6aokjwQ3I1iRbuieRhJ\n" \
    "Q6+fAgMBAAGjYDBeMB8GA1UdIwQYMBaAFAQuHdeqHsdLyC5hWDJxXPiDRHiJMB0G\n" \
    "A1UdDgQWBBR9mrDvamHQaZoQhZc+i0g0SZBOlDAMBgNVHRMBAf8EAjAAMA4GA1Ud\n" \
    "DwEB/wQEAwIHgDANBgkqhkiG9w0BAQsFAAOCAQEAmArGZvMpmf4thgyZWJ4jl/2/\n" \
    "0tbvX+hdMO/OFvYUhFp+OdAWfVT/La+C4rLC7kV2ZWpcTr2DdJRVIUT/IYfWwGuR\n" \
    "9Ef8FkcXXJSDTKFxTJ/d2vqQpasxEAClEUwQFjARgD17mFpBAGq4fLluWzTgou0B\n" \
    "z945KnoEiUc4rrRjVlxhEVb4XXvr89lsAa+viGjKRGx/B81I220fTuzVAUBWKe24\n" \
    "pQWaaYfE4drmbwz3Rm387EGHIqEIjcMUDejdLww5mY+3ALV5QDBva07f/SzJFM8p\n" \
    "dhkezgrO4IpZ0i9w41GHo2ZlebVIVUUfrWsAWNwSMGB3Atb1byYNzucPQQJmwg==\n" \
    "-----END CERTIFICATE-----"

      /**
       * @brief Client's private key.
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
#define democonfigCLIENT_PRIVATE_KEY_PEM                                 \
    "-----BEGIN RSA PRIVATE KEY-----\n"                                  \
    "MIIEowIBAAKCAQEAqEO7gnYc3yf9DsPi/+7yZCGJ5rUuU4DyKiUM1+LKDkJOeGow\n" \
    "KKl6/yq3RCTc8UG0ZgzFeE4GLngAihKkEUHpPhmZRap5gIcUdUaCLMNoIX0v6D9Z\n" \
    "7HwgJ+6LroyZDTtPV63yR641dN4yNZ83T9eeo0t4+6ouOvSyB4JJVbg0QB258PiD\n" \
    "eSBmDQ8lXhbgXKIgjWqcrZ2CazQN3/LbnDKMmEmN7dXt8cONOZRXtf81w/UeDNKf\n" \
    "nW1FBNfdqL2w0qGXRwixm1SNfoq2ZnDUFKkLqrQ9lDhw599CJPFAJe5wkIqTF/hj\n" \
    "g7SBLImpa/mWHnOmqJI8ENyNYkW7onkYSUOvnwIDAQABAoIBAG9wTGNe7kgtJ7/7\n" \
    "o/90tTvzqm0NWZ0cLUYUO6lPHhrLd0Twrux/MmKEW9PZxipSJbPgiXff1OA5wcGw\n" \
    "DtEPIfZq5cPp34Zr7/SrudMDp5dmXbAnJNsmafWIWyJDI6pLuYSMQ4WNrwGzlvVE\n" \
    "eVF7sCjd90ZVs0CAhtfKRd9rm89Jzcugskg1cPzgb2eJjKByAhELU80f9hsJpFdp\n" \
    "SGD7zx3llGuZ0hWscHiieiMU81NJIYkUjbMTSmy/wqyw4N1g3dqOVozlPknHfXjV\n" \
    "MdeX6D5lP0u5/645pD9K/kFZJjiICKJ25b7nYGeUQqRgfE1VmL6SoajhuodwgwoL\n" \
    "RnmbpoECgYEA0UpmlSumtoqy7gQ4W5VElCZJ8/MUba/v1ALP5cXjRQwyebJSskrS\n" \
    "uqhOTXaHeGCruDJqbF2VdoiX4rhJe16xxf6CulXKQ9Vhq1lO8i1CWa39tu+T0V9X\n" \
    "9oJXmaqx3ByPLfC/oa+qXD1ktNUZtbpIeou3zPt7CX/ajdOOMk+tcS8CgYEAzdFa\n" \
    "DZSnqO/X+tA55AJUo6uhohi3ohQv9sLYXNnxGTOvitj6XToYNYHZtiHXWF0+kGyY\n" \
    "nmhkbnDdlIW/pdVQyVAAPP3MF2o6q8ig0Rn/DiYPvfYZgL557XkI+SWTl0Ao9/QN\n" \
    "gt+X3gWZrVAyeBpEMQTXCQavwC3xeaqAQhL1rJECgYEA0D/i4Q1lPn+2WSWz2lUl\n" \
    "vvB2Z5n5Osd0sRX3Pd/xK5ReaT9qD+Rp2Ld96pBFbh9q3sazpI5eGWsDDuJmo65u\n" \
    "399Gvxh8QZECNViROGKWgduh+DRddlkTksLRXaM+hRGZ2pGSbNT5g/zGxzS/91ab\n" \
    "pex+gCW/oI0qsDLQa/liUJsCgYBbVN1bTW4g/12eRSyLS6V3g8AUCFfkqoSmQcx1\n" \
    "V5kvj8oEGUjweckoZVjRA69l3OrYd/g5wyVeBOOu9rMWydQxoTiZ2B3q/g7PEBac\n" \
    "86ZFBwrRRxYGFYBRqvYaaVxXL/d+IGSmgMYJlf6d9AqRVUaRYg5ySO9QnpKbZNfJ\n" \
    "elReoQKBgG6VNx56cq2cGU6shPM0eQopDu1SVeKdO+C7DYqtTJaKWaeuVMUp90TY\n" \
    "dCT6ZPdZmgPSt++/lyX7/3e0Yk2yxC6xQFjflAAMIyDSDfAR9ajnHrVZXxEfquoO\n" \
    "Aqrm49+Sfr4wts9Cmo3PqA8oqYIRBzc76Zh4c8kc7P1XlYQIGiuN\n"             \
    "-----END RSA PRIVATE KEY-----"


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
#define democonfigMQTT_LIB                  "core-mqtt@1.0.0"

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE            configMINIMAL_STACK_SIZE

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define democonfigNETWORK_BUFFER_SIZE       ( 1024U )

#endif /* DEMO_CONFIG_H */
