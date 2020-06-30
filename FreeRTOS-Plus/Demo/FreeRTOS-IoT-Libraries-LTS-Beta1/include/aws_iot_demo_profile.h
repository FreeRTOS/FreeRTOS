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
 * IMPORTANT, CONFIGURATION REQUIRED: This is a configuration file containing AWS
 * IoT profile for the demos, will need additional setup:
 * https://www.freertos.org/mqtt/preconfiguredexamplesMA.html
 *
 * Each profile corresponds to a different service. The demos that use the same
 * profile share the same service. It is important to understand the
 * correspondence between the preconfigured profiles and demos, since each
 * service have different connection configuration and credential validation.
 *
 *  - mqtt_demo_profile.h is preconfigured to test.mosquitto.org MQTT broker.
 * The file is used with mqtt_plain_text demo and mqtt_basic_tls_server_auth
 * demo. Feel free to try out other broker with the demos.
 *
 *  - https_demo_profile.h is preconfigured to httpbin.org server. The file is
 * used with http_plain_text demo and https_basic_tls_server_auth demo.
 *
 *  - aws_iot_demo_profile.h (current) contains information to connect to AWS
 * IoT. The file is used with mqtt_tls_mutual_auth demo, https_tls_mutual_auth
 * demo, and other AWS IoT related demo.
 */

#ifndef AWS_IOT_DEMO_PROFILE_H
#define AWS_IOT_DEMO_PROFILE_H

/**
 * @brief Details of the MQTT broker to connect to.
 *
 * This is the Thing's Rest API Endpoint for AWS IoT.
 *
 * #define awsiotdemoprofileAWS_ENDPOINT	   "...insert here..."
 */

/**
 * @brief The port to use for the MQTT demo.
 *
 * Use 8883 if connecting to AWS IoT services.
 */
#define awsiotdemoprofileAWS_MQTT_PORT	   8883

/**
 * @brief The port to use for the HTTPS demo.
 *
 * Use 8443 if connecting to AWS IoT services.
 */
#define awsiotdemoprofileAWS_HTTPS_PORT	   8443

/**
 * @brief The AWS IoT server certificate.
 *
 * This certificate is used to identify the AWS IoT server and is publicly
 * available.
 */
#define awsiotdemoprofileAWS_CERTIFICATE_PEM                             \
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
 * @brief The MQTT client identifier.
 *
 * This is the "Thing Name" in AWS IoT.
 *
 * #define awsiotdemoprofileCLIENT_IDENTIFIER    "...insert here..."
 */

/**
 * @brief PEM-encoded client certificate
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"\
 * "...base64 data...\n"\
 * "-----END CERTIFICATE-----\n"
 *
 * #define awsiotdemoprofileCLIENT_CERTIFICATE_PEM    "...insert here..."
 */

/**
 * @brief PEM-encoded client private key.
 *
 * Must include the PEM header and footer:
 * "-----BEGIN RSA PRIVATE KEY-----\n"\
 * "...base64 data...\n"\
 * "-----END RSA PRIVATE KEY-----\n"
 *
 * #define awsiotdemoprofileCLIENT_PRIVATE_KEY_PEM    "...insert here..."
 */

#endif /* AWS_IOT_DEMO_PROFILE_H */
