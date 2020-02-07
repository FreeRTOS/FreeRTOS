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

#ifndef DEMO_CONFIG_H
#define DEMO_CONFIG_H

/*
 * This configuration file determines how MQTT demo is run.
 *
 * mqtt_plain_text demo: Security is turned off. Preconfigured to a public MQTT
 * broker on unencrypted port so no authentication configuration required.
 *
 * mqtt_basic_tls_server_auth demo: TLS security is enabled, allowing broker side
 * authentication. Preconfigured to a public MQTT broker with certificate provided
 * by the broker so no authentication configuration required.
 *
 * mqtt_tls_mutual_auth demo: Mutual authentication is enabled. Preconfigured to
 * AWS IoT broker, will require certificate setup for successful connection.
 */

/**
 * @brief Enable/Disable TLS in demos.
 *
 * For more information regarding TLS protocol:
 * https://www.freertos.org/mqtt/tls.html
 */
#define democonfigENABLE_TLS			 1

/**
 * @brief Enable/Disable mutual authentication in demos. If enabled, require
 * democonfigENABLE_TLS to be set to 1.
 */
#define democonfigENABLE_MUTUAL_AUTH	 1

/**
 * @brief Select a connection profile.
 *
 * If set to 1, the demo will connect to AWS IoT with credential setup in
 * aws_iot_demo_profile.h file, otherwise the demo is preconfigured to connect to
 * test.mosquitto.org with credential setup in mqtt_demo_profile.h file. If
 * enabled, requires democonfigENABLE_MUTUAL_AUTH to be set to 1 since AWS IoT
 * requires mutually authenticated connection.
 */
#define democonfigPROFILE_USE_AWS_IOT	 1

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE	    configMINIMAL_STACK_SIZE

#endif /* DEMO_CONFIG_H */
