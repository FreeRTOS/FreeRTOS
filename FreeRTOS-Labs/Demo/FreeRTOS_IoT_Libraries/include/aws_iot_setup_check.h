/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * This file performs the configuration check at preprocessor time to make sure
 * the credentials are defined. If credentials are not set, users will
 * immediately be guided to the getting started documentation for proper setup.
 *
 * This is meant to be included after the credential define.
 * e.g., a .c file that establishes a MQTT connection:
 * #include "aws_iot_demo_profile.h" // This file includes the credential for user to define
 * #include "aws_iot_setup_check.h"  // This file make sure credentials are defined
 */

#ifndef IOT_CONFIGCHECK_H
#define IOT_CONFIGCHECK_H

/*
 * TLS is enabled by default. This is config to zero for *_plain_text demo.
 */
#ifndef democonfigENABLE_TLS
    #define democonfigENABLE_TLS    1
#endif

/*
 * Mutual authentication is enabled by default. This is config to zero for
 * *_plain_text and *_basic_tls_server demo.
 */
#ifndef democonfigENABLE_MUTUAL_AUTH
    #define democonfigENABLE_MUTUAL_AUTH    1
#endif

/*
 * Credential setup check.
 */
#if defined( AWS_IOT_DEMO_PROFILE_H )
    #ifndef awsiotdemoprofileAWS_ENDPOINT
        #error ACTION REQUIRED: Please ensure you have awsiotdemoprofileAWS_ENDPOINT (in aws_iot_demo_profile.h) configured. Refer to https://www.freertos.org/mqtt/preconfiguredexamplesMA.html for proper setup.
    #endif
    #ifndef awsiotdemoprofileCLIENT_IDENTIFIER
        #error ACTION REQUIRED: Please ensure you have awsiotdemoprofileCLIENT_IDENTIFIER (in aws_iot_demo_profile.h) configured. Refer to https://www.freertos.org/mqtt/preconfiguredexamplesMA.html for proper setup.
    #endif
    #if ( democonfigENABLE_TLS )
        #if ( democonfigENABLE_MUTUAL_AUTH )
            #ifndef awsiotdemoprofileCLIENT_CERTIFICATE_PEM
                #error ACTION REQUIRED: Please ensure you have awsiotdemoprofileCLIENT_CERTIFICATE_PEM (in aws_iot_demo_profile.h) configured as required for mutual authentication. https://www.freertos.org/mqtt/preconfiguredexamplesMA.html for proper setup.
            #endif
            #ifndef awsiotdemoprofileCLIENT_PRIVATE_KEY_PEM
                #error ACTION REQUIRED: Please ensure you have awsiotdemoprofileCLIENT_PRIVATE_KEY_PEM (in aws_iot_demo_profile.h) configured as required for mutual authentication. https://www.freertos.org/mqtt/preconfiguredexamplesMA.html for proper setup.
            #endif
        #endif
    #endif /* if ( democonfigENABLE_TLS ) */
#endif /* if defined( AWS_IOT_DEMO_PROFILE_H ) */

#endif /* IOT_CONFIGCHECK_H */
