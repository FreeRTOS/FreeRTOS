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

/**
 * @file cellular_config.h
 * @brief cellular config options.
 */

#ifndef __CELLULAR_CONFIG_H__
#define __CELLULAR_CONFIG_H__

/* This is a project specific file and is used to override config values defined
 * in cellular_config_defaults.h. */

/**
 * Cellular comm interface make use of COM port on computer to communicate with
 * cellular module on windows simulator, for example "COM5".
 * #define CELLULAR_COMM_INTERFACE_PORT    "...insert here..."
 */

/*
 * Default APN for network registration.
 * #define CELLULAR_APN                    "...insert here..."
 */

/*
 * PDN context id for cellular network.
 */
#define CELLULAR_PDN_CONTEXT_ID         ( CELLULAR_PDN_CONTEXT_ID_MIN )

/*
 * PDN connect timeout for network registration.
 */
#define CELLULAR_PDN_CONNECT_TIMEOUT    ( 100000UL )

/*
 * Overwrite default config for different cellular modules.
 */

/*
 * GetHostByName API is not used in the demo. IP address is used to store the hostname.
 * The value should be longer than the length of democonfigMQTT_BROKER_ENDPOINT in demo_config.h.
 */
#define CELLULAR_IP_ADDRESS_MAX_SIZE    ( 64U )

#endif /* __CELLULAR_CONFIG_H__ */
