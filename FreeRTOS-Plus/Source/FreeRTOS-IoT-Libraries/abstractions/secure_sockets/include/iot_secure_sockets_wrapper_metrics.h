/*
 * Amazon FreeRTOS Secure Sockets V1.1.5
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#ifndef _AWS_SECURE_SOCKETS_WRAPPER_METRICS_
#define _AWS_SECURE_SOCKETS_WRAPPER_METRICS_

/* This file redefines Secure Sockets functions to be called through a wrapper macro,
 * but only if metrics is enabled explicitly. */
#if AWS_IOT_SECURE_SOCKETS_METRICS_ENABLED == 1

/* This macro is included in aws_secure_socket.c and aws_secure_socket_wrapper_metrics.c.
 * It will prevent the redefine in those source files. */
    #ifndef _SECURE_SOCKETS_WRAPPER_NOT_REDEFINE
        #define SOCKETS_Init        Sockets_MetricsInit
        #define SOCKETS_Connect     Sockets_MetricsConnect
        #define SOCKETS_Shutdown    Sockets_MetricsShutdown
    #endif

#endif

#endif /* ifndef _AWS_SECURE_SOCKETS_WRAPPER_METRICS_ */
