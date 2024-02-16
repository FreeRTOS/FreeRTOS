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

#ifndef DEMO_LOGGING_H
#define DEMO_LOGGING_H

#include "FreeRTOS.h"

/*
 * Initialize a logging system that can be used from FreeRTOS tasks and Win32
 * threads.  Do not call printf() directly while the scheduler is running.
 *
 * Set xLogToStdout, xLogToFile and xLogToUDP to either pdTRUE or pdFALSE to
 * lot to stdout, a disk file and a UDP port respectively.
 *
 * If xLogToUDP is pdTRUE then ulRemoteIPAddress and usRemotePort must be set
 * to the IP address and port number to which UDP log messages will be sent.
 */
void vLoggingInit( BaseType_t xLogToStdout,
                   BaseType_t xLogToFile,
                   BaseType_t xLogToUDP,
                   uint32_t ulRemoteIPAddress,
                   uint16_t usRemotePort );

void vPlatformInitLogging( void );

void vLoggingPrintf( const char * pcFormat,
                     ... );

#endif /* DEMO_LOGGING_H */
