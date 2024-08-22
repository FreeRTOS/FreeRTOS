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

/*
 * A simple demo for NTP using FreeRTOS+TCP
 */

#ifndef NTPDEMO_H

#define NTPDEMO_H

void vStartNTPTask( uint16_t usTaskStackSize,
                    UBaseType_t uxTaskPriority );

/*
 * xIPVersion = 4 or 6.
 * xAsynchronous = true for asynchronous DNS lookups.
 * xLogging = true to get more logging.
 */
void vNTPSetNTPType( BaseType_t aIPType,
                     BaseType_t xAsynchronous,
                     BaseType_t xLogging );

/* Delete the IP-addresses of the NTP server to force a DNS lookup. */
void vNTPClearCache( void );

extern BaseType_t xNTPHasTime;
extern uint32_t ulNTPTime;

#endif /* ifndef NTPDEMO_H */
