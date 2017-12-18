/*
 * FreeRTOS+UDP V1.0.4
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef NETWORK_BUFFER_MANAGEMENT_H
#define NETWORK_BUFFER_MANAGEMENT_H

/* NOTE PUBLIC API FUNCTIONS. */
BaseType_t xNetworkBuffersInitialise( void );
xNetworkBufferDescriptor_t *pxNetworkBufferGet( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks );
xNetworkBufferDescriptor_t *pxNetworkBufferGetFromISR( size_t xRequestedSizeBytes );
void vNetworkBufferRelease( xNetworkBufferDescriptor_t * const pxNetworkBuffer );
BaseType_t vNetworkBufferReleaseFromISR( xNetworkBufferDescriptor_t * const pxNetworkBuffer );
uint8_t *pucEthernetBufferGet( size_t *pxRequestedSizeBytes );
void vEthernetBufferRelease( uint8_t *pucEthernetBuffer );

#endif /* NETWORK_BUFFER_MANAGEMENT_H */
