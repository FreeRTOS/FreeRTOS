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

#ifndef LPC18xx_43xx_EMAC_H
#define LPC18xx_43xx_EMAC_H

/*
 * Initialise the MAC and PHY.
 */
BaseType_t xEMACInit( uint8_t ucMACAddress[ 6 ] );

/*
 * Return pdTRUE if there is a FreeRTOS Tx descriptor.  Return pdFALSE if all
 * Tx descriptors are already in use.
 */
BaseType_t xEMACIsTxDescriptorAvailable( void );

/*
 * Assign a buffer to a Tx descriptor so it is ready to be transmitted, but
 * don't start the transmission yet.
 */
void vEMACAssignBufferToDescriptor( uint8_t * pucBuffer );

/*
 * Start transmitting the buffer pointed to by the next Tx descriptor.  The
 * buffer must have first been allocated to the Tx descriptor using a call to
 * vEMACAssignBufferToDescriptor().
 */
void vEMACStartNextTransmission( uint32_t ulLength );

/*
 * The data pointed to by the Rx descriptor has been consumed, and the Rx
 * descriptor can be returned to the control of the DMS.
 */
void vEMACReturnRxDescriptor( void );

/*
 * Returns pdTRUE if the next Rx descriptor contains received data.  Returns
 * pdFLASE fi the next Rx descriptor is still under the control of the DMA.
 */
BaseType_t xEMACRxDataAvailable( void );
void vEMACSwapEmptyBufferForRxedData( xNetworkBufferDescriptor_t *pxNetworkBuffer );

#endif /* LPC18xx_43xx_EMAC_H */

