/*
 * FreeRTOS+UDP V1.0.3 (C) 2014 Real Time Engineers ltd.
 * All rights reserved
 *
 * This file is part of the FreeRTOS+UDP distribution.  The FreeRTOS+UDP license
 * terms are different to the FreeRTOS license terms.
 *
 * FreeRTOS+UDP uses a dual license model that allows the software to be used 
 * under a standard GPL open source license, or a commercial license.  The 
 * standard GPL license (unlike the modified GPL license under which FreeRTOS 
 * itself is distributed) requires that all software statically linked with 
 * FreeRTOS+UDP is also distributed under the same GPL V2 license terms.  
 * Details of both license options follow:
 *
 * - Open source licensing -
 * FreeRTOS+UDP is a free download and may be used, modified, evaluated and
 * distributed without charge provided the user adheres to version two of the
 * GNU General Public License (GPL) and does not remove the copyright notice or
 * this text.  The GPL V2 text is available on the gnu.org web site, and on the
 * following URL: http://www.FreeRTOS.org/gpl-2.0.txt.
 *
 * - Commercial licensing -
 * Businesses and individuals that for commercial or other reasons cannot comply
 * with the terms of the GPL V2 license must obtain a commercial license before 
 * incorporating FreeRTOS+UDP into proprietary software for distribution in any 
 * form.  Commercial licenses can be purchased from http://shop.freertos.org/udp 
 * and do not require any source files to be changed.
 *
 * FreeRTOS+UDP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+UDP unless you agree that you use the software 'as is'.
 * FreeRTOS+UDP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/udp
 *
 */

#ifndef NETWORK_BUFFER_MANAGEMENT_H
#define NETWORK_BUFFER_MANAGEMENT_H

/* NOTE PUBLIC API FUNCTIONS. */
portBASE_TYPE xNetworkBuffersInitialise( void );
xNetworkBufferDescriptor_t *pxNetworkBufferGet( size_t xRequestedSizeBytes, portTickType xBlockTimeTicks );
xNetworkBufferDescriptor_t *pxNetworkBufferGetFromISR( size_t xRequestedSizeBytes );
void vNetworkBufferRelease( xNetworkBufferDescriptor_t * const pxNetworkBuffer );
portBASE_TYPE vNetworkBufferReleaseFromISR( xNetworkBufferDescriptor_t * const pxNetworkBuffer );
uint8_t *pucEthernetBufferGet( size_t *pxRequestedSizeBytes );
void vEthernetBufferRelease( uint8_t *pucEthernetBuffer );

#endif /* NETWORK_BUFFER_MANAGEMENT_H */
