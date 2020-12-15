/*
 * FreeRTOS V202012.00
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

#ifndef LED_IO_H
#define LED_IO_H

	#define EnvisionRX72N

/* Board support settings. */

	#ifdef EnvisionRX72N

		/* R5F572NDHDFB 144pin LQFP */

		/* General Values */
		#define LED_ON					(0)
		#define LED_OFF 				(1)
		#define SW_PUSH 				(0)
		#define SW_RELEASE				(1)

		/* Switches (and its notation in the User's Manual) */
		#define SW1/*(SW2)*/				(PORT0.PIDR.BIT.B7)
		#define U_GPIO_PIN_SW1/*(SW2)*/ 	(GPIO_PORT_0_PIN_7)

		/* LED port settings (and its notation in the User's Manual) */
		#define LED0/*(LED2)*/				(PORT4.PODR.BIT.B0)
		#define U_GPIO_PIN_LED0/*(LED2)*/	(GPIO_PORT_4_PIN_0)

		/* FreeRTOS CLI Command Console */
		#define U_SCI_UART_CLI_PINSET()	R_SCI_PinSet_SCI2()
		#define U_SCI_UART_CLI_SCI_CH	(SCI_CH2)
		#define U_DTC_UART_CLI_TX_ACT	((dtc_activation_source_t)VECT(SCI2,TXI2))
		#define U_DTC_UART_CLI_TX_DR	(SCI2.TDR)

	#endif /* EnvisionRX72N */

	#ifndef LED0
		#error The hardware platform is not defined
	#endif

/* Board Support Data Structures. */

#include "r_sci_rx_if.h"
#include "r_dtc_rx_if.h"

extern sci_hdl_t xSerialSciHandle;
extern dtc_transfer_data_t xSerialTxDtcInfo;

/* Board Support Callback Functions. */

extern void vSerialSciCallback( void *pvArgs );

#endif /* LED_IO_H */

