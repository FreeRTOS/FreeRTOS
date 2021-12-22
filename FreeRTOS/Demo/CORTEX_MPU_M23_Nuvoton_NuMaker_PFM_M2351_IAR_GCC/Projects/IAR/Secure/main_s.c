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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Standard includes. */
#include <arm_cmse.h>
#include <stdio.h>

/* Device includes. */
#include "NuMicro.h"
#include "partition_M2351.h"

/* FreeRTOS includes. */
#include "secure_port_macros.h"

/* Start address of non-secure application. */
#define mainNONSECURE_APP_START_ADDRESS		( 0x10040000 )

/* typedef for non-secure Reset Handler. */
typedef __cmse_nonsecure_call void ( *NonSecureResetHandler_t )( void );
/*-----------------------------------------------------------*/

/**
 * @brief Sets up the hardware - clocks and UARTs.
 */
static void prvSetupHardware( void );

/**
 * @brief Boots into the non-secure code.
 *
 * @param[in] ulNonSecureStartAddress Start address of the non-secure application.
 */
static void prvBootNonSecure( uint32_t ulNonSecureStartAddress );
/*-----------------------------------------------------------*/

/* For instructions on how to build and run this demo, visit the following link:
 * https://www.freertos.org/RTOS-Cortex-M23-NuMaker-PFM-M2351-Keil.html
 */

/* Secure main. */
int main(void)
{
	/* Unlock protected registers. */
	SYS_UnlockReg();

	/* Initialize the hardware. */
	prvSetupHardware();

	/* Print banner. */
	printf( "\n" );
	printf( "+---------------------------------------------+\n" );
	printf( "|            Secure is running ...            |\n" );
	printf( "+---------------------------------------------+\n" );

	/* Do not generate Systick interrupt on secure side. */
	SysTick_Config( 1 );

	/* Set GPIO Port A to non-secure for controlling LEDs from the non-secure
	 * side . */
	SCU_SET_IONSSET( SCU_IONSSET_PA_Msk );

	/* Set UART0 to non-secure for debug output from non-secure side. */
	SCU_SET_PNSSET( UART0_Attr );

	/* Lock protected registers before booting non-secure code. */
	SYS_LockReg();

	/* Boot the non-secure code. */
	printf( "Entering non-secure world ...\n" );
	prvBootNonSecure( mainNONSECURE_APP_START_ADDRESS );

	/* Non-secure software does not return, this code is not executed. */
	for( ; ; )
	{
		/* Should not reach here. */
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Init System Clock. */
	/* Enable PLL */
	CLK->PLLCTL = CLK_PLLCTL_64MHz_HIRC;
	/* Wait for PLL to be stable. */
	while( ( CLK->STATUS & CLK_STATUS_PLLSTB_Msk ) == 0 );

	/* Set HCLK divider to 1. */
	CLK->CLKDIV0 = ( CLK->CLKDIV0 & ( ~CLK_CLKDIV0_HCLKDIV_Msk ) );

	/* Switch HCLK clock source to PLL. */
	CLK->CLKSEL0 = ( CLK->CLKSEL0 & ( ~CLK_CLKSEL0_HCLKSEL_Msk ) ) | CLK_CLKSEL0_HCLKSEL_PLL;

	/* Initialize UART0 - It is used for debug output from the non-secure side. */
	/* Enable UART0 clock. */
	CLK->APBCLK0 |= CLK_APBCLK0_UART0CKEN_Msk;

	/* Select UART0 clock source. */
	CLK->CLKSEL1 = ( CLK->CLKSEL1 & ( ~CLK_CLKSEL1_UART0SEL_Msk ) ) | CLK_CLKSEL1_UART0SEL_HIRC;

	/* Set multi-function pins for UART0 RXD and TXD. */
	SYS->GPB_MFPH = ( SYS->GPB_MFPH & ( ~UART0_RXD_PB12_Msk ) ) | UART0_RXD_PB12;
	SYS->GPB_MFPH = ( SYS->GPB_MFPH & ( ~UART0_TXD_PB13_Msk ) ) | UART0_TXD_PB13;

	/* Initialize UART1 - It is used for debug output from the secure side. */
	/* Enable UART1 clock. */
	CLK->APBCLK0 |= CLK_APBCLK0_UART1CKEN_Msk;

	/* Select UART1 clock source. */
	CLK->CLKSEL1 = ( CLK->CLKSEL1 & ( ~CLK_CLKSEL1_UART1SEL_Msk ) ) | CLK_CLKSEL1_UART1SEL_HIRC;

	/* Set multi-function pins for UART1 RXD and TXD. */
	SYS->GPA_MFPL = ( SYS->GPA_MFPL & ( ~UART1_RXD_PA2_Msk ) ) | UART1_RXD_PA2;
	SYS->GPA_MFPL = ( SYS->GPA_MFPL & ( ~UART1_TXD_PA3_Msk ) ) | UART1_TXD_PA3;

	/* Update System Core Clock. */
	PllClock		= 64000000;				/* PLL. */
	SystemCoreClock	= 64000000 / 1;			/* HCLK. */
	CyclesPerUs		= 64000000 / 1000000;	/* For SYS_SysTickDelay(). */

	/* Initialize the debug port. */
	DEBUG_PORT->BAUD = UART_BAUD_MODE2 | UART_BAUD_MODE2_DIVIDER(__HIRC, 115200);
	DEBUG_PORT->LINE = UART_WORD_LEN_8 | UART_PARITY_NONE | UART_STOP_BIT_1;
}
/*-----------------------------------------------------------*/

static void prvBootNonSecure( uint32_t ulNonSecureStartAddress )
{
	NonSecureResetHandler_t pxNonSecureResetHandler;

	/* Setup the non-secure vector table. */
	SCB_NS->VTOR = ulNonSecureStartAddress;

	/* Main Stack Pointer value for the non-secure side is the first entry in
	 * the non-secure vector table. Read the first entry and assign the same to
	 * the non-secure main stack pointer(MSP_NS). */
	secureportSET_MSP_NS( *( ( uint32_t * )( ulNonSecureStartAddress ) ) );

	/* Reset Handler for the non-secure side is the second entry in the
	 * non-secure vector table. Read the second entry to get the non-secure
	 * Reset Handler. */
	pxNonSecureResetHandler = ( NonSecureResetHandler_t )( * ( ( uint32_t * ) ( ( ulNonSecureStartAddress ) + 4U ) ) );

	/* Start non-secure state software application by jumping to the non-secure
	 * Reset Handler. */
	pxNonSecureResetHandler();
}
/*-----------------------------------------------------------*/
