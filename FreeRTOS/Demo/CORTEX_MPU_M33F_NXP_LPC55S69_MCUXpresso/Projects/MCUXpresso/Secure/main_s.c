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

/* FreeRTOS includes. */
#include "secure_port_macros.h"

/* Device includes. */
#include "fsl_device_registers.h"
#include "fsl_debug_console.h"
#include "arm_cmse.h"
#include "board.h"
#include "tzm_config.h"
#include "pin_mux.h"
#include "clock_config.h"

#if ( __ARM_FEATURE_CMSE & 1 ) == 0
	#error "Need ARMv8-M security extensions"
#elif ( __ARM_FEATURE_CMSE & 2 ) == 0
	#error "Compile with --cmse"
#endif

/* Start address of non-secure application. */
#define mainNONSECURE_APP_START_ADDRESS		( 0x00010000UL )

/* typedef for non-secure Reset Handler. */
typedef void ( *NonSecureResetHandler_t ) ( void ) __attribute__( ( cmse_nonsecure_call ) );
/*-----------------------------------------------------------*/

/**
 * @brief Boots into the non-secure code.
 *
 * @param[in] ulNonSecureStartAddress Start address of the non-secure application.
 */
static void prvBootNonSecure( uint32_t ulNonSecureStartAddress );

/**
 * @brief Application-specific implementation of the SystemInitHook() weak
 * function.
 */
void SystemInitHook( void );
/*-----------------------------------------------------------*/

/* For instructions on how to build and run this demo, visit the following link:
 * https://www.freertos.org/RTOS-Cortex-M33-LPC55S69-MCUXpresso-GCC.html
 */

/* Secure main(). */
int main(void)
{
	PRINTF( "Booting Secure World.\r\n" );

	/* Attach main clock divide to FLEXCOMM0 (debug console). */
	CLOCK_AttachClk( BOARD_DEBUG_UART_CLK_ATTACH );

	/* Init board hardware. */
	BOARD_InitPins();
	BOARD_BootClockFROHF96M();
	BOARD_InitDebugConsole();

	/* Boot the non-secure code. */
	PRINTF( "Booting Non-Secure World.\r\n" );
	prvBootNonSecure( mainNONSECURE_APP_START_ADDRESS );

	/* Non-secure software does not return, this code is not executed. */
	for( ; ; )
	{
		/* Should not reach here. */
	}
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

void SystemInitHook( void )
{
	/* Set CP10 and CP11 full access from Non-Secure code. */
	SCB_NS->CPACR |= ( ( 3UL << 10 * 2 ) | ( 3UL << 11 * 2 ) );

	/* The TrustZone should be configured as early as possible after RESET.
	 * Therefore it is called from SystemInit() during startup. The
	 * SystemInitHook() weak function overloading is used for this purpose.
	 */
	BOARD_InitTrustZone();
}
/*-----------------------------------------------------------*/
