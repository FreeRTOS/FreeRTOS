/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief FreeRTOS and lwIP example for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


/* Environment include files. */
#include <stdlib.h>
#include <string.h>
#include "pm.h"
#include "flashc.h"

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include "partest.h"
#include "serial.h"
#include "ethernet.h"
#include "netif/etharp.h"
#include "flash.h"

/* Priority definitions for most of the tasks in the demo application. */
#define mainLED_TASK_PRIORITY     ( tskIDLE_PRIORITY + 1 )
#define mainETH_TASK_PRIORITY     ( tskIDLE_PRIORITY + 1 )

/* Baud rate used by the serial port tasks. */
#define mainCOM_BAUD_RATE      ( ( unsigned long ) 57600 )
#define mainCOM_BUFFER_LEN     ( ( unsigned long ) 70 )

/* An address in the internal Flash used to count resets.  This is used to check that
the demo application is not unexpectedly resetting. */
#define mainRESET_COUNT_ADDRESS     ( ( void * ) 0xC0000000 )


//!
//! \fn     main
//! \brief  start the software here
//!         1) Initialize the microcontroller and the shared hardware resources
//!         of the board.
//!         2) Launch the IP modules.
//!         3) Start FreeRTOS.
//! \return 42, which should never occur.
//! \note
//!
int main( void )
{
volatile avr32_pm_t* pm = &AVR32_PM;

	/* 1) Initialize the microcontroller and the shared hardware resources of the board. */

	/* Switch to external oscillator 0 */
	pm_switch_to_osc0( pm, FOSC0, OSC0_STARTUP );

	/* Setup PLL0 on OSC0, mul+1=16 ,divisor by 1, lockcount=16, ie. 12Mhzx16/1 = 192MHz output.
	   Extra div by 2 => 96MHz */
	pm_pll_setup(pm,	/* volatile avr32_pm_t* pm */
				0,		/* unsigned int pll */
				15,		/* unsigned int mul */
				1,		/* unsigned int div, Sel Osc0/PLL0 or Osc1/Pll1 */
				0,		/* unsigned int osc */
				16);		/* unsigned int lockcount */

	pm_pll_set_option( pm, 0,   // pll0
	                       0,   // Choose the range 160-240MHz.
	                       1,   // div2
	                       0 ); // wbwdisable

	/* Enable PLL0 */
	pm_pll_enable(pm,0);

	/* Wait for PLL0 locked */
	pm_wait_for_pll0_locked(pm) ;

	/* Setup generic clock number 2 on PLL, with OSC0/PLL0, no divisor */
	pm_gc_setup(pm,
				0,
				1, /* Use Osc (=0) or PLL (=1) */
				0, /* Sel Osc0/PLL0 or Osc1/Pll1 */
				0,
				1);

	/* Enable Generic clock 0*/
	pm_gc_enable(pm, 0);

	/* switch to clock */
	pm_cksel( pm, 1, 1, 1, 0, 1, 0 );
	flashc_set_wait_state( 1 );
	pm_switch_to_clock( pm, AVR32_PM_MCCTRL_MCSEL_PLL0 );

	/* Setup the LED's for output. */
	vParTestInitialise();

	/* Start the flash tasks just to provide visual feedback that the demo is
	executing. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );

	/* 2) Start ethernet task. */
	vStartEthernetTask( mainETH_TASK_PRIORITY );

	/* 3) Start FreeRTOS. */
	vTaskStartScheduler();

	/* Will only reach here if there was insufficient memory to create the idle task. */

	return 0;
}
/*-----------------------------------------------------------*/
