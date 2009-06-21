/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

/* 
Changes from V3.0.0
	+ ISRcode is pulled inline and portTICKisr() is therefore
	  deleted from this file.

	+ Prescaler logic for Timer1 added to allow for a wider
	  range of TickRates.

Changes from V3.0.1
*/

#include <FreeRTOS.h>
#include <task.h>

/* IO port constants. */
#define portBIT_SET		(1)
#define portBIT_CLEAR	(0)

/* 
 * Hardware setup for the tick.
 * We use a compare match on timer1. Depending on MPU-frequency
 * and requested tickrate, a prescaled value with a matching
 * prescaler are determined.
 */
#define	portTIMER_COMPARE_BASE			((APROCFREQ/4)/configTICK_RATE_HZ)

#if portTIMER_COMPARE_BASE   < 0x10000
	#define	portTIMER_COMPARE_VALUE		(portTIMER_COMPARE_BASE)
	#define portTIMER_COMPARE_PS1		(portBIT_CLEAR)
	#define portTIMER_COMPARE_PS0		(portBIT_CLEAR)
#elif portTIMER_COMPARE_BASE < 0x20000
	#define	portTIMER_COMPARE_VALUE		(portTIMER_COMPARE_BASE / 2)
	#define portTIMER_COMPARE_PS1		(portBIT_CLEAR)
	#define portTIMER_COMPARE_PS0		(portBIT_SET)
#elif portTIMER_COMPARE_BASE < 0x40000
	#define	portTIMER_COMPARE_VALUE		(portTIMER_COMPARE_BASE / 4)
	#define portTIMER_COMPARE_PS1		(portBIT_SET)
	#define portTIMER_COMPARE_PS0		(portBIT_CLEAR)
#elif portTIMER_COMPARE_BASE < 0x80000
	#define	portTIMER_COMPARE_VALUE		(portTIMER_COMPARE_BASE / 8)
	#define portTIMER_COMPARE_PS1		(portBIT_SET)
	#define portTIMER_COMPARE_PS0		(portBIT_SET)
#else
	#error "TickRate out of range"
#endif

/*-----------------------------------------------------------*/

/*
 * Setup a timer for a regular tick.
 */
void portSetupTick( void )
{
	/*
	 * Interrupts are disabled when this function is called.
	 */

	/*
	 * Setup CCP1
	 * Provide the tick interrupt using a compare match on timer1.
	 */

	/*
	 * Set the compare match value.
	 */
	CCPR1H = ( unsigned portCHAR ) ( ( portTIMER_COMPARE_VALUE >> 8 ) & 0xff );
	CCPR1L = ( unsigned portCHAR )   ( portTIMER_COMPARE_VALUE & 0xff );

	/*
	 * Set Compare Special Event Trigger Mode
	 */
	bCCP1M3 	= portBIT_SET;
	bCCP1M2 	= portBIT_CLEAR;
	bCCP1M1 	= portBIT_SET;
	bCCP1M0		= portBIT_SET;

	/*
	 * Enable CCP1 interrupt
	 */
	bCCP1IE 	= portBIT_SET;

	/*
	 * We are only going to use the global interrupt bit, so disable
	 * interruptpriorities and enable peripheral interrupts.
	 */
	bIPEN		= portBIT_CLEAR;
	bPEIE		= portBIT_SET;

	/*
	 * Set up timer1
	 * It will produce the system tick.
	 */

	/*
	 * Clear the time count
	 */
	TMR1H = ( unsigned portCHAR ) 0x00;
	TMR1L = ( unsigned portCHAR ) 0x00;

	/*
	 * Setup the timer
	 */
	bRD16		= portBIT_SET;				// 16-bit
	bT1CKPS1	= portTIMER_COMPARE_PS1;	// prescaler
	bT1CKPS0	= portTIMER_COMPARE_PS0;	// prescaler
	bT1OSCEN	= portBIT_SET;				// Oscillator enable
	bT1SYNC		= portBIT_SET;				// No external clock sync
	bTMR1CS		= portBIT_CLEAR;			// Internal clock
	
	bTMR1ON		= portBIT_SET;				// Start timer1
}
