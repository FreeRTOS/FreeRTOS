/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

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
	+ ISRcode pulled inline to reduce stack-usage.

	+ Added functionality to only call vTaskSwitchContext() once
	  when handling multiple interruptsources in a single interruptcall.

	+ Filename changed to a .c extension to allow stepping through code
	  using F7.

Changes from V3.0.1
*/

/*
 * ISR for the tick.
 * This increments the tick count and, if using the preemptive scheduler, 
 * performs a context switch.  This must be identical to the manual 
 * context switch in how it stores the context of a task. 
 */

#ifndef _FREERTOS_DRIVERS_TICK_ISRTICK_C
#define _FREERTOS_DRIVERS_TICK_ISRTICK_C

{
	/*
	 * Was the interrupt the SystemClock?
	 */
	if( bCCP1IF && bCCP1IE )
	{
		/*
		 * Reset the interrupt flag
		 */
		bCCP1IF = 0;
	
		/*
	 	 * Maintain the tick count.
	 	 */
		vTaskIncrementTick();
		
		#if configUSE_PREEMPTION == 1
		{
			/*
		 	 * Ask for a switch to the highest priority task
		 	 * that is ready to run.
		 	 */
			uxSwitchRequested = pdTRUE;
		}
		#endif
	}
}

#pragma wizcpp uselib     "$__PATHNAME__/Tick.c"

#endif	/* _FREERTOS_DRIVERS_TICK_ISRTICK_C */
