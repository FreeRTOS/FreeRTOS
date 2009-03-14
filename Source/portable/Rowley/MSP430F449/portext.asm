/*
	FreeRTOS.org V5.2.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it 
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
	more details.

	You should have received a copy of the GNU General Public License along 
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.

	A special exception to the GPL is included to allow you to distribute a 
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details.


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

#include "FreeRTOSConfig.h"
#include "portasm.h"


.CODE

/*
 * The RTOS tick ISR.
 *
 * If the cooperative scheduler is in use this simply increments the tick 
 * count.
 *
 * If the preemptive scheduler is in use a context switch can also occur.
 */
_vTickISR:
		portSAVE_CONTEXT
				
		call	#_vTaskIncrementTick

		#if configUSE_PREEMPTION == 1
			call	#_vTaskSwitchContext
		#endif
		
		portRESTORE_CONTEXT
/*-----------------------------------------------------------*/


/*
 * Manual context switch called by the portYIELD() macro.
 */                
_vPortYield::

		/* Mimic an interrupt by pushing the SR. */
		push	SR			

		/* Now the SR is stacked we can disable interrupts. */
		dint			
				
		/* Save the context of the current task. */
		portSAVE_CONTEXT			

		/* Switch to the highest priority task that is ready to run. */
		call	#_vTaskSwitchContext		

		/* Restore the context of the new task. */
		portRESTORE_CONTEXT
/*-----------------------------------------------------------*/


/*
 * Start off the scheduler by initialising the RTOS tick timer, then restoring
 * the context of the first task.
 */
_xPortStartScheduler::

		/* Setup the hardware to generate the tick.  Interrupts are disabled 
		when this function is called. */
		call	#_prvSetupTimerInterrupt

		/* Restore the context of the first task that is going to run. */
		portRESTORE_CONTEXT
/*-----------------------------------------------------------*/          
      		

		/* Place the tick ISR in the correct vector. */
		.VECTORS
		
		.KEEP
		
		ORG		TIMERA0_VECTOR
		DW		_vTickISR
		


		END
		
