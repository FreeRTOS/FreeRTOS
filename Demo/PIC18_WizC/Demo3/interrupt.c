/*
	FreeRTOS V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
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
	+ Added functionality to only call vTaskSwitchContext() once
	  when handling multiple interruptsources in a single interruptcall.

	+ Included Filenames changed to a .c extension to allow stepping through
	  code using F7.

Changes from V3.0.1
*/

#include <pic.h>

/* Scheduler include files. */
#include <FreeRTOS.h>
#include <task.h>
#include <queue.h>

static bit uxSwitchRequested;

/*
 * Vector for the ISR.
 */
void pointed Interrupt()
{
	/*
	 * Save the context of the current task.
	 */
	portSAVE_CONTEXT( portINTERRUPTS_FORCED );

	/*
	 * No contextswitch requested yet
	 */
	uxSwitchRequested	= pdFALSE;
	
	/*
	 * Was the interrupt the FreeRTOS SystemTick?
	 */
	#include <libFreeRTOS/Drivers/Tick/isrTick.c>

/*******************************************************************************
** DO NOT MODIFY ANYTHING ABOVE THIS LINE
********************************************************************************
** Enter the includes for the ISR-code of the FreeRTOS drivers below.
**
** You cannot use local variables. Alternatives are:
** - Use static variables	(Global RAM usage increases)
** - Call a function		(Additional cycles are needed)
** - Use unused SFR's		(preferred, no additional overhead)
** See "../Serial/isrSerialTx.c" for an example of this last option
*******************************************************************************/



	/*
	 * Was the interrupt a byte being received?
	 */
	#include "../Serial/isrSerialRx.c"


	/*
	 * Was the interrupt the Tx register becoming empty?
	 */
	#include "../Serial/isrSerialTx.c"



/*******************************************************************************
** DO NOT MODIFY ANYTHING BELOW THIS LINE
*******************************************************************************/
	/*
	 * Was a contextswitch requested by one of the
	 * interrupthandlers?
	 */
	 if ( uxSwitchRequested )
	 {
	 	vTaskSwitchContext();
	 }
	 
	/*
	 * Restore the context of the (possibly other) task.
	 */
	portRESTORE_CONTEXT();

	#pragma asmline retfie	0
}
