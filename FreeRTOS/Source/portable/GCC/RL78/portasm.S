/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#include "FreeRTOSConfig.h"
#include "ISR_Support.h"

	.global    _vPortYield
	.global    _vPortStartFirstTask
	.global    _vPortTickISR

	.extern    _vTaskSwitchContext
	.extern    _xTaskIncrementTick

	.text
	.align 2

/* FreeRTOS yield handler.  This is installed as the BRK software interrupt
handler. */
_vPortYield:
	/* Save the context of the current task. */
	portSAVE_CONTEXT
	/* Call the scheduler to select the next task. */
	call      !!_vTaskSwitchContext
	/* Restore the context of the next task to run. */
	portRESTORE_CONTEXT
	retb


/* Starts the scheduler by restoring the context of the task that will execute
first. */
	.align 2
_vPortStartFirstTask:
	/* Restore the context of whichever task will execute first. */
	portRESTORE_CONTEXT
	/* An interrupt stack frame is used so the task is started using RETI. */
	reti

/* FreeRTOS tick handler.  This is installed as the interval timer interrupt
handler. */
	.align 2
_vPortTickISR:

	/* Save the context of the currently executing task. */
	portSAVE_CONTEXT
	/* Call the RTOS tick function. */
	call      !!_xTaskIncrementTick
#if configUSE_PREEMPTION == 1
	/* Select the next task to run. */
	call      !!_vTaskSwitchContext
#endif
	/* Retore the context of whichever task will run next. */
	portRESTORE_CONTEXT
	reti

	.end

