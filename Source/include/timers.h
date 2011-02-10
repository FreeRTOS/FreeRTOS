/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/


#ifndef TIMERS_H
#define TIMERS_H

#ifndef INC_FREERTOS_H
	#error "include FreeRTOS.h must appear in source files before include timers.h"
#endif

#include "portable.h"
#include "list.h"

#ifdef __cplusplus
extern "C" {
#endif

/* IDs for commands that can be sent/received on the timer queue. */
#define trmCOMMAND_PROCESS_TIMER_OVERFLOW	0 /* For use by the kernel only! */
#define tmrCOMMAND_START					1
#define tmrCOMMAND_STOP						2
#define tmrCOMMAND_CHANGE_PERIOD			3
#define tmrCOMMAND_DELETE					4

/*-----------------------------------------------------------
 * MACROS AND DEFINITIONS
 *----------------------------------------------------------*/

typedef void * xTimerHandle;

/* Define the prototype to which timer callback functions must conform. */
typedef void (*tmrTIMER_CALLBACK)( xTimerHandle xTimer );

portBASE_TYPE xTimerCreateTimerTask( void ) PRIVILEGED_FUNCTION;
xTimerHandle xTimerCreate( const signed char *pcTimerName, portTickType xTimerPeriod, unsigned portBASE_TYPE uxAutoReload, void * pvTimerID, tmrTIMER_CALLBACK pxCallbackFunction ) PRIVILEGED_FUNCTION;
void *pvTimerGetTimerID( xTimerHandle xTimer ) PRIVILEGED_FUNCTION;
portBASE_TYPE xTimerGenericCommand( xTimerHandle xTimer, portBASE_TYPE xCommandID, portTickType xOptionalValue, portTickType xBlockTime ) PRIVILEGED_FUNCTION;
portBASE_TYPE xTimerIsTimerActive( xTimerHandle xTimer ) PRIVILEGED_FUNCTION;

#define xTimerStart( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_START, 0, xBlockTime )
#define xTimerStop( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_STOP, 0, xBlockTime )
#define xTimerChangePeriod( xTimer, xNewPeriod, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_CHANGE_PERIOD, xNewPeriod, xBlockTime )
#define xTimerDelete( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_DELETE, 0, xBlockTime )
#define xTimerReset( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_START, 0, xBlockTime )

#ifdef __cplusplus
}
#endif
#endif /* TIMERS_H */



