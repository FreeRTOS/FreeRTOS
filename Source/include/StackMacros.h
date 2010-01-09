/*
    FreeRTOS V6.0.2 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
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

#ifndef STACK_MACROS_H
#define STACK_MACROS_H

/*
 * Call the stack overflow hook function if the stack of the task being swapped
 * out is currently overflowed, or looks like it might have overflowed in the
 * past.
 *
 * Setting configCHECK_FOR_STACK_OVERFLOW to 1 will cause the macro to check
 * the current stack state only - comparing the current top of stack value to
 * the stack limit.  Setting configCHECK_FOR_STACK_OVERFLOW to greater than 1
 * will also cause the last few stack bytes to be checked to ensure the value
 * to which the bytes were set when the task was created have not been 
 * overwritten.  Note this second test does not guarantee that an overflowed
 * stack will always be recognised.
 */

/*-----------------------------------------------------------*/

#if( configCHECK_FOR_STACK_OVERFLOW == 0 )

	/* FreeRTOSConfig.h is not set to check for stack overflows. */
	#define taskFIRST_CHECK_FOR_STACK_OVERFLOW()
	#define taskSECOND_CHECK_FOR_STACK_OVERFLOW()

#endif /* configCHECK_FOR_STACK_OVERFLOW == 0 */
/*-----------------------------------------------------------*/

#if( configCHECK_FOR_STACK_OVERFLOW == 1 )

	/* FreeRTOSConfig.h is only set to use the first method of
	overflow checking. */
	#define taskSECOND_CHECK_FOR_STACK_OVERFLOW()

#endif
/*-----------------------------------------------------------*/

#if( ( configCHECK_FOR_STACK_OVERFLOW > 0 ) && ( portSTACK_GROWTH < 0 ) )

	/* Only the current stack state is to be checked. */
	#define taskFIRST_CHECK_FOR_STACK_OVERFLOW()														\
	{																									\
	extern void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );			\
																										\
		/* Is the currently saved stack pointer within the stack limit? */								\
		if( pxCurrentTCB->pxTopOfStack <= pxCurrentTCB->pxStack )										\
		{																								\
			vApplicationStackOverflowHook( ( xTaskHandle ) pxCurrentTCB, pxCurrentTCB->pcTaskName );	\
		}																								\
	}

#endif /* configCHECK_FOR_STACK_OVERFLOW > 0 */
/*-----------------------------------------------------------*/

#if( ( configCHECK_FOR_STACK_OVERFLOW > 0 ) && ( portSTACK_GROWTH > 0 ) )

	/* Only the current stack state is to be checked. */
	#define taskFIRST_CHECK_FOR_STACK_OVERFLOW()														\
	{																									\
	extern void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );		\
																										\
		/* Is the currently saved stack pointer within the stack limit? */								\
		if( pxCurrentTCB->pxTopOfStack >= pxCurrentTCB->pxEndOfStack )									\
		{																								\
			vApplicationStackOverflowHook( ( xTaskHandle ) pxCurrentTCB, pxCurrentTCB->pcTaskName );	\
		}																								\
	}

#endif /* configCHECK_FOR_STACK_OVERFLOW == 1 */
/*-----------------------------------------------------------*/

#if( ( configCHECK_FOR_STACK_OVERFLOW > 1 ) && ( portSTACK_GROWTH < 0 ) )

	#define taskSECOND_CHECK_FOR_STACK_OVERFLOW()																									\
	{																																				\
	extern void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );													\
	static const unsigned char ucExpectedStackBytes[] = {	tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE };	\
																																					\
																																					\
		/* Has the extremity of the task stack ever been written over? */																			\
		if( memcmp( ( void * ) pxCurrentTCB->pxStack, ( void * ) ucExpectedStackBytes, sizeof( ucExpectedStackBytes ) ) != 0 )						\
		{																																			\
			vApplicationStackOverflowHook( ( xTaskHandle ) pxCurrentTCB, pxCurrentTCB->pcTaskName );												\
		}																																			\
	}

#endif /* #if( configCHECK_FOR_STACK_OVERFLOW > 1 ) */
/*-----------------------------------------------------------*/

#if( ( configCHECK_FOR_STACK_OVERFLOW > 1 ) && ( portSTACK_GROWTH > 0 ) )

	#define taskSECOND_CHECK_FOR_STACK_OVERFLOW()																									\
	{																																				\
	extern void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );													\
	char *pcEndOfStack = ( char * ) pxCurrentTCB->pxEndOfStack;																				\
	static const unsigned char ucExpectedStackBytes[] = {	tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE,		\
																tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE, tskSTACK_FILL_BYTE };	\
																																					\
																																					\
		pcEndOfStack -= sizeof( ucExpectedStackBytes );																								\
																																					\
		/* Has the extremity of the task stack ever been written over? */																			\
		if( memcmp( ( void * ) pcEndOfStack, ( void * ) ucExpectedStackBytes, sizeof( ucExpectedStackBytes ) ) != 0 )								\
		{																																			\
			vApplicationStackOverflowHook( ( xTaskHandle ) pxCurrentTCB, pxCurrentTCB->pcTaskName );												\
		}																																			\
	}

#endif /* #if( configCHECK_FOR_STACK_OVERFLOW > 1 ) */
/*-----------------------------------------------------------*/

#endif /* STACK_MACROS_H */

