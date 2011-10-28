/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

#ifndef PORTMACRO_H
#define PORTMACRO_H

#ifdef __cplusplus
extern "C" {
#endif

/* System Includes. */
#include <tc1782.h>
#include <machine/intrinsics.h>

/*-----------------------------------------------------------
 * Port specific definitions.
 *
 * The settings in this file configure FreeRTOS correctly for the
 * given hardware and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

/* Type definitions. */
#define portCHAR		char
#define portFLOAT		float
#define portDOUBLE		double
#define portLONG		long
#define portSHORT		short
#define portSTACK_TYPE	unsigned long
#define portBASE_TYPE	long

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned portLONG portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*---------------------------------------------------------------------------*/

/* Architecture specifics. */
#define portSTACK_GROWTH							( -1 )
#define portTICK_RATE_MS							( ( portTickType ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT							4
#define portNOP()									__asm volatile( " nop " )
#define portCRITICAL_NESTING_IN_TCB					1
#define portRESTORE_FIRST_TASK_PRIORITY_LEVEL		1


/*---------------------------------------------------------------------------*/

typedef struct MPU_SETTINGS { unsigned long ulNotUsed; } xMPU_SETTINGS;

/* Define away the instruction from the Restore Context Macro. */
#define portPRIVILEGE_BIT							0x0UL

#define portCCPN_MASK						( 0x000000FFUL )

extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
#define portENTER_CRITICAL()			vTaskEnterCritical()
#define portEXIT_CRITICAL()				vTaskExitCritical()
/*---------------------------------------------------------------------------*/

/* Task utilities. */

extern void vPortReclaimCSA( unsigned portBASE_TYPE *pxTCB );

/* CSA Manipulation. */
#define portCSA_TO_ADDRESS( pCSA )			( ( unsigned portBASE_TYPE * )( ( ( ( pCSA ) & 0x000F0000 ) << 12 ) | ( ( ( pCSA ) & 0x0000FFFF ) << 6 ) ) )
#define portADDRESS_TO_CSA( pAddress )		( ( unsigned portBASE_TYPE )( ( ( ( (unsigned portBASE_TYPE)( pAddress ) ) & 0xF0000000 ) >> 12 ) | ( ( (unsigned portBASE_TYPE)( pAddress ) & 0x003FFFC0 ) >> 6 ) ) )
/*---------------------------------------------------------------------------*/

#define portYIELD()								_syscall(0)
/* Port Restore is implicit in the platform when the function is returned from the original PSW is automatically replaced. */
#define portSYSCALL_TASK_YIELD					0
#define portSYSCALL_RAISE_PRIORITY				1
/*---------------------------------------------------------------------------*/

/* Critical section management. */

/* Clear the ICR.IE bit. */
#define portDISABLE_INTERRUPTS()			_mtcr( $ICR, ( ( _mfcr( $ICR ) & ~portCCPN_MASK ) | configMAX_SYSCALL_INTERRUPT_PRIORITY ) )

/* Set the ICR.IE bit. */
#define portENABLE_INTERRUPTS()				{ unsigned long ulCurrentICR = _mfcr( $ICR ); _mtcr( $ICR, ( ulCurrentICR & ~portCCPN_MASK ) ) }

extern unsigned portBASE_TYPE uxPortSetInterruptMaskFromISR( void );
extern void vPortClearInterruptMaskFromISR( unsigned portBASE_TYPE uxSavedStatusValue );

/* Set ICR.CCPN to configMAX_SYSCALL_INTERRUPT_PRIORITY */
#define portSET_INTERRUPT_MASK_FROM_ISR() 	uxPortSetInterruptMaskFromISR()

/* Set ICR.CCPN to uxSavedInterruptStatus */
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedStatusValue ) vPortClearInterruptMaskFromISR( uxSavedStatusValue )

/* As this port holds a CSA address in pxTopOfStack, the assert that checks the
pxTopOfStack alignment is removed. */
#define portALIGNMENT_ASSERT_pxCurrentTCB ( void )

/*---------------------------------------------------------------------------*/

/*
 * Save the context of a task.
 * The upper context is automatically saved when entering a trap or interrupt.
 * Need to save the lower context as well and copy the PCXI CSA ID into
 * pxCurrentTCB->pxTopOfStack. Only Lower Context CSA IDs may be saved to the
 * TCB of a task.
 *
 * Call vTaskSwitchContext to select the next task, note that this changes the
 * value of pxCurrentTCB so that it needs to be reloaded.
 *
 * Call vPortSetMPURegisterSetOne to change the MPU mapping for the task
 * that has just been switched in.
 *
 * Load the context of the task.
 * Need to restore the lower context by loading the CSA from
 * pxCurrentTCB->pxTopOfStack into PCXI (effectively changing the call stack).
 * In the Interrupt handler post-amble, RSLCX will restore the lower context
 * of the task. RFE will restore the upper context of the task, jump to the
 * return address and restore the previous state of interrupts being
 * enabled/disabled.
 */
#define portYIELD_FROM_ISR( xHigherPriorityTaskWoken )			\
{																\
unsigned portBASE_TYPE *pxUpperCSA = NULL;						\
unsigned portBASE_TYPE xUpperCSA = 0UL;							\
extern volatile unsigned long *pxCurrentTCB;					\
	if ( pdTRUE == xHigherPriorityTaskWoken )					\
	{															\
		_disable();												\
		_isync();												\
		xUpperCSA = _mfcr( $PCXI );								\
		pxUpperCSA = portCSA_TO_ADDRESS( xUpperCSA );			\
		*pxCurrentTCB = pxUpperCSA[0];							\
		vTaskSwitchContext();									\
		pxUpperCSA[0] = *pxCurrentTCB;							\
		_dsync();												\
		_isync();												\
		_nop();													\
		_nop();													\
	}															\
}
/*---------------------------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*---------------------------------------------------------------------------*/

/*
 * Port specific clean up macro required to free the CSAs that were consumed by
 * a task that has since been deleted.
 */
void vPortReclaimCSA( unsigned portBASE_TYPE *pxTCB );
#define portCLEAN_UP_TCB( pxTCB )		vPortReclaimCSA( ( unsigned portBASE_TYPE *) ( pxTCB ) )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */
