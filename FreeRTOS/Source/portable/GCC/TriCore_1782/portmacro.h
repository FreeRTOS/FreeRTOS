/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
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

/* CSA Manipulation. */
#define portCSA_TO_ADDRESS( pCSA )			( ( unsigned long * )( ( ( ( pCSA ) & 0x000F0000 ) << 12 ) | ( ( ( pCSA ) & 0x0000FFFF ) << 6 ) ) )
#define portADDRESS_TO_CSA( pAddress )		( ( unsigned long )( ( ( ( (unsigned long)( pAddress ) ) & 0xF0000000 ) >> 12 ) | ( ( ( unsigned long )( pAddress ) & 0x003FFFC0 ) >> 6 ) ) )
/*---------------------------------------------------------------------------*/

#define portYIELD()								_syscall( 0 )
/* Port Restore is implicit in the platform when the function is returned from the original PSW is automatically replaced. */
#define portSYSCALL_TASK_YIELD					0
#define portSYSCALL_RAISE_PRIORITY				1
/*---------------------------------------------------------------------------*/

/* Critical section management. */

/* Set ICR.CCPN to configMAX_SYSCALL_INTERRUPT_PRIORITY. */
#define portDISABLE_INTERRUPTS()	{																									\
										unsigned long ulICR;																			\
										_disable();																						\
										ulICR = _mfcr( $ICR ); 		/* Get current ICR value. */										\
										ulICR &= ~portCCPN_MASK;	/* Clear down mask bits. */											\
										ulICR |= configMAX_SYSCALL_INTERRUPT_PRIORITY; /* Set mask bits to required priority mask. */	\
										_mtcr( $ICR, ulICR );		/* Write back updated ICR. */										\
										_isync();																						\
										_enable();																						\
									}

/* Clear ICR.CCPN to allow all interrupt priorities. */
#define portENABLE_INTERRUPTS()		{																	\
										unsigned long ulICR;											\
										_disable();														\
										ulICR = _mfcr( $ICR );		/* Get current ICR value. */		\
										ulICR &= ~portCCPN_MASK;	/* Clear down mask bits. */			\
										_mtcr( $ICR, ulICR );		/* Write back updated ICR. */		\
										_isync();														\
										_enable();														\
									}

/* Set ICR.CCPN to uxSavedMaskValue. */
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedMaskValue ) 	{																						\
																	unsigned long ulICR;																\
																	_disable();																			\
																	ulICR = _mfcr( $ICR );		/* Get current ICR value. */							\
																	ulICR &= ~portCCPN_MASK;	/* Clear down mask bits. */								\
																	ulICR |= uxSavedMaskValue;	/* Set mask bits to previously saved mask value. */		\
																	_mtcr( $ICR, ulICR );		/* Write back updated ICR. */							\
																	_isync();																			\
																	_enable();																			\
																}


/* Set ICR.CCPN to configMAX_SYSCALL_INTERRUPT_PRIORITY */
extern unsigned long uxPortSetInterruptMaskFromISR( void );
#define portSET_INTERRUPT_MASK_FROM_ISR() 	uxPortSetInterruptMaskFromISR()

/* Pend a priority 1 interrupt, which will take care of the context switch. */
#define portYIELD_FROM_ISR( xHigherPriorityTaskWoken ) 		if( xHigherPriorityTaskWoken != pdFALSE ) {	CPU_SRC0.bits.SETR = 1; _isync(); }

/*---------------------------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*---------------------------------------------------------------------------*/

/*
 * Port specific clean up macro required to free the CSAs that were consumed by
 * a task that has since been deleted.
 */
void vPortReclaimCSA( unsigned long *pxTCB );
#define portCLEAN_UP_TCB( pxTCB )		vPortReclaimCSA( ( unsigned long * ) ( pxTCB ) )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */
