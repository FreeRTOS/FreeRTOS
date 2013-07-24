/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

#ifndef PORTMACRO_H
#define PORTMACRO_H

#ifdef __cplusplus
extern "C" {
#endif

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
#define portCHAR        char
#define portFLOAT       float
#define portDOUBLE      long
#define portLONG        long
#define portSHORT       int
#define portSTACK_TYPE  unsigned portSHORT
#define portBASE_TYPE	portSHORT

#if( configUSE_16_BIT_TICKS == 1 )
        typedef unsigned portSHORT portTickType;
        #define portMAX_DELAY ( portTickType ) 0xffff
#else
        typedef unsigned portLONG portTickType;
        #define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/

/* Critical section management. */
void portENTER_CRITICAL( void );
#pragma aux portENTER_CRITICAL = "pushf" \
                                 "cli";

void portEXIT_CRITICAL( void );
#pragma aux portEXIT_CRITICAL   = "popf";

void portDISABLE_INTERRUPTS( void );
#pragma aux portDISABLE_INTERRUPTS = "cli";

void portENABLE_INTERRUPTS( void );
#pragma aux portENABLE_INTERRUPTS = "sti";
/*-----------------------------------------------------------*/

/* Architecture specifics. */
#define portSTACK_GROWTH        ( -1 )
#define portSWITCH_INT_NUMBER   0x80
#define portYIELD()             __asm{ int portSWITCH_INT_NUMBER } 
#define portTICK_RATE_MS        ( ( portTickType ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT      2
#define portINITIAL_SW          ( ( portSTACK_TYPE ) 0x0202 )   /* Start the tasks with interrupts enabled. */
#define portNOP()				__asm{ nop }
/*-----------------------------------------------------------*/

/* Compiler specifics. */
#define portINPUT_BYTE( xAddr )                 inp( xAddr )
#define portOUTPUT_BYTE( xAddr, ucValue )       outp( xAddr, ucValue )
#define portINPUT_WORD( xAddr )                 inpw( xAddr )
#define portOUTPUT_WORD( xAddr, usValue )       outpw( xAddr, usValue )
/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

