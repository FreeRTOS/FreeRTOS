/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#ifndef PORTMACRO_H
#define PORTMACRO_H

#include <stdlib.h>
#include <stdint.h>
#include <csi_core.h>

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
#define portDOUBLE      double
#define portLONG        long
#define portSHORT       short
#define portSTACK_TYPE  uint32_t
#define portBASE_TYPE   long

typedef portSTACK_TYPE StackType_t;
typedef long BaseType_t;
typedef unsigned long UBaseType_t;
typedef void (*portvectorfunc)(void);

#if( configUSE_16_BIT_TICKS == 1 )
    typedef uint16_t  TickType_t;
    #define portMAX_DELAY ( TickType_t ) 0xffff
#else
    typedef uint32_t  TickType_t;
    #define portMAX_DELAY ( TickType_t ) 0xffffffffUL
#endif


/* Hardware specifics. */
#define portBYTE_ALIGNMENT          8
#define portSTACK_GROWTH            -1
#define portMS_PERIOD_TICK          10

static inline void vPortEnableInterrupt( void )
{
    __enable_irq();
}

static inline void vPortDisableInterrupt( void )
{
    __disable_irq();
}

static inline portLONG GetCurrentPSR (void)
{
    return __get_PSR();
}

static inline portLONG SaveLocalPSR (void)
{
    portLONG flags = __get_PSR();
    __disable_irq();
    return flags;
}

static inline void RestoreLocalPSR (portLONG newMask)
{
    __asm__ __volatile__(
    "mtcr   %0, psr \n"
    :
    :"r" (newMask)
    :"memory"
    );
}

extern void vPortEnterCritical( void );
extern void vPortExitCritical( void );
extern __attribute__((naked)) void cpu_yeild(void);

#define portDISABLE_INTERRUPTS()                vPortDisableInterrupt()
#define portENABLE_INTERRUPTS()                 vPortEnableInterrupt()
#define portENTER_CRITICAL()                    vPortEnterCritical()
#define portEXIT_CRITICAL()                     vPortExitCritical()
#define portSET_INTERRUPT_MASK_FROM_ISR()       SaveLocalPSR()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR(a)    RestoreLocalPSR(a)

#define portNOP()                   asm("nop")

extern portLONG ulCriticalNesting;
extern portLONG pendsvflag;

#define portYIELD()                 cpu_yeild(); \
                                    portNOP();portNOP()

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters ) __attribute__((noreturn))
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*-----------------------------------------------------------*/

#define portEND_SWITCHING_ISR( xSwitchRequired )    do {    \
                                                            if( xSwitchRequired != pdFALSE )    \
                                                            {   \
                                                                portYIELD();    \
                                                            }   \
                                                    }while(0)

#define portYIELD_FROM_ISR( a )     portEND_SWITCHING_ISR( a )

#define configASSERT( a )   do {if ((a)==0){printf("Assert : %s %d\r\n", __FILE__, __LINE__);while(1);}}while(0)


#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

