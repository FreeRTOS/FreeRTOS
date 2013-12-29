/*
    FreeRTOS V4.1.1 - Copyright (C) 2003-2006 Richard Barry.
    MCF5235 Port - Copyright (C) 2006 Christian Walter.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License** as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FreeRTOS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FreeRTOS; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    A special exception to the GPL can be applied should you wish to distribute
    a combined work that includes FreeRTOS, without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details of how and when the exception
    can be applied.

    ***************************************************************************
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
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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

/* ------------------------ Data types for Coldfire ----------------------- */
#define portCHAR        char
#define portFLOAT       float
#define portDOUBLE      double
#define portLONG        long
#define portSHORT       short
#define portSTACK_TYPE  unsigned int
#define portBASE_TYPE   int

typedef portSTACK_TYPE StackType_t;
typedef long BaseType_t;
typedef unsigned long UBaseType_t;

#if( configUSE_16_BIT_TICKS == 1 )
    typedef uint16_t TickType_t;
    #define portMAX_DELAY ( TickType_t ) 0xffff
#else
    typedef uint32_t TickType_t;
    #define portMAX_DELAY ( TickType_t ) 0xffffffffUL
#endif

/* ------------------------ Architecture specifics ------------------------ */
#define portSTACK_GROWTH                ( -1 )
#define portTICK_RATE_MS                ( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT              4

#define portTRAP_YIELD                  0   /* Trap 0 */
#define portIPL_MAX                     7   /* Only NMI interrupt 7 allowed. */

/* ------------------------ FreeRTOS macros for port ---------------------- */

/*
 * This function must be called when the current state of the active task
 * should be stored. It must be called immediately after exception
 * processing from the CPU, i.e. there exists a Coldfire exception frame at
 * the current position in the stack. The function reserves space on
 * the stack for the CPU registers and other task dependent values (e.g
 * ulCriticalNesting) and updates the top of the stack in the TCB.
 */
#define portSAVE_CONTEXT()                                                   \
    asm volatile ( /* reserve space for task state. */                       \
                   "lea.l   (-64, %sp), %sp\n\t"                             \
                   /* push data register %d0-%d7/%a0-%a6 on stack. */        \
                   "movem.l %d0-%d7/%a0-%a6, (%sp)\n\t"                      \
                   /* push ulCriticalNesting counter on stack. */            \
                   "lea.l  (60, %sp), %a0\n\t"                               \
                   "move.l  ulCriticalNesting, (%a0)\n\t"                    \
                   /* set the new top of the stack in the TCB. */            \
                   "move.l  pxCurrentTCB, %a0\n\t"                           \
                   "move.l  %sp, (%a0)");

/*.
 * This function restores the current active and continues its execution.
 * It loads the current TCB and restores the processor registers, the
 * task dependent values (e.g ulCriticalNesting). Finally execution
 * is continued by executing an rte instruction.
 */
#define portRESTORE_CONTEXT()                                                \
    asm volatile ( "move.l  pxCurrentTCB, %sp\n\t"                           \
                   "move.l  (%sp), %sp\n\t"                                  \
                   /* stack pointer now points to the saved registers. */    \
                   "movem.l (%sp), %d0-%d7/%a0-%a6\n\t"                      \
                   /* restore ulCriticalNesting counter from stack. */       \
                   "lea.l   (%sp, 60), %sp\n\t"                              \
                   "move.l  (%sp)+, ulCriticalNesting\n\t"                   \
                   /* stack pointer now points to exception frame. */        \
                   "rte\n\t" );

#define portENTER_CRITICAL()                                                 \
    vPortEnterCritical();

#define portEXIT_CRITICAL()                                                  \
    vPortExitCritical();

#define portSET_IPL( xIPL )                                                  \
    asm_set_ipl( xIPL )

#define portDISABLE_INTERRUPTS() \
    do { ( void )portSET_IPL( portIPL_MAX ); } while( 0 )
#define portENABLE_INTERRUPTS() \
    do { ( void )portSET_IPL( 0 ); } while( 0 )

#define portYIELD()                                                          \
    asm volatile ( " trap   %0\n\t" : : "i"(portTRAP_YIELD) )

#define portNOP()                                                            \
    asm volatile ( "nop\n\t" )

#define portENTER_SWITCHING_ISR()                                            \
    asm volatile ( "move.w  #0x2700, %sr" );                                 \
    /* Save the context of the interrupted task. */                          \
    portSAVE_CONTEXT(  );                                                    \
    {

#define portEXIT_SWITCHING_ISR( SwitchRequired )                             \
        /* If a switch is required we call vTaskSwitchContext(). */          \
        if( SwitchRequired )                                                 \
        {                                                                    \
            vTaskSwitchContext(  );                                          \
        }                                                                    \
    }                                                                        \
    portRESTORE_CONTEXT(  );

/* ------------------------ Function prototypes --------------------------- */
void vPortEnterCritical( void );
void vPortExitCritical( void );
int asm_set_ipl( uint32_t int uiNewIPL );

/* ------------------------ Compiler specifics ---------------------------- */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters )                   \
    void vFunction( void *pvParameters )

#define portTASK_FUNCTION( vFunction, pvParameters )                         \
    void vFunction( void *pvParameters )

#ifdef __cplusplus
}
#endif


#endif /* PORTMACRO_H */

