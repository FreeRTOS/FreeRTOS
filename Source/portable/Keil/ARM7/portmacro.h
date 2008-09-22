/*
	FreeRTOS.org V5.0.4 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
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
#define portSTACK_TYPE	unsigned portLONG
#define portBASE_TYPE	portLONG

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned portLONG portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/	

/* Hardware specifics. */
#define portSTACK_GROWTH			( -1 )
#define portTICK_RATE_MS			( ( portTickType ) 1000 / configTICK_RATE_HZ )		
#define portBYTE_ALIGNMENT			4
/*-----------------------------------------------------------*/	

/* Task utilities. */
#define portRESTORE_CONTEXT()																			\
{																										\
extern volatile unsigned portLONG ulCriticalNesting;													\
extern volatile void * volatile pxCurrentTCB;															\
																										\
	__asm{ LDR		R1, =pxCurrentTCB };/* Set the LR to the task stack.  The location was ... */		\
	__asm{ LDR		R0, [R1]		};	/* ... stored in pxCurrentTCB. */								\
	__asm{ LDR		LR, [R0]		};																	\
																										\
	__asm{ LDR		R0, =ulCriticalNesting }; /* The critical nesting depth is the first item on ... */	\
	__asm{ LDMFD	LR!, {R1 }		}  /* ... the stack.  Load it into the ulCriticalNesting var. */	\
	__asm{ STR		R1, [R0]		}																	\
																										\
	__asm{ LDMFD	LR!, {R0}		}; /* Get the SPSR from the stack. */								\
	__asm{ MSR		SPSR_CXSF, R0	};																	\
																										\
	__asm{ LDMFD	LR, {R0-R14}^	}; /* Restore all system mode registers for the task. */			\
	__asm{ NOP						};																	\
																										\
	__asm{ LDR		LR, [LR, #+60]	}; /* Restore the return address. */								\
																										\
									   /* And return - correcting the offset in the LR to obtain ... */ \
	__asm{ SUBS	PC, LR, #4			}; /* ... the correct address. */									\
}
/*----------------------------------------------------------*/

#define portSAVE_CONTEXT()																				\
{																										\
extern volatile unsigned portLONG ulCriticalNesting;													\
extern volatile void * volatile pxCurrentTCB;															\
																										\
	__asm{ STMDB 	SP!, {R0}		};	/* Store R0 first as we need to use it.						*/	\
																										\
	__asm{ STMDB	SP,{SP}^		}; /* Set R0 to point to the task stack pointer.				*/	\
	__asm{ NOP						};																	\
	__asm{ SUB		SP, SP, #4		};																	\
	__asm{ LDMIA	SP!,{R0}		};																	\
																										\																	
	__asm{ STMDB	R0!, {LR}		}; /* Push the return address onto the stack.					*/	\
	__asm{ MOV		LR, R0			}; /* Now we have saved LR we can use it instead of R0.			*/	\
	__asm{ LDMIA	SP!, {R0}		}; /* Pop R0 so we can save it onto the system mode stack.		*/	\
																										\
	__asm{ STMDB	LR,{R0-LR}^		}; /* Push all the system mode registers onto the task stack.	*/	\
	__asm{ NOP						};																	\
	__asm{ SUB		LR, LR, #60		};																	\
																										\
	__asm{ MRS		R0, SPSR		}; /* Push the SPSR onto the task stack.						*/	\
	__asm{ STMDB	LR!, {R0}		};																	\
																										\
	__asm{ LDR		R0, =ulCriticalNesting };															\
	__asm{ LDR		R0, [R0]		};																	\
	__asm{ STMDB	LR!, {R0}		};																	\
																										\
	__asm{ LDR		R0, =pxCurrentTCB };/* Store the new top of stack for the task.					*/	\
	__asm{ LDR		R1, [R0]		};																	\
	__asm{ STR		LR, [R1]		};																	\
}

/*-----------------------------------------------------------
 * ISR entry and exit macros.  These are only required if a task switch
 * is required from an ISR.
 *----------------------------------------------------------*/

#define portENTER_SWITCHING_ISR()										\
		portSAVE_CONTEXT();												\
		{

#define portEXIT_SWITCHING_ISR( SwitchRequired )						\
		/* If a switch is required then we just need to call */			\
		/* vTaskSwitchContext() as the context has already been */		\
		/* saved. */													\
		if( SwitchRequired )											\
		{																\
			vTaskSwitchContext();										\
		}																\
	}																	\
	/* Restore the context of which ever task is now the highest */		\
	/* priority that is ready to run. */								\
	portRESTORE_CONTEXT();


/* Yield the processor - force a context switch. */
#define portYIELD()					__asm{ SWI 0 };	
/*-----------------------------------------------------------*/	

/* Critical section management. */

/*-----------------------------------------------------------
 * Interrupt control macros.
 *
 * The interrupt management utilities can only be called from ARM mode.  When
 * KEIL_THUMB_INTERWORK is defined the utilities are defined as functions in 
 * portISR.c to ensure a switch to ARM mode.  When KEIL_THUMB_INTERWORK is not 
 * defined then the utilities are defined as macros here - as per other ports.
 *----------------------------------------------------------*/

#ifdef KEIL_THUMB_INTERWORK

	extern void vPortDisableInterruptsFromThumb( void ) __task;
	extern void vPortEnableInterruptsFromThumb( void ) __task;

	#define portDISABLE_INTERRUPTS()	vPortDisableInterruptsFromThumb()
	#define portENABLE_INTERRUPTS()		vPortEnableInterruptsFromThumb()

#else

	/*-----------------------------------------------------------*/

	#define portDISABLE_INTERRUPTS()														\
		__asm{ STMDB	SP!, {R0}		};	/* Push R0.									*/	\
		__asm{ MRS		R0, CPSR		};	/* Get CPSR.								*/	\
		__asm{ ORR		R0, R0, #0xC0	};	/* Disable IRQ, FIQ.						*/	\
		__asm{ MSR		CPSR_CXSF, R0	};	/* Write back modified value.				*/	\
		__asm{ LDMIA	SP!, {R0}		}	/* Pop R0.									*/
			
	#define portENABLE_INTERRUPTS()															\
		__asm{ STMDB	SP!, {R0}		};	/* Push R0.									*/	\
		__asm{ MRS		R0, CPSR		};	/* Get CPSR.								*/	\
		__asm{ BIC		R0, R0, #0xC0	};	/* Enable IRQ, FIQ.							*/	\
		__asm{ MSR		CPSR_CXSF, R0	};	/* Write back modified value.				*/	\
		__asm{ LDMIA	SP!, {R0}		}	/* Pop R0. */

#endif /* KEIL_THUMB_INTERWORK */

/*-----------------------------------------------------------
 * Critical section control
 *
 * The code generated by the Keil compiler does not maintain separate
 * stack and frame pointers. The portENTER_CRITICAL macro cannot therefore
 * use the stack as per other ports.  Instead a variable is used to keep
 * track of the critical section nesting.  This necessitates the use of a 
 * function in place of the macro.
 *----------------------------------------------------------*/

extern void vPortEnterCritical( void );
extern void vPortExitCritical( void );

#define portENTER_CRITICAL()		vPortEnterCritical();
#define portEXIT_CRITICAL()			vPortExitCritical();
/*-----------------------------------------------------------*/	

#define register
#define portNOP()	__asm{ NOP }
/*-----------------------------------------------------------*/	

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters )	void vFunction( void *pvParameters ) __task
#define portTASK_FUNCTION( vFunction, pvParameters )	void vFunction( void *pvParameters )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

