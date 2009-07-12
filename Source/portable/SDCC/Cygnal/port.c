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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the Cygnal port.
 *----------------------------------------------------------*/

/* Standard includes. */
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Constants required to setup timer 2 to produce the RTOS tick. */
#define portCLOCK_DIVISOR				( ( unsigned portLONG ) 12 )
#define portMAX_TIMER_VALUE				( ( unsigned portLONG ) 0xffff )
#define portENABLE_TIMER				( ( unsigned portCHAR ) 0x04 )
#define portTIMER_2_INTERRUPT_ENABLE	( ( unsigned portCHAR ) 0x20 )

/* The value used in the IE register when a task first starts. */
#define portGLOBAL_INTERRUPT_BIT	( ( portSTACK_TYPE ) 0x80 )

/* The value used in the PSW register when a task first starts. */
#define portINITIAL_PSW				( ( portSTACK_TYPE ) 0x00 )

/* Macro to clear the timer 2 interrupt flag. */
#define portCLEAR_INTERRUPT_FLAG()	TMR2CN &= ~0x80;

/* Used during a context switch to store the size of the stack being copied
to or from XRAM. */
data static unsigned portCHAR ucStackBytes;

/* Used during a context switch to point to the next byte in XRAM from/to which
a RAM byte is to be copied. */
xdata static portSTACK_TYPE * data pxXRAMStack;

/* Used during a context switch to point to the next byte in RAM from/to which
an XRAM byte is to be copied. */
data static portSTACK_TYPE * data pxRAMStack;

/* We require the address of the pxCurrentTCB variable, but don't want to know
any details of its type. */
typedef void tskTCB;
extern volatile tskTCB * volatile pxCurrentTCB;

/*
 * Setup the hardware to generate an interrupt off timer 2 at the required 
 * frequency.
 */
static void prvSetupTimerInterrupt( void );

/*-----------------------------------------------------------*/
/*
 * Macro that copies the current stack from internal RAM to XRAM.  This is 
 * required as the 8051 only contains enough internal RAM for a single stack, 
 * but we have a stack for every task.
 */
#define portCOPY_STACK_TO_XRAM()																\
{																								\
	/* pxCurrentTCB points to a TCB which itself points to the location into					\
	which the first	stack byte should be copied.  Set pxXRAMStack to point						\
	to the location into which the first stack byte is to be copied. */							\
	pxXRAMStack = ( xdata portSTACK_TYPE * ) *( ( xdata portSTACK_TYPE ** ) pxCurrentTCB );		\
																								\
	/* Set pxRAMStack to point to the first byte to be coped from the stack. */					\
	pxRAMStack = ( data portSTACK_TYPE * data ) configSTACK_START;								\
																								\
	/* Calculate the size of the stack we are about to copy from the current					\
	stack pointer value. */																		\
	ucStackBytes = SP - ( configSTACK_START - 1 );												\
																								\
	/* Before starting to copy the stack, store the calculated stack size so					\
	the stack can be restored when the task is resumed. */										\
	*pxXRAMStack = ucStackBytes;																\
																								\
	/* Copy each stack byte in turn.  pxXRAMStack is incremented first as we					\
	have already stored the stack size into XRAM. */											\
	while( ucStackBytes )																		\
	{																							\
		pxXRAMStack++;																			\
		*pxXRAMStack = *pxRAMStack;																\
		pxRAMStack++;																			\
		ucStackBytes--;																			\
	}																							\
}
/*-----------------------------------------------------------*/

/*
 * Macro that copies the stack of the task being resumed from XRAM into 
 * internal RAM.
 */
#define portCOPY_XRAM_TO_STACK()																\
{																								\
	/* Setup the pointers as per portCOPY_STACK_TO_XRAM(), but this time to						\
	copy the data back out of XRAM and into the stack. */										\
	pxXRAMStack = ( xdata portSTACK_TYPE * ) *( ( xdata portSTACK_TYPE ** ) pxCurrentTCB );		\
	pxRAMStack = ( data portSTACK_TYPE * data ) ( configSTACK_START - 1 );						\
																								\
	/* The first value stored in XRAM was the size of the stack - i.e. the						\
	number of bytes we need to copy back. */													\
	ucStackBytes = pxXRAMStack[ 0 ];															\
																								\
	/* Copy the required number of bytes back into the stack. */								\
	do																							\
	{																							\
		pxXRAMStack++;																			\
		pxRAMStack++;																			\
		*pxRAMStack = *pxXRAMStack;																\
		ucStackBytes--;																			\
	} while( ucStackBytes );																	\
																								\
	/* Restore the stack pointer ready to use the restored stack. */							\
	SP = ( unsigned portCHAR ) pxRAMStack;														\
}
/*-----------------------------------------------------------*/

/*
 * Macro to push the current execution context onto the stack, before the stack 
 * is moved to XRAM. 
 */
#define portSAVE_CONTEXT()																		\
{																								\
	_asm																						\
		/* Push ACC first, as when restoring the context it must be restored					\
		last (it is used to set the IE register). */											\
		push	ACC																				\
		/* Store the IE register then disable interrupts. */									\
		push	IE																				\
		clr		_EA																				\
		push	DPL																				\
		push	DPH																				\
		push	b																				\
		push	ar2																				\
		push	ar3																				\
		push	ar4																				\
		push	ar5																				\
		push	ar6																				\
		push	ar7																				\
		push	ar0																				\
		push	ar1																				\
		push	PSW																				\
	_endasm;																					\
		PSW = 0;																				\
	_asm																						\
		push	_bp																				\
	_endasm;																					\
}
/*-----------------------------------------------------------*/

/*
 * Macro that restores the execution context from the stack.  The execution 
 * context was saved into the stack before the stack was copied into XRAM.
 */
#define portRESTORE_CONTEXT()																	\
{																								\
	_asm																						\
		pop		_bp																				\
		pop		PSW																				\
		pop		ar1																				\
		pop		ar0																				\
		pop		ar7																				\
		pop		ar6																				\
		pop		ar5																				\
		pop		ar4																				\
		pop		ar3																				\
		pop		ar2																				\
		pop		b																				\
		pop		DPH																				\
		pop		DPL																				\
		/* The next byte of the stack is the IE register.  Only the global						\
		enable bit forms part of the task context.  Pop off the IE then set						\
		the global enable bit to match that of the stored IE register. */						\
		pop		ACC																				\
		JB		ACC.7,0098$																		\
		CLR		IE.7																			\
		LJMP	0099$																			\
	0098$:																						\
		SETB	IE.7																			\
	0099$:																						\
		/* Finally pop off the ACC, which was the first register saved. */						\
		pop		ACC																				\
		reti																					\
	_endasm;																					\
}
/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
unsigned portLONG ulAddress;
portSTACK_TYPE *pxStartOfStack;

	/* Leave space to write the size of the stack as the first byte. */
	pxStartOfStack = pxTopOfStack;
	pxTopOfStack++;

	/* Place a few bytes of known values on the bottom of the stack. 
	This is just useful for debugging and can be uncommented if required.
	*pxTopOfStack = 0x11;
	pxTopOfStack++;
	*pxTopOfStack = 0x22;
	pxTopOfStack++;
	*pxTopOfStack = 0x33;
	pxTopOfStack++;
	*/

	/* Simulate how the stack would look after a call to the scheduler tick 
	ISR. 

	The return address that would have been pushed by the MCU. */
	ulAddress = ( unsigned portLONG ) pxCode;
	*pxTopOfStack = ( portSTACK_TYPE ) ulAddress;
	ulAddress >>= 8;
	pxTopOfStack++;
	*pxTopOfStack = ( portSTACK_TYPE ) ( ulAddress );
	pxTopOfStack++;

	/* Next all the registers will have been pushed by portSAVE_CONTEXT(). */
	*pxTopOfStack = 0xaa;	/* acc */
	pxTopOfStack++;	

	/* We want tasks to start with interrupts enabled. */
	*pxTopOfStack = portGLOBAL_INTERRUPT_BIT;
	pxTopOfStack++;

	/* The function parameters will be passed in the DPTR and B register as
	a three byte generic pointer is used. */
	ulAddress = ( unsigned portLONG ) pvParameters;
	*pxTopOfStack = ( portSTACK_TYPE ) ulAddress;	/* DPL */
	ulAddress >>= 8;
	*pxTopOfStack++;
	*pxTopOfStack = ( portSTACK_TYPE ) ulAddress;	/* DPH */
	ulAddress >>= 8;
	pxTopOfStack++;
	*pxTopOfStack = ( portSTACK_TYPE ) ulAddress;	/* b */
	pxTopOfStack++;

	/* The remaining registers are straight forward. */
	*pxTopOfStack = 0x02;	/* R2 */
	pxTopOfStack++;
	*pxTopOfStack = 0x03;	/* R3 */
	pxTopOfStack++;
	*pxTopOfStack = 0x04;	/* R4 */
	pxTopOfStack++;
	*pxTopOfStack = 0x05;	/* R5 */
	pxTopOfStack++;
	*pxTopOfStack = 0x06;	/* R6 */
	pxTopOfStack++;
	*pxTopOfStack = 0x07;	/* R7 */
	pxTopOfStack++;
	*pxTopOfStack = 0x00;	/* R0 */
	pxTopOfStack++;
	*pxTopOfStack = 0x01;	/* R1 */
	pxTopOfStack++;
	*pxTopOfStack = 0x00;	/* PSW */
	pxTopOfStack++;
	*pxTopOfStack = 0xbb;	/* BP */

	/* Dont increment the stack size here as we don't want to include
	the stack size byte as part of the stack size count.

	Finally we place the stack size at the beginning. */
	*pxStartOfStack = ( portSTACK_TYPE ) ( pxTopOfStack - pxStartOfStack );

	/* Unlike most ports, we return the start of the stack as this is where the
	size of the stack is stored. */
	return pxStartOfStack;
}
/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portBASE_TYPE xPortStartScheduler( void )
{
	/* Setup timer 2 to generate the RTOS tick. */
	prvSetupTimerInterrupt();	

	/* Make sure we start with the expected SFR page.  This line should not
	really be required. */
	SFRPAGE = 0;

	/* Copy the stack for the first task to execute from XRAM into the stack,
	restore the task context from the new stack, then start running the task. */
	portCOPY_XRAM_TO_STACK();
	portRESTORE_CONTEXT();

	/* Should never get here! */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented for this port. */
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch.  The first thing we do is save the registers so we
 * can use a naked attribute.
 */
void vPortYield( void ) _naked
{
	/* Save the execution context onto the stack, then copy the entire stack
	to XRAM.  This is necessary as the internal RAM is only large enough to
	hold one stack, and we want one per task. 
	
	PERFORMANCE COULD BE IMPROVED BY ONLY COPYING TO XRAM IF A TASK SWITCH
	IS REQUIRED. */
	portSAVE_CONTEXT();
	portCOPY_STACK_TO_XRAM();

	/* Call the standard scheduler context switch function. */
	vTaskSwitchContext();

	/* Copy the stack of the task about to execute from XRAM into RAM and
	restore it's context ready to run on exiting. */
	portCOPY_XRAM_TO_STACK();
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

#if configUSE_PREEMPTION == 1
	void vTimer2ISR( void ) interrupt 5 _naked
	{
		/* Preemptive context switch function triggered by the timer 2 ISR.
		This does the same as vPortYield() (see above) with the addition
		of incrementing the RTOS tick count. */

		portSAVE_CONTEXT();
		portCOPY_STACK_TO_XRAM();

		vTaskIncrementTick();
		vTaskSwitchContext();
		
		portCLEAR_INTERRUPT_FLAG();
		portCOPY_XRAM_TO_STACK();
		portRESTORE_CONTEXT();
	}
#else
	void vTimer2ISR( void ) interrupt 5
	{
		/* When using the cooperative scheduler the timer 2 ISR is only 
		required to increment the RTOS tick count. */

		vTaskIncrementTick();
		portCLEAR_INTERRUPT_FLAG();
	}
#endif
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
unsigned portCHAR ucOriginalSFRPage;

/* Constants calculated to give the required timer capture values. */
const unsigned portLONG ulTicksPerSecond = configCPU_CLOCK_HZ / portCLOCK_DIVISOR;
const unsigned portLONG ulCaptureTime = ulTicksPerSecond / configTICK_RATE_HZ;
const unsigned portLONG ulCaptureValue = portMAX_TIMER_VALUE - ulCaptureTime;
const unsigned portCHAR ucLowCaptureByte = ( unsigned portCHAR ) ( ulCaptureValue & ( unsigned portLONG ) 0xff );
const unsigned portCHAR ucHighCaptureByte = ( unsigned portCHAR ) ( ulCaptureValue >> ( unsigned portLONG ) 8 );

	/* NOTE:  This uses a timer only present on 8052 architecture. */

	/* Remember the current SFR page so we can restore it at the end of the
	function. */
	ucOriginalSFRPage = SFRPAGE;
	SFRPAGE = 0;

	/* TMR2CF can be left in its default state. */	
	TMR2CF = ( unsigned portCHAR ) 0;

	/* Setup the overflow reload value. */
	RCAP2L = ucLowCaptureByte;
	RCAP2H = ucHighCaptureByte;

	/* The initial load is performed manually. */
	TMR2L = ucLowCaptureByte;
	TMR2H = ucHighCaptureByte;

	/* Enable the timer 2 interrupts. */
	IE |= portTIMER_2_INTERRUPT_ENABLE;

	/* Interrupts are disabled when this is called so the timer can be started
	here. */
	TMR2CN = portENABLE_TIMER;

	/* Restore the original SFR page. */
	SFRPAGE = ucOriginalSFRPage;
}




