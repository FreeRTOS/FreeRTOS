/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the 16FX port.
 *----------------------------------------------------------*/

/* 
 * Get current value of DPR and ADB registers 
 */
StackType_t xGet_DPR_ADB_bank( void ); 

/* 
 * Get current value of DTB and PCB registers 
 */
StackType_t xGet_DTB_PCB_bank( void );

/*
 * Sets up the periodic ISR used for the RTOS tick.  This uses RLT0, but
 * can be done using any given RLT.
 */
static void prvSetupRLT0Interrupt( void );

/*-----------------------------------------------------------*/

/* 
 * We require the address of the pxCurrentTCB variable, but don't want to know
 * any details of its type. 
 */
typedef void TCB_t;
extern volatile TCB_t * volatile pxCurrentTCB;

/*-----------------------------------------------------------*/

/* 
 * Macro to save a task context to the task stack. This macro  copies the 
 * saved context (AH:AL, DPR:ADB, DTB:PCB , PC and PS) from  the   system 
 * stack to task stack pointed by user stack pointer ( USP  for SMALL and 
 * MEDIUM memory model amd USB:USP for COMPACT  and LARGE memory model ),
 * then  it pushes the general purpose registers RW0-RW7  on  to the task 
 * stack. Finally the  resultant  stack  pointer  value is saved into the 
 * task  control  block  so  it  can  be retrieved the next time the task 
 * executes.
 */ 
#if( ( configMEMMODEL == portSMALL ) || ( configMEMMODEL == portMEDIUM ) )

	#define portSAVE_CONTEXT()											\
			{	__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
	    		__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" PUSHW (RW0,RW1,RW2,RW3,RW4,RW5,RW6,RW7) ");		\
				__asm(" MOVW A, _pxCurrentTCB ");						\
				__asm(" MOVW A, SP ");									\
  				__asm(" SWAPW ");										\
				__asm(" MOVW @AL, AH ");								\
				__asm(" OR   CCR,#H'20 ");								\
			}

/* 
 * Macro to restore a task context from the task stack.  This is effecti-
 * vely the reverse of SAVE_CONTEXT(). First the stack pointer  value
 * (USP for SMALL and MEDIUM memory model amd  USB:USP  for  COMPACT  and 
 * LARGE memory model ) is loaded from the task  control block.  Next the 
 * value of all the general purpose registers RW0-RW7 is retrieved. Fina-
 * lly it copies of the context ( AH:AL,  DPR:ADB, DTB:PCB, PC and PS) of 
 * the task to be executed upon RETI from user stack to system stack.  
 */
 
	#define portRESTORE_CONTEXT()										\
			{	__asm(" MOVW A, _pxCurrentTCB ");						\
				__asm(" MOVW A, @A ");									\
  				__asm(" AND  CCR,#H'DF ");  							\
  				__asm(" MOVW SP, A ");									\
				__asm(" POPW (RW0,RW1,RW2,RW3,RW4,RW5,RW6,RW7) ");		\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
			}
		
#elif( ( configMEMMODEL == portCOMPACT ) || ( configMEMMODEL == portLARGE ) )

	#define portSAVE_CONTEXT()											\
			{	__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
	    		__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" POPW  A ");										\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" PUSHW  A ");									\
				__asm(" PUSHW (RW0,RW1,RW2,RW3,RW4,RW5,RW6,RW7) ");		\
				__asm(" MOVL A, _pxCurrentTCB ");						\
				__asm(" MOVL RL2, A ");									\
				__asm(" MOVW A, SP ");									\
				__asm(" MOVW @RL2+0, A ");								\
				__asm(" MOV A, USB ");									\
				__asm(" MOV @RL2+2, A ");								\
			}	
            
	#define portRESTORE_CONTEXT()										\
			{	__asm(" MOVL A, _pxCurrentTCB ");						\
				__asm(" MOVL RL2, A ");									\
				__asm(" MOVW A, @RL2+0 ");								\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" MOVW SP, A ");									\
				__asm(" MOV A, @RL2+2 ");								\
				__asm(" MOV USB, A ");									\
				__asm(" POPW (RW0,RW1,RW2,RW3,RW4,RW5,RW6,RW7) ");		\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
				__asm(" AND  CCR,#H'DF ");  							\
				__asm(" POPW  A ");										\
				__asm(" OR   CCR,#H'20 ");								\
				__asm(" PUSHW  A ");									\
			}
#endif

/*-----------------------------------------------------------*/	

/* 
 * Functions for obtaining the current value  of  DPR:ADB, DTB:PCB bank registers
 */
 
#pragma asm

        .GLOBAL    _xGet_DPR_ADB_bank
        .GLOBAL    _xGet_DTB_PCB_bank
        .SECTION   CODE, CODE, ALIGN=1

_xGet_DPR_ADB_bank:

    MOV A, DPR
    SWAP
    MOV A, ADB
    ORW A
	#if configMEMMODEL == portMEDIUM || configMEMMODEL == portLARGE
		RETP
	#elif configMEMMODEL == portSMALL || configMEMMODEL == portCOMPACT   
		RET
	#endif 


_xGet_DTB_PCB_bank:

    MOV A, DTB
    SWAP
    MOV A, PCB
    ORW A
	#if configMEMMODEL == portMEDIUM || configMEMMODEL == portLARGE
		RETP
	#elif configMEMMODEL == portSMALL || configMEMMODEL == portCOMPACT   
		RET
	#endif 

#pragma endasm
/*-----------------------------------------------------------*/

/* 
 * Initialise the stack of a task to look exactly as if a call to 
 * portSAVE_CONTEXT had been called.
 * 
 * See the header file portable.h.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/* Place a few bytes of known values on the bottom of the stack. 
	This is just useful for debugging. */
	*pxTopOfStack = 0x1111;
	pxTopOfStack--;
	*pxTopOfStack = 0x2222;
	pxTopOfStack--;
	*pxTopOfStack = 0x3333;
	pxTopOfStack--;

	/* Once the task is called the task  would  push  the  pointer to the
	parameter onto the stack. Hence here the pointer would be copied to the stack
	first.  When using the COMPACT or LARGE memory model the pointer would be 24 
	bits, and when using the SMALL or MEDIUM memory model the pointer would be 16 
	bits. */ 
	#if( ( configMEMMODEL == portCOMPACT ) || ( configMEMMODEL == portLARGE ) )
	{
		*pxTopOfStack = ( StackType_t ) ( ( uint32_t ) ( pvParameters ) >> 16 );
		pxTopOfStack--;         
	}
	#endif

    *pxTopOfStack = ( StackType_t ) ( pvParameters );
    pxTopOfStack--;                  
    
    /* This is redundant push to the stack. This is required in order to introduce 
    an offset so that the task accesses a parameter correctly that is passed on to 
    the task stack. */
	#if( ( configMEMMODEL == portMEDIUM ) || ( configMEMMODEL == portLARGE ) )
	{
		*pxTopOfStack = ( xGet_DTB_PCB_bank() & 0xff00 ) | ( ( ( int32_t ) ( pxCode ) >> 16 ) & 0xff );      
		pxTopOfStack--;       
	}
	#endif

    /* This is redundant push to the stack. This is required in order to introduce 
    an offset so the task correctly accesses the parameter passed on the task stack. */
    *pxTopOfStack = ( StackType_t ) ( pxCode );
    pxTopOfStack--;       

    /* PS - User Mode, ILM=7, RB=0, Interrupts enabled,USP */
    *pxTopOfStack = 0xE0C0;							
	pxTopOfStack--; 

	/* PC */
	*pxTopOfStack = ( StackType_t ) ( pxCode );     
    pxTopOfStack--;      
    
    /* DTB | PCB */
	#if configMEMMODEL == portSMALL || configMEMMODEL == portCOMPACT
	{
		*pxTopOfStack = xGet_DTB_PCB_bank();         	
		pxTopOfStack--;
	}
	#endif

	/* DTB | PCB, in case of MEDIUM and LARGE memory models, PCB would be used
	along with PC to indicate the start address of the function. */
	#if( ( configMEMMODEL == portMEDIUM ) || ( configMEMMODEL == portLARGE ) )
	{
		*pxTopOfStack = ( xGet_DTB_PCB_bank() & 0xff00 ) | ( ( ( int32_t ) ( pxCode ) >> 16 ) & 0xff );
		pxTopOfStack--;       
	}
	#endif

	/* DPR | ADB  */
	*pxTopOfStack = xGet_DPR_ADB_bank();				
	pxTopOfStack--;
    
	/* AL */
	*pxTopOfStack = ( StackType_t ) 0x9999;		
	pxTopOfStack--;

	/* AH */
	*pxTopOfStack = ( StackType_t ) 0xAAAA;		
	pxTopOfStack--;
	
	/* Next the general purpose registers. */
	*pxTopOfStack = ( StackType_t ) 0x7777;	/* RW7 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x6666;	/* RW6 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x5555;	/* RW5 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x4444;	/* RW4 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x3333;	/* RW3 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x2222;	/* RW2 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x1111;	/* RW1 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x8888;	/* RW0 */
		
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

static void prvSetupRLT0Interrupt( void )
{
/* The peripheral clock divided by 16 is used by the timer. */
const uint16_t usReloadValue = ( uint16_t ) ( ( ( configCLKP1_CLOCK_HZ / configTICK_RATE_HZ ) / 16UL ) - 1UL );

	/* set reload value = 34999+1, TICK Interrupt after 10 ms @ 56MHz of CLKP1 */
	TMRLR0 = usReloadValue;    
    
    /* prescaler 1:16, reload, interrupt enable, count enable, trigger */
    TMCSR0 = 0x041B;    
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	/* Setup the hardware to generate the tick. */
	prvSetupRLT0Interrupt();
	
	/* Restore the context of the first task that is going to run. */
	portRESTORE_CONTEXT();

	/* Simulate a function call end as generated by the compiler.  We will now
	jump to the start of the task the context of which we have just restored. */	
	__asm(" reti ");


	/* Should not get here. */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented - unlikely to ever be required as there is nothing to
	return to. */
}

/*-----------------------------------------------------------*/

/* 
 * The interrupt service routine used depends on whether the pre-emptive
 * scheduler is being used or not.
 */

#if configUSE_PREEMPTION == 1

	/* 
	 * Tick ISR for preemptive scheduler.  We can use a __nosavereg attribute
	 * as the context is to be saved by the portSAVE_CONTEXT() macro, not the
	 * compiler generated code.  The tick count is incremented after the context 
	 * is saved. 
	 */
	__nosavereg __interrupt void prvRLT0_TICKISR( void )
	{
		/* Disable interrupts so that portSAVE_CONTEXT() is not interrupted */
		__DI();
		
		/* Save the context of the interrupted task. */
		portSAVE_CONTEXT();
		
		/* Enable interrupts */
		__EI();
		
		/* Clear RLT0 interrupt flag */
		TMCSR0_UF = 0;      
		
		/* Increment the tick count then switch to the highest priority task
		that is ready to run. */
		if( xTaskIncrementTick() != pdFALSE )
		{
			vTaskSwitchContext();
		}

		/* Disable interrupts so that portRESTORE_CONTEXT() is not interrupted */
		__DI();
		
		/* Restore the context of the new task. */
		portRESTORE_CONTEXT();
		
		/* Enable interrupts */
		__EI();
	}

#else

	/*
	 * Tick ISR for the cooperative scheduler.  All this does is increment the
	 * tick count.  We don't need to switch context, this can only be done by
	 * manual calls to taskYIELD();
	 */
	__interrupt void prvRLT0_TICKISR( void )
	{
		/* Clear RLT0 interrupt flag */
		TMCSR0_UF = 0;  
		
		xTaskIncrementTick();
	}

#endif

/*-----------------------------------------------------------*/

/*
 * Manual context switch. We can use a __nosavereg attribute  as the context 
 * is to be saved by the portSAVE_CONTEXT() macro, not the compiler generated 
 * code.
 */
__nosavereg __interrupt void vPortYield( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();
	
	/* Switch to the highest priority task that is ready to run. */
	vTaskSwitchContext();
	
	/* Restore the context of the new task. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

__nosavereg __interrupt void vPortYieldDelayed( void )
{    
    /* Disable interrupts so that portSAVE_CONTEXT() is not interrupted */      
	__DI();
	
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();
	
	/* Enable interrupts */
	__EI();
				
	/* Clear delayed interrupt flag */
    __asm (" CLRB  03A4H:0 ");
	
	/* Switch to the highest priority task that is ready to run. */
	vTaskSwitchContext();
	
	/* Disable interrupts so that portSAVE_CONTEXT() is not interrupted */   
	__DI();
	
	/* Restore the context of the new task. */
	portRESTORE_CONTEXT();

	/* Enable interrupts */
	__EI();
}	
/*-----------------------------------------------------------*/

