#include <msp430x14x.h>

/*
 * Milos Prokic
 */

/**********************************************************
All Interrupts should follow the naming convention : ISR"name" and declared
as a normal function in C.

One must not forget to allocate interrupts below (see the line "MSPINT	OsTick"
below for an example).

By default the ISR will not cause the context switch, but if called in 
conjunction with portENTER_SWITCHING_ISR/portEXIT_SWITCHING_ISR(wakeup), where 
wakeup = TRUE upon exit the ISR will force the context switch via the 
ucReschedule global variable.
**********************************************************/	
MSPINT	macro name
_##name::
		call	#_portSAVE_CONTEXT		
		call	#_ISR##name                       
		br		#_portSWITCH_EXIT			
		endm


/**********************************************************
API code
**********************************************************/	

                .CODE
_vPortYield::
		/* Mimic an INT call by pushing SR. */
		push	SR			
		/* no INTs !! */
		dint				
		/* Save the context of the current task. */
		call	#_portSAVE_CONTEXT			
		/* Switch to the highest priority task that is ready to run. */
		call	#_vTaskSwitchContext		
		/* Restore the context of the new task. */
		br		#_portSWITCH_EXIT		

_xPortStartScheduler::
		/* Setup the hardware to generate the tick.  Interrupts are disabled when
		this function is called. */
		call	#_prvSetupTimerInterrupt

		/* Restore the context of the first task that is going to run. */
		jmp		_portRESTORE_CONTEXT
          
_portSAVE_CONTEXT::
		/* Function to save the context.  When this function is called the
		return address will appear on the stack.  This does not need to be
		saved so is overwritten by R4 - hence R4 is not saved initially.

		Save the general purpose registers. */
		push	R5		
		push	R6		
		push	R7
		push	R8		
		push	R9
		push	R10		
		push	R11		
		push	R12		
		push	R13		
		push	R14		
		push	R15					

		/* Now R10 has been saved we can use it to hold the return address, 
		which is about to be overwritten. */
		mov		22(R1),R10			

		/* Store R4 where the return address was on the stack. */
		mov		R4,22(R1)	

		/* Save the critical nesting depth. */
		mov.w	&_usCriticalNesting, R14   
		push	R14				

		/* Finally save the new top of stack. */
		mov.w	&_pxCurrentTCB, R12	
		mov.w	R1, @R12

		/* No rescheduling by default. */
		mov.b	#0,&_ucReschedule	

		/* Return using the saved return address. */
		br		R10					


_portSWITCH_EXIT::
		/* Check ucReschedule to see if a context switch is required. */
		tst.b	&_ucReschedule
		jz		_portRESTORE_CONTEXT
		call	#_vTaskSwitchContext
_portRESTORE_CONTEXT::	         
		/* Restore the context in the opposite order to the save. */
		mov.w	&_pxCurrentTCB, R12
		mov.w	@R12, R1
		pop		R15
		mov.w	R15, &_usCriticalNesting
		pop		R15
		pop		R14		
		pop		R13		
		pop		R12		
		pop		R11		
		pop		R10		
		pop		R9		
		pop		R8		
		pop		R7		
		pop		R6		
		pop		R5		
		pop		R4		

		/* Ensure any low power mode bits are cleared within the status
                register about to be restored. */
		bic #(SCG1+SCG0+OSCOFF+CPUOFF),0(SP)
		reti	
      

/**********************************************************
Allocate Interrupts using the MSPINT macro (defined at the top of this file.
ex: MSPINT "name"
**********************************************************/	
        
		MSPINT	OsTick
		MSPINT	Com1Rx
		MSPINT	Com1Tx
		

/*********************************************************
Interrupt Vectors
Timer_A0
ex: PORT1 would look like:
ORG PORT1_VECTOR
DW _"name"
**********************************************************/	
		.VECTORS
		.KEEP

		ORG		TIMERA0_VECTOR
		DW		_OsTick

		ORG		UART1RX_VECTOR
		DW		_Com1Rx

		ORG		UART1TX_VECTOR
		DW		_Com1Tx		
		
		END
