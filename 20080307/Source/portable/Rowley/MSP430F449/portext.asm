#include "FreeRTOSConfig.h"

portSAVE_CONTEXT macro
		push	r4
		push	r5
		push	r6
		push	r7
		push	r8
		push	r9
		push	r10
		push	r11
		push	r12
		push	r13
		push	r14
		push	r15
		mov.w	&_usCriticalNesting, r14
		push	r14
		mov.w	&_pxCurrentTCB, r12
		mov.w	r1, @r12
		endm
/*-----------------------------------------------------------*/
		
portRESTORE_CONTEXT macro
		mov.w	&_pxCurrentTCB, r12
		mov.w	@r12, r1
		pop		r15
		mov.w	r15, &_usCriticalNesting
		pop		r15
		pop		r14
		pop		r13
		pop		r12
		pop		r11
		pop		r10
		pop		r9
		pop		r8
		pop		r7
		pop		r6
		pop		r5
		pop		r4
		reti
		endm
/*-----------------------------------------------------------*/


.CODE

/*
 * The RTOS tick ISR.
 *
 * If the cooperative scheduler is in use this simply increments the tick 
 * count.
 *
 * If the preemptive scheduler is in use a context switch can also occur.
 */
_vTickISR:
		portSAVE_CONTEXT
				
		call	#_vTaskIncrementTick

		#if configUSE_PREEMPTION == 1
			call	#_vTaskSwitchContext
		#endif
		
		portRESTORE_CONTEXT
/*-----------------------------------------------------------*/


/*
 * Manual context switch called by the portYIELD() macro.
 */                
_vPortYield::

		/* Mimic an interrupt by pushing the SR. */
		push	SR			

		/* Now the SR is stacked we can disable interrupts. */
		dint			
				
		/* Save the context of the current task. */
        portSAVE_CONTEXT			

        /* Switch to the highest priority task that is ready to run. */
        call	#_vTaskSwitchContext		

        /* Restore the context of the new task. */
        portRESTORE_CONTEXT
/*-----------------------------------------------------------*/


/*
 * Start off the scheduler by initialising the RTOS tick timer, then restoring
 * the context of the first task.
 */
_xPortStartScheduler::

		/* Setup the hardware to generate the tick.  Interrupts are disabled 
		when this function is called. */
		call	#_prvSetupTimerInterrupt

		/* Restore the context of the first task that is going to run. */
		portRESTORE_CONTEXT
/*-----------------------------------------------------------*/          
      		

		/* Place the tick ISR in the correct vector. */
		.VECTORS
		
		.KEEP
		
		ORG		TIMERA0_VECTOR
		DW		_vTickISR
		


		END
		
