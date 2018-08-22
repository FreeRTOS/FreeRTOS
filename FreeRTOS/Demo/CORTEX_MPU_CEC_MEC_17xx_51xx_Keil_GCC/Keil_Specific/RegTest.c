/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/*
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 */

void vRegTest1Implementation( void *pvParameters );
void vRegTest2Implementation( void *pvParameters );
void vRegTest3Implementation( void );
void vRegTest4Implementation( void );

/*
 * Used as an easy way of deleting a task from inline assembly.
 */
extern void vMainDeleteMe( void ) __attribute__((noinline));

/*
 * Used by the first two reg test tasks and a software timer callback function
 * to send messages to the check task.  The message just lets the check task
 * know that the tasks and timer are still functioning correctly.  If a reg test
 * task detects an error it will delete itself, and in so doing prevent itself
 * from sending any more 'I'm Alive' messages to the check task.
 */
extern void vMainSendImAlive( QueueHandle_t xHandle, uint32_t ulTaskNumber );

/* The queue used to send a message to the check task. */
extern QueueHandle_t xGlobalScopeCheckQueue;

/*-----------------------------------------------------------*/

void vRegTest1Implementation( void *pvParameters )
{
/* This task is created in privileged mode so can access the file scope
queue variable.  Take a stack copy of this before the task is set into user
mode.  Once this task is in user mode the file scope queue variable will no
longer be accessible but the stack copy will. */
QueueHandle_t xQueue = xGlobalScopeCheckQueue;
const TickType_t xDelayTime = pdMS_TO_TICKS( 100UL );

	/* Now the queue handle has been obtained the task can switch to user
	mode.  This is just one method of passing a handle into a protected
	task, the other	reg test task uses the task parameter instead. */
	portSWITCH_TO_USER_MODE();

	/* First check that the parameter value is as expected. */
	if( pvParameters != ( void * ) configREG_TEST_TASK_1_PARAMETER )
	{
		/* Error detected.  Delete the task so it stops communicating with
		the check task. */
		vMainDeleteMe();
	}

	for( ;; )
	{
		#if defined ( __GNUC__ )
		{
			/* This task tests the kernel context switch mechanism by reading and
			writing directly to registers - which requires the test to be written
			in assembly code. */
			__asm volatile
			(
				"		MOV	R4, #104			\n" /* Set registers to a known value.  R0 to R1 are done in the loop below. */
				"		MOV	R5, #105			\n"
				"		MOV	R6, #106			\n"
				"		MOV	R8, #108			\n"
				"		MOV	R9, #109			\n"
				"		MOV	R10, #110			\n"
				"		MOV	R11, #111			\n"
				"reg1loop:						\n"
				"		MOV	R0, #100			\n" /* Set the scratch registers to known values - done inside the loop as they get clobbered. */
				"		MOV	R1, #101			\n"
				"		MOV	R2, #102			\n"
				"		MOV R3, #103			\n"
				"		MOV	R12, #112			\n"
				"		SVC #1					\n" /* Yield just to increase test coverage. */
				"		CMP	R0, #100			\n" /* Check all the registers still contain their expected values. */
				"		BNE	vMainDeleteMe		\n" /* Value was not as expected, delete the task so it stops communicating with the check task. */
				"		CMP	R1, #101			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R2, #102			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP R3, #103			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R4, #104			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R5, #105			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R6, #106			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R8, #108			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R9, #109			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R10, #110			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R11, #111			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R12, #112			\n"
				"		BNE	vMainDeleteMe		\n"
				:::"r0", "r1", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
			);
		}
		#endif /* __GNUC__ */

		/* Send configREG_TEST_1_STILL_EXECUTING to the check task to indicate that this
		task is still functioning. */
		vMainSendImAlive( xQueue, configREG_TEST_1_STILL_EXECUTING );
		vTaskDelay( xDelayTime );

		#if defined ( __GNUC__ )
		{
			/* Go back to check all the register values again. */
			__asm volatile( "		B reg1loop	" );
		}
		#endif /* __GNUC__ */
	}
}
/*-----------------------------------------------------------*/

void vRegTest2Implementation( void *pvParameters )
{
/* The queue handle is passed in as the task parameter.  This is one method of
passing data into a protected task, the other reg test task uses a different
method. */
QueueHandle_t xQueue = ( QueueHandle_t ) pvParameters;
const TickType_t xDelayTime = pdMS_TO_TICKS( 100UL );

	for( ;; )
	{
		#if defined ( __GNUC__ )
		{
			/* This task tests the kernel context switch mechanism by reading and
			writing directly to registers - which requires the test to be written
			in assembly code. */
			__asm volatile
			(
				"		MOV	R4, #4				\n" /* Set registers to a known value.  R0 to R1 are done in the loop below. */
				"		MOV	R5, #5				\n"
				"		MOV	R6, #6				\n"
				"		MOV	R8, #8				\n" /* Frame pointer is omitted as it must not be changed. */
				"		MOV	R9, #9				\n"
				"		MOV	R10, 10				\n"
				"		MOV	R11, #11			\n"
				"reg2loop:						\n"
				"		MOV	R0, #13				\n" /* Set the scratch registers to known values - done inside the loop as they get clobbered. */
				"		MOV	R1, #1				\n"
				"		MOV	R2, #2				\n"
				"		MOV R3, #3				\n"
				"		MOV	R12, #12			\n"
				"		CMP	R0, #13				\n" /* Check all the registers still contain their expected values. */
				"		BNE	vMainDeleteMe		\n" /* Value was not as expected, delete the task so it stops communicating with the check task */
				"		CMP	R1, #1				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R2, #2				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP R3, #3				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R4, #4				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R5, #5				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R6, #6				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R8, #8				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R9, #9				\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R10, #10			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R11, #11			\n"
				"		BNE	vMainDeleteMe		\n"
				"		CMP	R12, #12			\n"
				"		BNE	vMainDeleteMe		\n"
				:::"r0", "r1", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
			);
		}
		#endif /* __GNUC__ */

		/* Send configREG_TEST_2_STILL_EXECUTING to the check task to indicate
		that this task is still functioning. */
		vMainSendImAlive( xQueue, configREG_TEST_2_STILL_EXECUTING );
		vTaskDelay( xDelayTime );

		#if defined ( __GNUC__ )
		{
			/* Go back to check all the register values again. */
			__asm volatile( "		B reg2loop	" );
		}
		#endif /* __GNUC__ */
	}
}
/*-----------------------------------------------------------*/

__asm void vRegTest3Implementation( void )
{
	extern pulRegTest3LoopCounter

	PRESERVE8

	/* Fill the core registers with known values. */
	mov	r0, #100
	mov	r1, #101
	mov	r2, #102
	mov	r3, #103
	mov	r4, #104
	mov	r5, #105
	mov	r6, #106
	mov	r7, #107
	mov	r8, #108
	mov	r9, #109
	mov	r10, #110
	mov	r11, #111
	mov	r12, #112

	/* Fill the VFP registers with known values. */
	vmov	d0, r0, r1
	vmov	d1, r2, r3
	vmov	d2, r4, r5
	vmov	d3, r6, r7
	vmov	d4, r8, r9
	vmov	d5, r10, r11
	vmov	d6, r0, r1
	vmov	d7, r2, r3
	vmov	d8, r4, r5
	vmov	d9, r6, r7
	vmov	d10, r8, r9
	vmov	d11, r10, r11
	vmov	d12, r0, r1
	vmov	d13, r2, r3
	vmov	d14, r4, r5
	vmov	d15, r6, r7

reg1_loop

	/* Check all the VFP registers still contain the values set above.
	First save registers that are clobbered by the test. */
	push { r0-r1 }

	vmov	r0, r1, d0
	cmp 	r0, #100
	bne 	reg1_error_loopf
	cmp 	r1, #101
	bne 	reg1_error_loopf
	vmov 	r0, r1, d1
	cmp 	r0, #102
	bne 	reg1_error_loopf
	cmp 	r1, #103
	bne 	reg1_error_loopf
	vmov 	r0, r1, d2
	cmp 	r0, #104
	bne 	reg1_error_loopf
	cmp 	r1, #105
	bne 	reg1_error_loopf
	vmov 	r0, r1, d3
	cmp 	r0, #106
	bne 	reg1_error_loopf
	cmp 	r1, #107
	bne 	reg1_error_loopf
	vmov 	r0, r1, d4
	cmp 	r0, #108
	bne 	reg1_error_loopf
	cmp 	r1, #109
	bne 	reg1_error_loopf
	vmov 	r0, r1, d5
	cmp 	r0, #110
	bne 	reg1_error_loopf
	cmp 	r1, #111
	bne 	reg1_error_loopf
	vmov 	r0, r1, d6
	cmp 	r0, #100
	bne 	reg1_error_loopf
	cmp 	r1, #101
	bne 	reg1_error_loopf
	vmov 	r0, r1, d7
	cmp 	r0, #102
	bne 	reg1_error_loopf
	cmp 	r1, #103
	bne 	reg1_error_loopf
	vmov 	r0, r1, d8
	cmp 	r0, #104
	bne 	reg1_error_loopf
	cmp 	r1, #105
	bne 	reg1_error_loopf
	vmov 	r0, r1, d9
	cmp 	r0, #106
	bne 	reg1_error_loopf
	cmp 	r1, #107
	bne 	reg1_error_loopf
	vmov 	r0, r1, d10
	cmp 	r0, #108
	bne 	reg1_error_loopf
	cmp 	r1, #109
	bne 	reg1_error_loopf
	vmov 	r0, r1, d11
	cmp 	r0, #110
	bne 	reg1_error_loopf
	cmp 	r1, #111
	bne 	reg1_error_loopf
	vmov 	r0, r1, d12
	cmp 	r0, #100
	bne 	reg1_error_loopf
	cmp 	r1, #101
	bne 	reg1_error_loopf
	vmov	r0, r1, d13
	cmp 	r0, #102
	bne 	reg1_error_loopf
	cmp 	r1, #103
	bne 	reg1_error_loopf
	vmov 	r0, r1, d14
	cmp 	r0, #104
	bne 	reg1_error_loopf
	cmp 	r1, #105
	bne 	reg1_error_loopf
	vmov 	r0, r1, d15
	cmp 	r0, #106
	bne 	reg1_error_loopf
	cmp 	r1, #107
	bne 	reg1_error_loopf

	/* Restore the registers that were clobbered by the test. */
	pop 	{r0-r1}

	/* VFP register test passed.  Jump to the core register test. */
	b 		reg1_loopf_pass

reg1_error_loopf
	/* If this line is hit then a VFP register value was found to be incorrect. */
	b reg1_error_loopf

reg1_loopf_pass

	cmp	r0, #100
	bne	reg1_error_loop
	cmp	r1, #101
	bne	reg1_error_loop
	cmp	r2, #102
	bne	reg1_error_loop
	cmp 	r3, #103
	bne	reg1_error_loop
	cmp	r4, #104
	bne	reg1_error_loop
	cmp	r5, #105
	bne	reg1_error_loop
	cmp	r6, #106
	bne	reg1_error_loop
	cmp	r7, #107
	bne	reg1_error_loop
	cmp	r8, #108
	bne	reg1_error_loop
	cmp	r9, #109
	bne	reg1_error_loop
	cmp	r10, #110
	bne	reg1_error_loop
	cmp	r11, #111
	bne	reg1_error_loop
	cmp	r12, #112
	bne	reg1_error_loop

	/* Everything passed, increment the loop counter. */
	push 	{ r0-r1 }
	ldr	r0, =pulRegTest3LoopCounter
	ldr	r0, [r0]
	ldr 	r1, [r0]
	adds 	r1, r1, #1
	str 	r1, [r0]
	pop 	{ r0-r1 }

	/* Start again. */
	b 		reg1_loop

reg1_error_loop
	/* If this line is hit then there was an error in a core register value.
	The loop ensures the loop counter stops incrementing. */
	b 	reg1_error_loop
	nop
	nop
}
/*-----------------------------------------------------------*/

__asm void vRegTest4Implementation( void )
{
	extern pulRegTest4LoopCounter;

	PRESERVE8

	/* Set all the core registers to known values. */
	mov 	r0, #-1
	mov 	r1, #1
	mov 	r2, #2
	mov 	r3, #3
	mov	r4, #4
	mov	r5, #5
	mov	r6, #6
	mov 	r7, #7
	mov	r8, #8
	mov	r9, #9
	mov	r10, #10
	mov	r11, #11
	mov 	r12, #12

	/* Set all the VFP to known values. */
	vmov 	d0, r0, r1
	vmov 	d1, r2, r3
	vmov 	d2, r4, r5
	vmov 	d3, r6, r7
	vmov 	d4, r8, r9
	vmov 	d5, r10, r11
	vmov 	d6, r0, r1
	vmov 	d7, r2, r3
	vmov 	d8, r4, r5
	vmov 	d9, r6, r7
	vmov 	d10, r8, r9
	vmov 	d11, r10, r11
	vmov 	d12, r0, r1
	vmov 	d13, r2, r3
	vmov 	d14, r4, r5
	vmov 	d15, r6, r7

reg2_loop

	/* Check all the VFP registers still contain the values set above.
	First save registers that are clobbered by the test. */
	push { r0-r1 }

	vmov	r0, r1, d0
	cmp	r0, #-1
	bne	reg2_error_loopf
	cmp	r1, #1
	bne	reg2_error_loopf
	vmov	r0, r1, d1
	cmp 	r0, #2
	bne 	reg2_error_loopf
	cmp 	r1, #3
	bne 	reg2_error_loopf
	vmov 	r0, r1, d2
	cmp 	r0, #4
	bne 	reg2_error_loopf
	cmp 	r1, #5
	bne 	reg2_error_loopf
	vmov 	r0, r1, d3
	cmp 	r0, #6
	bne 	reg2_error_loopf
	cmp 	r1, #7
	bne 	reg2_error_loopf
	vmov 	r0, r1, d4
	cmp 	r0, #8
	bne 	reg2_error_loopf
	cmp 	r1, #9
	bne 	reg2_error_loopf
	vmov 	r0, r1, d5
	cmp 	r0, #10
	bne 	reg2_error_loopf
	cmp 	r1, #11
	bne 	reg2_error_loopf
	vmov 	r0, r1, d6
	cmp 	r0, #-1
	bne 	reg2_error_loopf
	cmp 	r1, #1
	bne 	reg2_error_loopf
	vmov 	r0, r1, d7
	cmp 	r0, #2
	bne 	reg2_error_loopf
	cmp 	r1, #3
	bne 	reg2_error_loopf
	vmov 	r0, r1, d8
	cmp 	r0, #4
	bne 	reg2_error_loopf
	cmp 	r1, #5
	bne 	reg2_error_loopf
	vmov 	r0, r1, d9
	cmp 	r0, #6
	bne 	reg2_error_loopf
	cmp 	r1, #7
	bne 	reg2_error_loopf
	vmov 	r0, r1, d10
	cmp 	r0, #8
	bne 	reg2_error_loopf
	cmp 	r1, #9
	bne 	reg2_error_loopf
	vmov 	r0, r1, d11
	cmp 	r0, #10
	bne 	reg2_error_loopf
	cmp 	r1, #11
	bne 	reg2_error_loopf
	vmov 	r0, r1, d12
	cmp 	r0, #-1
	bne 	reg2_error_loopf
	cmp 	r1, #1
	bne 	reg2_error_loopf
	vmov 	r0, r1, d13
	cmp 	r0, #2
	bne 	reg2_error_loopf
	cmp 	r1, #3
	bne 	reg2_error_loopf
	vmov 	r0, r1, d14
	cmp 	r0, #4
	bne 	reg2_error_loopf
	cmp 	r1, #5
	bne 	reg2_error_loopf
	vmov 	r0, r1, d15
	cmp 	r0, #6
	bne 	reg2_error_loopf
	cmp 	r1, #7
	bne 	reg2_error_loopf

	/* Restore the registers that were clobbered by the test. */
	pop 	{r0-r1}

	/* VFP register test passed.  Jump to the core register test. */
	b 		reg2_loopf_pass

reg2_error_loopf
	/* If this line is hit then a VFP register value was found to be
	incorrect. */
	b reg2_error_loopf

reg2_loopf_pass

	cmp	r0, #-1
	bne	reg2_error_loop
	cmp	r1, #1
	bne	reg2_error_loop
	cmp	r2, #2
	bne	reg2_error_loop
	cmp 	r3, #3
	bne	reg2_error_loop
	cmp	r4, #4
	bne	reg2_error_loop
	cmp	r5, #5
	bne	reg2_error_loop
	cmp	r6, #6
	bne	reg2_error_loop
	cmp	r7, #7
	bne	reg2_error_loop
	cmp	r8, #8
	bne	reg2_error_loop
	cmp	r9, #9
	bne	reg2_error_loop
	cmp	r10, #10
	bne	reg2_error_loop
	cmp	r11, #11
	bne	reg2_error_loop
	cmp	r12, #12
	bne	reg2_error_loop

	/* Increment the loop counter so the check task knows this task is
	still running. */
	push	{ r0-r1 }
	ldr	r0, =pulRegTest4LoopCounter
	ldr	r0, [r0]
	ldr 	r1, [r0]
	adds 	r1, r1, #1
	str 	r1, [r0]
	pop { r0-r1 }

	/* Yield to increase test coverage. */
	SVC #1

	/* Start again. */
	b reg2_loop

reg2_error_loop
	/* If this line is hit then there was an error in a core register value.
	This loop ensures the loop counter variable stops incrementing. */
	b reg2_error_loop
	nop
}
/*-----------------------------------------------------------*/

/* Fault handlers are here for convenience as they use compiler specific syntax
and this file is specific to the Keil compiler. */
void hard_fault_handler( uint32_t * hardfault_args )
{
volatile uint32_t stacked_r0;
volatile uint32_t stacked_r1;
volatile uint32_t stacked_r2;
volatile uint32_t stacked_r3;
volatile uint32_t stacked_r12;
volatile uint32_t stacked_lr;
volatile uint32_t stacked_pc;
volatile uint32_t stacked_psr;

	stacked_r0 = ((uint32_t) hardfault_args[ 0 ]);
	stacked_r1 = ((uint32_t) hardfault_args[ 1 ]);
	stacked_r2 = ((uint32_t) hardfault_args[ 2 ]);
	stacked_r3 = ((uint32_t) hardfault_args[ 3 ]);

	stacked_r12 = ((uint32_t) hardfault_args[ 4 ]);
	stacked_lr = ((uint32_t) hardfault_args[ 5 ]);
	stacked_pc = ((uint32_t) hardfault_args[ 6 ]);
	stacked_psr = ((uint32_t) hardfault_args[ 7 ]);

	/* Inspect stacked_pc to locate the offending instruction. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void HardFault_Handler( void );
__asm void HardFault_Handler( void )
{
	extern hard_fault_handler

	tst lr, #4
	ite eq
	mrseq r0, msp
	mrsne r0, psp
	ldr r1, [r0, #24]
	ldr r2, hard_fault_handler
	bx r2
}
/*-----------------------------------------------------------*/

void MemManage_Handler( void );
__asm void MemManage_Handler( void )
{
	extern hard_fault_handler

	tst lr, #4
	ite eq
	mrseq r0, msp
	mrsne r0, psp
	ldr r1, [r0, #24]
	ldr r2, hard_fault_handler
	bx r2
}
/*-----------------------------------------------------------*/
