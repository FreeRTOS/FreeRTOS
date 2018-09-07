/*
 * FreeRTOS Kernel V10.1.1
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
void vRegTest3Implementation( void ) __attribute__ ((naked));
void vRegTest4Implementation( void ) __attribute__ ((naked));

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

		/* Send configREG_TEST_1_STILL_EXECUTING to the check task to indicate that this
		task is still functioning. */
		vMainSendImAlive( xQueue, configREG_TEST_1_STILL_EXECUTING );

		/* Go back to check all the register values again. */
		__asm volatile( "		B reg1loop	" );
	}
}
/*-----------------------------------------------------------*/

void vRegTest2Implementation( void *pvParameters )
{
/* The queue handle is passed in as the task parameter.  This is one method of
passing data into a protected task, the other reg test task uses a different
method. */
QueueHandle_t xQueue = ( QueueHandle_t ) pvParameters;

	for( ;; )
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

		/* Send configREG_TEST_2_STILL_EXECUTING to the check task to indicate that this
		task is still functioning. */
		vMainSendImAlive( xQueue, configREG_TEST_2_STILL_EXECUTING );

		/* Go back to check all the register values again. */
		__asm volatile( "		B reg2loop	" );
	}
}
/*-----------------------------------------------------------*/

void vRegTest3Implementation( void )
{
	__asm volatile
	(
		".extern pulRegTest3LoopCounter \n"
		"/* Fill the core registers with known values. */		\n"
		"mov	r0, #100			\n"
		"mov	r1, #101			\n"
		"mov	r2, #102			\n"
		"mov	r3, #103			\n"
		"mov	r4, #104			\n"
		"mov	r5, #105			\n"
		"mov	r6, #106			\n"
		"mov	r7, #107			\n"
		"mov	r8, #108			\n"
		"mov	r9, #109			\n"
		"mov	r10, #110			\n"
		"mov	r11, #111			\n"
		"mov	r12, #112			\n"

		"/* Fill the VFP registers with known values. */		\n"
		"vmov	d0, r0, r1			\n"
		"vmov	d1, r2, r3			\n"
		"vmov	d2, r4, r5			\n"
		"vmov	d3, r6, r7			\n"
		"vmov	d4, r8, r9			\n"
		"vmov	d5, r10, r11		\n"
		"vmov	d6, r0, r1			\n"
		"vmov	d7, r2, r3			\n"
		"vmov	d8, r4, r5			\n"
		"vmov	d9, r6, r7			\n"
		"vmov	d10, r8, r9			\n"
		"vmov	d11, r10, r11		\n"
		"vmov	d12, r0, r1			\n"
		"vmov	d13, r2, r3			\n"
		"vmov	d14, r4, r5			\n"
		"vmov	d15, r6, r7			\n"

	"reg1_loop:						\n"
		"/* Check all the VFP registers still contain the values set above.		\n"
		"First save registers that are clobbered by the test. */				\n"
		"push { r0-r1 }				\n"

		"vmov	r0, r1, d0			\n"
		"cmp 	r0, #100			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #101			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d1			\n"
		"cmp 	r0, #102			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #103			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d2			\n"
		"cmp 	r0, #104			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #105			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d3			\n"
		"cmp 	r0, #106			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #107			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d4			\n"
		"cmp 	r0, #108			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #109			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d5			\n"
		"cmp 	r0, #110			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #111			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d6			\n"
		"cmp 	r0, #100			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #101			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d7			\n"
		"cmp 	r0, #102			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #103			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d8			\n"
		"cmp 	r0, #104			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #105			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d9			\n"
		"cmp 	r0, #106			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #107			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d10			\n"
		"cmp 	r0, #108			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #109			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d11			\n"
		"cmp 	r0, #110			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #111			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d12			\n"
		"cmp 	r0, #100			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #101			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov	r0, r1, d13			\n"
		"cmp 	r0, #102			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #103			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d14			\n"
		"cmp 	r0, #104			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #105			\n"
		"bne 	reg1_error_loopf	\n"
		"vmov 	r0, r1, d15			\n"
		"cmp 	r0, #106			\n"
		"bne 	reg1_error_loopf	\n"
		"cmp 	r1, #107			\n"
		"bne 	reg1_error_loopf	\n"

		"/* Restore the registers that were clobbered by the test. */		\n"
		"pop 	{r0-r1}				\n"

		"/* VFP register test passed.  Jump to the core register test. */	\n"
		"b 		reg1_loopf_pass		\n"

	"reg1_error_loopf:				\n"
		"/* If this line is hit then a VFP register value was found to be incorrect. */		\n"
		"b reg1_error_loopf			\n"

	"reg1_loopf_pass:				\n"

		"cmp	r0, #100			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r1, #101			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r2, #102			\n"
		"bne	reg1_error_loop		\n"
		"cmp 	r3, #103			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r4, #104			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r5, #105			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r6, #106			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r7, #107			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r8, #108			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r9, #109			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r10, #110			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r11, #111			\n"
		"bne	reg1_error_loop		\n"
		"cmp	r12, #112			\n"
		"bne	reg1_error_loop		\n"

		"/* Everything passed, increment the loop counter. */	\n"
		"push 	{ r0-r1 }			\n"
		"ldr	r0, =pulRegTest3LoopCounter	\n"
		"ldr	r0, [r0]			\n"
		"ldr 	r1, [r0]			\n"
		"adds 	r1, r1, #1			\n"
		"str 	r1, [r0]			\n"
		"pop 	{ r0-r1 }			\n"

		"/* Start again. */			\n"
		"b 		reg1_loop			\n"

	"reg1_error_loop:				\n"
		"/* If this line is hit then there was an error in a core register value. \n"
		"The loop ensures the loop counter stops incrementing. */	\n"
		"b 	reg1_error_loop			\n"
		"nop						"
	); /* __asm volatile. */
}
/*-----------------------------------------------------------*/

void vRegTest4Implementation( void )
{
	__asm volatile
	(
		".extern pulRegTest4LoopCounter \n"
		"/* Set all the core registers to known values. */	\n"
		"mov 	r0, #-1				\n"
		"mov 	r1, #1				\n"
		"mov 	r2, #2				\n"
		"mov 	r3, #3				\n"
		"mov	r4, #4				\n"
		"mov	r5, #5				\n"
		"mov	r6, #6				\n"
		"mov 	r7, #7				\n"
		"mov	r8, #8				\n"
		"mov	r9, #9				\n"
		"mov	r10, #10			\n"
		"mov	r11, #11			\n"
		"mov 	r12, #12			\n"

		"/* Set all the VFP to known values. */	 \n"
		"vmov 	d0, r0, r1			\n"
		"vmov 	d1, r2, r3			\n"
		"vmov 	d2, r4, r5			\n"
		"vmov 	d3, r6, r7			\n"
		"vmov 	d4, r8, r9			\n"
		"vmov 	d5, r10, r11		\n"
		"vmov 	d6, r0, r1			\n"
		"vmov 	d7, r2, r3			\n"
		"vmov 	d8, r4, r5			\n"
		"vmov 	d9, r6, r7			\n"
		"vmov 	d10, r8, r9			\n"
		"vmov 	d11, r10, r11		\n"
		"vmov 	d12, r0, r1			\n"
		"vmov 	d13, r2, r3			\n"
		"vmov 	d14, r4, r5			\n"
		"vmov 	d15, r6, r7			\n"

	"reg2_loop:						\n"

		"/* Check all the VFP registers still contain the values set above.		\n"
		"First save registers that are clobbered by the test. */				\n"
		"push { r0-r1 }				\n"

		"vmov	r0, r1, d0			\n"
		"cmp	r0, #-1				\n"
		"bne	reg2_error_loopf	\n"
		"cmp	r1, #1				\n"
		"bne	reg2_error_loopf	\n"
		"vmov	r0, r1, d1			\n"
		"cmp 	r0, #2				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #3				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d2			\n"
		"cmp 	r0, #4				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #5				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d3			\n"
		"cmp 	r0, #6				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #7				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d4			\n"
		"cmp 	r0, #8				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #9				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d5			\n"
		"cmp 	r0, #10				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #11				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d6			\n"
		"cmp 	r0, #-1				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #1				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d7			\n"
		"cmp 	r0, #2				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #3				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d8			\n"
		"cmp 	r0, #4				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #5				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d9			\n"
		"cmp 	r0, #6				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #7				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d10			\n"
		"cmp 	r0, #8				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #9				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d11			\n"
		"cmp 	r0, #10				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #11				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d12			\n"
		"cmp 	r0, #-1				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #1				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d13			\n"
		"cmp 	r0, #2				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #3				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d14			\n"
		"cmp 	r0, #4				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #5				\n"
		"bne 	reg2_error_loopf	\n"
		"vmov 	r0, r1, d15			\n"
		"cmp 	r0, #6				\n"
		"bne 	reg2_error_loopf	\n"
		"cmp 	r1, #7				\n"
		"bne 	reg2_error_loopf	\n"

		"/* Restore the registers that were clobbered by the test. */		\n"
		"pop 	{r0-r1}				\n"

		"/* VFP register test passed.  Jump to the core register test. */		\n"
		"b 		reg2_loopf_pass		\n"

	"reg2_error_loopf:				\n"
		"/* If this line is hit then a VFP register value was found to be		\n"
		"incorrect. */				\n"
		"b reg2_error_loopf			\n"

	"reg2_loopf_pass:				\n"

		"cmp	r0, #-1				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r1, #1				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r2, #2				\n"
		"bne	reg2_error_loop		\n"
		"cmp 	r3, #3				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r4, #4				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r5, #5				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r6, #6				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r7, #7				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r8, #8				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r9, #9				\n"
		"bne	reg2_error_loop		\n"
		"cmp	r10, #10			\n"
		"bne	reg2_error_loop		\n"
		"cmp	r11, #11			\n"
		"bne	reg2_error_loop		\n"
		"cmp	r12, #12			\n"
		"bne	reg2_error_loop		\n"

		"/* Increment the loop counter so the check task knows this task is \n"
		"still running. */			\n"
		"push	{ r0-r1 }			\n"
		"ldr	r0, =pulRegTest4LoopCounter	\n"
		"ldr	r0, [r0]			\n"
		"ldr 	r1, [r0]			\n"
		"adds 	r1, r1, #1			\n"
		"str 	r1, [r0]			\n"
		"pop { r0-r1 }				\n"

		"/* Yield to increase test coverage. */			\n"
		"SVC #1						\n"

		"/* Start again. */			\n"
		"b reg2_loop				\n"

	"reg2_error_loop:				\n"
		"/* If this line is hit then there was an error in a core register value.	\n"
		"This loop ensures the loop counter variable stops incrementing. */			\n"
		"b reg2_error_loop			\n"
	); /* __asm volatile */
}
/*-----------------------------------------------------------*/

/* Fault handlers are here for convenience as they use compiler specific syntax
and this file is specific to the GCC compiler. */
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

	( void ) stacked_psr;
	( void ) stacked_pc;
	( void ) stacked_lr;
	( void ) stacked_r12;
    ( void ) stacked_r0;
    ( void ) stacked_r1;
    ( void ) stacked_r2;
    ( void ) stacked_r3;
}
/*-----------------------------------------------------------*/

void HardFault_Handler( void ) __attribute__((naked));
void HardFault_Handler( void )
{
	__asm volatile
	(
		" tst lr, #4										\n"
		" ite eq											\n"
		" mrseq r0, msp										\n"
		" mrsne r0, psp										\n"
		" ldr r1, [r0, #24]									\n"
		" ldr r2, handler_address_const						\n"
		" bx r2												\n"
		" handler_address_const: .word hard_fault_handler	\n"
	);
}
/*-----------------------------------------------------------*/

void MemManage_Handler( void ) __attribute__((naked));
void MemManage_Handler( void )
{
	__asm volatile
	(
		" tst lr, #4										\n"
		" ite eq											\n"
		" mrseq r0, msp										\n"
		" mrsne r0, psp										\n"
		" ldr r1, [r0, #24]									\n"
		" ldr r2, handler2_address_const					\n"
		" bx r2												\n"
		" handler2_address_const: .word hard_fault_handler	\n"
	);
}/*-----------------------------------------------------------*/

