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


/*
 * The register test task as described in the comments at the top of main-full.c.
 */
.global vRegTest1Implementation
.global vRegTest2Implementation

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check timer inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled or
detected an error. */
.extern ulRegTest1LoopCounter
.extern ulRegTest2LoopCounter

/*-----------------------------------------------------------*/

.section .text
.align 2
vRegTest1Implementation:
	/* First fill the relevant registers with known values.  r0 is always 0, r1
	is the stack pointer, and r3 is a read only small data area pointer. */
	addi r3, r0, 3
	addi r4, r0, 4
	addi r5, r0, 5
	addi r6, r0, 6
	addi r7, r0, 7
	addi r8, r0, 8
	addi r9, r0, 9
	addi r10, r0, 10
	addi r11, r0, 11
	addi r12, r0, 12
	/* R13 = read write small data area anchour. */
	/* R14 = return address for interrupt. */
	/* R15 = return address for sub-routine. */
	/* R16 = return address for trap. */
	/* R17 = return address for exceptions. */
	/* R18 = reserved for assembler and compiler temporaries. */
	addi r19, r0, 19
	addi r20, r0, 20
	addi r21, r0, 21
	addi r22, r0, 22
	addi r23, r0, 23
	addi r24, r0, 24
	addi r25, r0, 25
	addi r26, r0, 26
	addi r27, r0, 27
	addi r28, r0, 28
	addi r29, r0, 29
	addi r30, r0, 30
	addi r31, r0, 31

	/* Now test the register values to ensure they contain the same value that
	was written to them above.	 This task will get preempted frequently so
	other tasks are likely to have executed since the register values were
	written.  If any register contains an unexpected value then the task will
	branch to Error_Loop_1, which in turn prevents it from incrementing its
	loop counter, enabling the check timer to determine that all is not as it
	should be. */

Loop_Start_1:
	xori r18, r3, 3
	bnei r18, Error_Loop_1
	xori r18, r4, 4
	bnei r18, Error_Loop_1
	xori r18, r6, 6
	bnei r18, Error_Loop_1
	xori r18, r7, 7
	bnei r18, Error_Loop_1
	xori r18, r8, 8
	bnei r18, Error_Loop_1
	xori r18, r9, 9
	bnei r18, Error_Loop_1
	xori r18, r10, 10
	bnei r18, Error_Loop_1
	xori r18, r11, 11
	bnei r18, Error_Loop_1
	xori r18, r12, 12
	bnei r18, Error_Loop_1
	xori r18, r19, 19
	bnei r18, Error_Loop_1
	xori r18, r20, 20
	bnei r18, Error_Loop_1
	xori r18, r21, 21
	bnei r18, Error_Loop_1
	xori r18, r22, 22
	bnei r18, Error_Loop_1
	xori r18, r23, 23
	bnei r18, Error_Loop_1
	xori r18, r24, 24
	bnei r18, Error_Loop_1
	xori r18, r25, 25
	bnei r18, Error_Loop_1
	xori r18, r26, 26
	bnei r18, Error_Loop_1
	xori r18, r27, 27
	bnei r18, Error_Loop_1
	xori r18, r28, 28
	bnei r18, Error_Loop_1
	xori r18, r29, 29
	bnei r18, Error_Loop_1
	xori r18, r30, 30
	bnei r18, Error_Loop_1
	xori r18, r31, 31
	bnei r18, Error_Loop_1

	/* If this task has not branched to the error loop, then everything is ok,
	and the check variable can be incremented to indicate that this task
	is still running.  Then, brach back to the top to check the register
	contents again. */
	lwi r18, r0, ulRegTest1LoopCounter
	addik r18, r18, 1
	swi r18, r0, ulRegTest1LoopCounter

	bri Loop_Start_1

	/* The test function will branch here if it discovers an error.  This part
	of the code just sits in a NULL loop, which prevents the check variable
	incrementing any further to allow the check timer to recognize that this
	test has failed. */
Error_Loop_1:
	bri 0
	nop

/*-----------------------------------------------------------*/

.section .text
.align 2
vRegTest2Implementation:
	/* First fill the relevant registers with known values.  r0 is always 0, r1
	is the stack pointer, and r3 is a read only small data area pointer. */
	addi r3, r0, 30000
	addi r4, r0, 40000
	addi r5, r0, 50000
	addi r6, r0, 60000
	addi r7, r0, 70000
	addi r8, r0, 80000
	addi r9, r0, 90000
	addi r10, r0, 100000
	addi r11, r0, 110000
	addi r12, r0, 120000
	/* R13 = read write small data area anchour. */
	/* R14 = return address for interrupt. */
	/* R15 = return address for sub-routine. */
	/* R16 = return address for trap. */
	/* R17 = return address for exceptions. */
	/* R18 = reserved for assembler and compiler temporaries. */
	addi r19, r0, 190000
	addi r20, r0, 200000
	addi r21, r0, 210000
	addi r22, r0, 220000
	addi r23, r0, 230000
	addi r24, r0, 240000
	addi r25, r0, 250000
	addi r26, r0, 260000
	addi r27, r0, 270000
	addi r28, r0, 280000
	addi r29, r0, 290000
	addi r30, r0, 300000
	addi r31, r0, 310000

	/* Now test the register values to ensure they contain the same value that
	was written to them above.	 This task will get preempted frequently so
	other tasks are likely to have executed since the register values were
	written.  If any register contains an unexpected value then the task will
	branch to Error_Loop_2, which in turn prevents it from incrementing its
	loop counter, enabling the check timer to determine that all is not as it
	should be. */

Loop_Start_2:
	xori r18, r3, 30000
	bnei r18, Error_Loop_2
	xori r18, r4, 40000
	bnei r18, Error_Loop_2
	xori r18, r6, 60000
	bnei r18, Error_Loop_2
	xori r18, r7, 70000
	bnei r18, Error_Loop_2
	xori r18, r8, 80000
	bnei r18, Error_Loop_2
	xori r18, r9, 90000
	bnei r18, Error_Loop_2
	xori r18, r10, 100000
	bnei r18, Error_Loop_2
	xori r18, r11, 110000
	bnei r18, Error_Loop_2
	xori r18, r12, 120000
	bnei r18, Error_Loop_2
	xori r18, r19, 190000
	bnei r18, Error_Loop_2
	xori r18, r20, 200000
	bnei r18, Error_Loop_2
	xori r18, r21, 210000
	bnei r18, Error_Loop_2
	xori r18, r22, 220000
	bnei r18, Error_Loop_2
	xori r18, r23, 230000
	bnei r18, Error_Loop_2
	xori r18, r24, 240000
	bnei r18, Error_Loop_2
	xori r18, r25, 250000
	bnei r18, Error_Loop_2
	xori r18, r26, 260000
	bnei r18, Error_Loop_2
	xori r18, r27, 270000
	bnei r18, Error_Loop_2
	xori r18, r28, 280000
	bnei r18, Error_Loop_2
	xori r18, r29, 290000
	bnei r18, Error_Loop_2
	xori r18, r30, 300000
	bnei r18, Error_Loop_2
	xori r18, r31, 310000
	bnei r18, Error_Loop_2

	/* If this task has not branched to the error loop, then everything is ok,
	and the check variable can be incremented to indicate that this task
	is still running.  Then, brach back to the top to check the register
	contents again. */
	lwi r18, r0, ulRegTest2LoopCounter
	addik r18, r18, 1
	swi r18, r0, ulRegTest2LoopCounter

	bri Loop_Start_2

	/* The test function will branch here if it discovers an error.  This part
	of the code just sits in a NULL loop, which prevents the check variable
	incrementing any further to allow the check timer to recognize that this
	test has failed. */
Error_Loop_2:
	bri 0
	nop

