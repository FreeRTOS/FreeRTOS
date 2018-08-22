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

	PUBLIC _vRegTest1Implementation
	PUBLIC _vRegTest2Implementation

	EXTERN _ulRegTest1CycleCount
	EXTERN _ulRegTest2CycleCount

	RSEG CODE:CODE(4)

_vRegTest1Implementation:

		/* Set each register to a known value. */
		MOV.L	#0x33333333, R15
		MVTACHI	R15
		MOV.L	#0x44444444, R15
		MVTACLO	R15
		MOV.L	#1, R1
		MOV.L	#2, R2
		MOV.L	#3, R3
		MOV.L	#4, R4
		MOV.L	#5, R5
		MOV.L	#6, R6
		MOV.L	#7, R7
		MOV.L	#8, R8
		MOV.L	#9, R9
		MOV.L	#10, R10
		MOV.L	#11, R11
		MOV.L	#12, R12
		MOV.L	#13, R13
		MOV.L	#14, R14
		MOV.L	#15, R15

	/* Loop, checking each iteration that each register still contains the
	expected value. */
	TestLoop1:

		/* Push the registers that are going to get clobbered. */
		PUSHM	R14-R15

		/* Increment the loop counter to show this task is still getting CPU
		time. */
		MOV.L	#_ulRegTest1CycleCount, R14
		MOV.L	[ R14 ], R15
		ADD		#1, R15
		MOV.L	R15, [ R14 ]

		/* Yield to extend the text coverage.  Set the bit in the ITU SWINTR
		register. */
		MOV.L	#1, R14
		MOV.L 	#0872E0H, R15
		MOV.B	R14, [R15]
		NOP
		NOP

		/* Check the accumulator value. */
		MVFACHI	R15
		CMP		#0x33333333, R15
		BNE		RegTest2Error
		MVFACMI	R15
		CMP		#0x33334444, R15
		BNE		RegTest2Error

		/* Restore the clobbered registers. */
		POPM	R14-R15

		/* Now compare each register to ensure it still contains the value that
		was set before this loop was entered. */
		CMP		#1, R1
		BNE		RegTest1Error
		CMP		#2, R2
		BNE		RegTest1Error
		CMP		#3, R3
		BNE		RegTest1Error
		CMP		#4, R4
		BNE		RegTest1Error
		CMP		#5, R5
		BNE		RegTest1Error
		CMP		#6, R6
		BNE		RegTest1Error
		CMP		#7, R7
		BNE		RegTest1Error
		CMP		#8, R8
		BNE		RegTest1Error
		CMP		#9, R9
		BNE		RegTest1Error
		CMP		#10, R10
		BNE		RegTest1Error
		CMP		#11, R11
		BNE		RegTest1Error
		CMP		#12, R12
		BNE		RegTest1Error
		CMP		#13, R13
		BNE		RegTest1Error
		CMP		#14, R14
		BNE		RegTest1Error
		CMP		#15, R15
		BNE		RegTest1Error

		/* All comparisons passed, start a new iteration of this loop. */
		BRA		TestLoop1

	/* A compare failed, just loop here so the loop counter stops
	incrementing causing the check timer to indicate the error. */
	RegTest1Error:
		BRA RegTest1Error

/*-----------------------------------------------------------*/

_vRegTest2Implementation:

		/* Set each register to a known value. */
		MOV.L	#0x11111111, R15
		MVTACHI	R15
		MOV.L	#0x22222222, R15
		MVTACLO	R15
		MOV.L	#100, R1
		MOV.L	#200, R2
		MOV.L	#300, R3
		MOV.L	#400, R4
		MOV.L	#500, R5
		MOV.L	#600, R6
		MOV.L	#700, R7
		MOV.L	#800, R8
		MOV.L	#900, R9
		MOV.L	#1000, R10
		MOV.L	#1001, R11
		MOV.L	#1002, R12
		MOV.L	#1003, R13
		MOV.L	#1004, R14
		MOV.L	#1005, R15

	/* Loop, checking each iteration that each register still contains the
	expected value. */
	TestLoop2:

		/* Push the registers that are going to get clobbered. */
		PUSHM	R14-R15

		/* Increment the loop counter to show this task is still getting CPU
		time. */
		MOV.L	#_ulRegTest2CycleCount, R14
		MOV.L	[ R14 ], R15
		ADD		#1, R15
		MOV.L	R15, [ R14 ]

		/* Check the accumulator value. */
		MVFACHI	R15
		CMP		#0x11111111, R15
		BNE		RegTest2Error
		MVFACMI	R15
		CMP		#0x11112222, R15
		BNE		RegTest2Error

		/* Restore the clobbered registers. */
		POPM	R14-R15

		/* Now compare each register to ensure it still contains the value that
		was set before this loop was entered. */
		CMP		#100, R1
		BNE		RegTest2Error
		CMP		#200, R2
		BNE		RegTest2Error
		CMP		#300, R3
		BNE		RegTest2Error
		CMP		#400, R4
		BNE		RegTest2Error
		CMP		#500, R5
		BNE		RegTest2Error
		CMP		#600, R6
		BNE		RegTest2Error
		CMP		#700, R7
		BNE		RegTest2Error
		CMP		#800, R8
		BNE		RegTest2Error
		CMP		#900, R9
		BNE		RegTest2Error
		CMP		#1000, R10
		BNE		RegTest2Error
		CMP		#1001, R11
		BNE		RegTest2Error
		CMP		#1002, R12
		BNE		RegTest2Error
		CMP		#1003, R13
		BNE		RegTest2Error
		CMP		#1004, R14
		BNE		RegTest2Error
		CMP		#1005, R15
		BNE		RegTest2Error

		/* All comparisons passed, start a new iteration of this loop. */
		BRA		TestLoop2

	/* A compare failed, just loop here so the loop counter stops
	incrementing causing the check timer to indicate the error. */
	RegTest2Error:
		BRA RegTest2Error

/*-----------------------------------------------------------*/

		END

