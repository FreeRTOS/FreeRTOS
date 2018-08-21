/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * This file defines the RegTest tasks as described at the top of main.c
 */

	.global	_vRegTest1Task
	.short  _vRegTest1Task
	.global	_vRegTest2Task
	.short  _vRegTest2Task

	.extern	_vRegTestError
	.extern	_usRegTest1LoopCounter
	.extern	_usRegTest2LoopCounter

	.text
/*
 * Fill all the registers with known values, then check that the registers
 * contain the expected value.  An incorrect value being indicative of an
 * error in the context switch mechanism.
 */
_vRegTest1Task:

	/* First fill the registers. */
	SEL		RB0
	MOVW	AX, #0x1122
	MOVW	BC, #0x3344
	MOVW	DE, #0x5566
	MOVW	HL, #0x7788
	SEL		RB1
	MOVW	AX, #0x1111
	MOVW	BC, #0x2222
	MOVW	DE, #0x3333
	MOVW	HL, #0x4444
	SEL		RB2
	MOVW	AX, #0x5555
	MOVW	BC, #0x6666
	MOVW	DE, #0x7777
	MOVW	HL, #0x8888

	/* Register bank 3 is not used outside of interrupts so is not saved as part
	of the task context. */
	SEL		RB0

_loop1:

	/* Continuously check that the register values remain at their expected
	values.  The BRK is to test the yield.  This task runs at low priority
	so will also regularly get preempted. */
	BRK

	/* Compare with the expected value. */
	CMPW	AX, #0x1122
	BZ		$.+5

	/* Jump over the branch to vRegTestError() if the register contained the
	expected value - otherwise flag an error by executing vRegTestError(). */
	BR		!!_vRegTestError

	/* Repeat for all the registers. */
	MOVW	AX, BC
	CMPW	AX, #0x3344
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0x5566
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0x7788
	BZ		$.+5
	BR		!!_vRegTestError

	/* Set AX back to its initial value. */
	MOVW	AX, #0x1122

	SEL		RB1
	CMPW	AX, #0x1111
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, BC
	CMPW	AX, #0x2222
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0x3333
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0x4444
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, #0x1111


	SEL		RB2
	CMPW	AX, #0x5555
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, BC
	CMPW	AX, #0x6666
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0x7777
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0x8888
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, #0x5555


	/* Register bank 3 is not used outside of interrupts so is not saved as
	part of the task context. */

	SEL 	RB0

	/* Indicate that this task is still cycling. */
	INCW	!_usRegTest1LoopCounter

	BR 		!!_loop1


/*
 * Fill all the registers with known values, then check that the registers
 * contain the expected value.  An incorrect value being indicative of an
 * error in the context switch mechanism.
 */
_vRegTest2Task:

	SEL		RB0
	MOVW	AX, #0x99aa
	MOVW	BC, #0xbbcc
	MOVW	DE, #0xddee
	MOVW	HL, #0xff12
	SEL		RB1
	MOVW	AX, #0x0110
	MOVW	BC, #0x0220
	MOVW	DE, #0x0330
	MOVW	HL, #0x0440
	SEL		RB2
	MOVW	AX, #0x0550
	MOVW	BC, #0x0660
	MOVW	DE, #0x0770
	MOVW	HL, #0x0880

	/* Register bank 3 is not used outside of interrupts so is not saved as
	part of the task context. */
	SEL		RB0

_loop2:
	CMPW	AX, #0x99aa
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, BC
	CMPW	AX, #0xbbcc
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0xddee
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0xff12
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, #0x99aa

	SEL		RB1
	CMPW	AX, #0x0110
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, BC
	CMPW	AX, #0x0220
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0x0330
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0x0440
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, #0x0110

	SEL		RB2
	CMPW	AX, #0x0550
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, BC
	CMPW	AX, #0x0660
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0x0770
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0x0880
	BZ		$.+5
	BR		!!_vRegTestError
	MOVW	AX, #0x0550

	/* Register bank 3 is not used outside of interrupts so is not saved as
	part of the task context. */

	SEL 	RB0

	/* Indicate that this task is still cycling. */
	INCW	!_usRegTest2LoopCounter

	BR 		!!_loop2

	.end

