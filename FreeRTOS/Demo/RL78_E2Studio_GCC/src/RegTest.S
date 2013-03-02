/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems, who sell the code with commercial support,
    indemnification and middleware, under the OpenRTOS brand.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.
*/

/*
 * This file defines the RegTest tasks as described at the top of main.c
 */


	.global	vRegTest1
	.global	vRegTest2

	.extern	_vRegTestError
	.extern	_usRegTest1LoopCounter
	.extern	_usRegTest2LoopCounter

	.text
/*
 * Fill all the registers with known values, then check that the registers
 * contain the expected value.  An incorrect value being indicative of an
 * error in the context switch mechanism.
 */
vRegTest1:

	/* First fill the registers. */
	MOVW	AX, #0x1122
	MOVW	BC, #0x3344
	MOVW	DE, #0x5566
	MOVW	HL, #0x7788
	MOV		CS, #0x01

#if __DATA_MODEL__ == __DATA_MODEL_FAR__

	; ES is not saved or restored when using the near memory model so only
	; test it when using the far model.
	MOV		ES, #0x02

#endif

_loop1:

	/* Continuously check that the register values remain at their expected
	values.  The BRK is to test the yield.  This task runs at low priority
	so will also regularly get preempted. */
	BRK

	/* Compare with the expected value. */
	CMPW	AX, #0x1122
	BZ		$5

	/* Jump over the branch to vRegTestError() if the register contained the
	expected value - otherwise flag an error by executing vRegTestError(). */
	BR		!_vRegTestError

	/* Repeat for all the registers. */
	MOVW	AX, BC
	CMPW	AX, #0x3344
	BZ		$5
	BR		!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0x5566
	BZ		$5
	BR		!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0x7788
	BZ		$5
	BR		!_vRegTestError
	MOV		A, CS
	CMP		A, #0x01
	BZ		$5
	BR		!_vRegTestError

#if __DATA_MODEL__ == __DATA_MODEL_FAR__

	/* ES is not saved or restored when using the near memory model so only
	test it when using the far model. */
	MOV		A, ES
	CMP		A, #0x02
	BZ		$5
	BR		!_vRegTestError

#endif

	/* Indicate that this task is still cycling. */
	INCW	!_usRegTest1LoopCounter

	MOVW	AX, #0x1122
	BR 		!_loop1


/*
 * Fill all the registers with known values, then check that the registers
 * contain the expected value.  An incorrect value being indicative of an
 * error in the context switch mechanism.
 */
vRegTest2:

	MOVW	AX, #0x99aa
	MOVW	BC, #0xbbcc
	MOVW	DE, #0xddee
	MOVW	HL, #0xff12
	MOV		CS, #0x03

#if __DATA_MODEL__ == __DATA_MODEL_FAR__

	MOV		ES, #0x04

#endif

_loop2:
	CMPW	AX, #0x99aa
	BZ		$5
	BR		!_vRegTestError
	MOVW	AX, BC
	CMPW	AX, #0xbbcc
	BZ		$5
	BR		!_vRegTestError
	MOVW	AX, DE
	CMPW	AX, #0xddee
	BZ		$5
	BR		!_vRegTestError
	MOVW	AX, HL
	CMPW	AX, #0xff12
	BZ		$5
	BR		!_vRegTestError
	MOV		A, CS
	CMP		A, #0x03
	BZ		$5
	BR		!_vRegTestError

#if __DATA_MODEL__ == __DATA_MODEL_FAR__

	MOV		A, ES
	CMP		A, #0x04
	BZ		$5
	BR		!_vRegTestError

#endif

	/* Indicate that this task is still cycling. */
	INCW	!_usRegTest2LoopCounter

	MOVW	AX, #0x99aa
	BR 		!_loop2


	.end

