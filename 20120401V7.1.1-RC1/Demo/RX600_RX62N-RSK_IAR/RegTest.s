/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

	PUBLIC _prvRegTest1Implementation
	PUBLIC _prvRegTest2Implementation
	
	EXTERN _ulRegTest1CycleCount
	EXTERN _ulRegTest2CycleCount

	RSEG CODE:CODE(4)

/* This function is explained in the comments at the top of main.c. */
_prvRegTest1Implementation:

	/* Put a known value in each register. */
	MOV	#1, R1						
	MOV	#2, R2						
	MOV	#3, R3						
	MOV	#4, R4						
	MOV	#5, R5						
	MOV	#6, R6						
	MOV	#7, R7						
	MOV	#8, R8						
	MOV	#9, R9						
	MOV	#10, R10					
	MOV	#11, R11					
	MOV	#12, R12					
	MOV	#13, R13					
	MOV	#14, R14					
	MOV	#15, R15					
	
	/* Loop, checking each itteration that each register still contains the
	expected value. */
TestLoop1:								

	/* Push the registers that are going to get clobbered. */
	PUSHM	R14-R15						
	
	/* Increment the loop counter to show this task is still getting CPU time. */
	MOV	#_ulRegTest1CycleCount, R14	
	MOV	[ R14 ], R15				
	ADD	#1, R15						
	MOV	R15, [ R14 ]				
	
	/* Yield to extend the text coverage.  Set the bit in the ITU SWINTR register. */
	MOV	#1, R14						
	MOV 	#0872E0H, R15				
	MOV.B	R14, [R15]					
	NOP								
	NOP								
	
	/* Restore the clobbered registers. */
	POPM	R14-R15						
	
	/* Now compare each register to ensure it still contains the value that was
	set before this loop was entered. */
	CMP	#1, R1						
	BNE	RegTest1Error				
	CMP	#2, R2						
	BNE	RegTest1Error				
	CMP	#3, R3						
	BNE	RegTest1Error				
	CMP	#4, R4						
	BNE	RegTest1Error				
	CMP	#5, R5						
	BNE	RegTest1Error				
	CMP	#6, R6						
	BNE	RegTest1Error				
	CMP	#7, R7						
	BNE	RegTest1Error				
	CMP	#8, R8						
	BNE	RegTest1Error				
	CMP	#9, R9						
	BNE	RegTest1Error				
	CMP	#10, R10					
	BNE	RegTest1Error				
	CMP	#11, R11					
	BNE	RegTest1Error				
	CMP	#12, R12					
	BNE	RegTest1Error				
	CMP	#13, R13					
	BNE	RegTest1Error				
	CMP	#14, R14					
	BNE	RegTest1Error				
	CMP	#15, R15					
	BNE	RegTest1Error				

	/* All comparisons passed, start a new itteratio of this loop. */
	BRA		TestLoop1				
	
RegTest1Error:							
	/* A compare failed, just loop here so the loop counter stops incrementing
	- causing the check task to indicate the error. */
	BRA RegTest1Error					
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of main.c. */
_prvRegTest2Implementation:

	/* Put a known value in each register. */
	MOV	#10H, R1					
	MOV	#20H, R2					
	MOV	#30H, R3					
	MOV	#40H, R4					
	MOV	#50H, R5					
	MOV	#60H, R6					
	MOV	#70H, R7					
	MOV	#80H, R8					
	MOV	#90H, R9					
	MOV	#100H, R10					
	MOV	#110H, R11					
	MOV	#120H, R12					
	MOV	#130H, R13					
	MOV	#140H, R14					
	MOV	#150H, R15					
	
	/* Loop, checking each itteration that each register still contains the
	expected value. */
TestLoop2:								

	/* Push the registers that are going to get clobbered. */
	PUSHM	R14-R15						
	
	/* Increment the loop counter to show this task is still getting CPU time. */
	MOV	#_ulRegTest2CycleCount, R14	
	MOV	[ R14 ], R15				
	ADD	#1, R15						
	MOV	R15, [ R14 ]				
	
	/* Restore the clobbered registers. */
	POPM	R14-R15						
	
	/* Now compare each register to ensure it still contains the value that was
	set before this loop was entered. */
	CMP	#10H, R1					
	BNE	RegTest2Error				
	CMP	#20H, R2					
	BNE	RegTest2Error				
	CMP	#30H, R3					
	BNE	RegTest2Error				
	CMP	#40H, R4					
	BNE	RegTest2Error				
	CMP	#50H, R5					
	BNE	RegTest2Error				
	CMP	#60H, R6					
	BNE	RegTest2Error				
	CMP	#70H, R7					
	BNE	RegTest2Error				
	CMP	#80H, R8					
	BNE	RegTest2Error				
	CMP	#90H, R9					
	BNE	RegTest2Error				
	CMP	#100H, R10					
	BNE	RegTest2Error				
	CMP	#110H, R11					
	BNE	RegTest2Error				
	CMP	#120H, R12					
	BNE	RegTest2Error				
	CMP	#130H, R13					
	BNE	RegTest2Error				
	CMP	#140H, R14					
	BNE	RegTest2Error				
	CMP	#150H, R15					
	BNE	RegTest2Error				

	/* All comparisons passed, start a new itteratio of this loop. */
	BRA	TestLoop2					
	
RegTest2Error:							
	/* A compare failed, just loop here so the loop counter stops incrementing
	- causing the check task to indicate the error. */
	BRA RegTest2Error					

	
	END
