/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


__asm vRegTest1Task( void )
{
	PRESERVE8
	IMPORT ulRegTest1LoopCounter

	/* Fill the core registers with known values. */
	mov r0, #100
	mov r1, #101
	mov r2, #102
	mov r3, #103
	mov	r4, #104
	mov	r5, #105
	mov	r6, #106
	mov r7, #107
	mov	r8, #108
	mov	r9, #109
	mov	r10, #110
	mov	r11, #111
	mov r12, #112

	/* Fill the VFP registers with known values. */
	vmov d0, r0, r1
	vmov d1, r2, r3
	vmov d2, r4, r5
	vmov d3, r6, r7
	vmov d4, r8, r9
	vmov d5, r10, r11
	vmov d6, r0, r1
	vmov d7, r2, r3
	vmov d8, r4, r5
	vmov d9, r6, r7
	vmov d10, r8, r9
	vmov d11, r10, r11
	vmov d12, r0, r1
	vmov d13, r2, r3
	vmov d14, r4, r5
	vmov d15, r6, r7

reg1_loop
	/* Check all the VFP registers still contain the values set above.
	First save registers that are clobbered by the test. */
	push { r0-r1 }
	
	vmov r0, r1, d0
	cmp r0, #100
	bne reg1_error_loopf
	cmp r1, #101
	bne reg1_error_loopf
	vmov r0, r1, d1
	cmp r0, #102
	bne reg1_error_loopf
	cmp r1, #103
	bne reg1_error_loopf
	vmov r0, r1, d2
	cmp r0, #104
	bne reg1_error_loopf
	cmp r1, #105
	bne reg1_error_loopf
	vmov r0, r1, d3
	cmp r0, #106
	bne reg1_error_loopf
	cmp r1, #107
	bne reg1_error_loopf
	vmov r0, r1, d4
	cmp r0, #108
	bne reg1_error_loopf
	cmp r1, #109
	bne reg1_error_loopf
	vmov r0, r1, d5
	cmp r0, #110
	bne reg1_error_loopf
	cmp r1, #111
	bne reg1_error_loopf
	vmov r0, r1, d6
	cmp r0, #100
	bne reg1_error_loopf
	cmp r1, #101
	bne reg1_error_loopf
	vmov r0, r1, d7
	cmp r0, #102
	bne reg1_error_loopf
	cmp r1, #103
	bne reg1_error_loopf
	vmov r0, r1, d8
	cmp r0, #104
	bne reg1_error_loopf
	cmp r1, #105
	bne reg1_error_loopf
	vmov r0, r1, d9
	cmp r0, #106
	bne reg1_error_loopf
	cmp r1, #107
	bne reg1_error_loopf
	vmov r0, r1, d10
	cmp r0, #108
	bne reg1_error_loopf
	cmp r1, #109
	bne reg1_error_loopf
	vmov r0, r1, d11
	cmp r0, #110
	bne reg1_error_loopf
	cmp r1, #111
	bne reg1_error_loopf
	vmov r0, r1, d12
	cmp r0, #100
	bne reg1_error_loopf
	cmp r1, #101
	bne reg1_error_loopf
	vmov r0, r1, d13
	cmp r0, #102
	bne reg1_error_loopf
	cmp r1, #103
	bne reg1_error_loopf
	vmov r0, r1, d14
	cmp r0, #104
	bne reg1_error_loopf
	cmp r1, #105
	bne reg1_error_loopf
	vmov r0, r1, d15
	cmp r0, #106
	bne reg1_error_loopf
	cmp r1, #107
	bne reg1_error_loopf
	
	/* Restore the registers that were clobbered by the test. */
	pop {r0-r1}
	
	/* VFP register test passed.  Jump to the core register test. */
	b reg1_loopf_pass

reg1_error_loopf
	/* If this line is hit then a VFP register value was found to be
	incorrect. */
	b reg1_error_loopf

reg1_loopf_pass

	cmp	r0, #100
	bne	reg1_error_loop
	cmp	r1, #101
	bne	reg1_error_loop
	cmp	r2, #102
	bne	reg1_error_loop
	cmp r3, #103
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
	push { r0-r1 }
	ldr	r0, =ulRegTest1LoopCounter
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]
	pop { r0-r1 }
	
	/* Start again. */
	b reg1_loop

reg1_error_loop
	/* If this line is hit then there was an error in a core register value.
	The loop ensures the loop counter stops incrementing. */
	b reg1_error_loop
	nop
}
/*-----------------------------------------------------------*/

__asm vRegTest2Task( void )
{
	PRESERVE8
	IMPORT ulRegTest2LoopCounter

	/* Set all the core registers to known values. */
	mov r0, #-1
	mov r1, #1
	mov r2, #2
	mov r3, #3
	mov	r4, #4
	mov	r5, #5
	mov	r6, #6
	mov r7, #7
	mov	r8, #8
	mov	r9, #9
	mov	r10, #10
	mov	r11, #11
	mov r12, #12

	/* Set all the VFP to known values. */
	vmov d0, r0, r1
	vmov d1, r2, r3
	vmov d2, r4, r5
	vmov d3, r6, r7
	vmov d4, r8, r9
	vmov d5, r10, r11
	vmov d6, r0, r1
	vmov d7, r2, r3
	vmov d8, r4, r5
	vmov d9, r6, r7
	vmov d10, r8, r9
	vmov d11, r10, r11
	vmov d12, r0, r1
	vmov d13, r2, r3
	vmov d14, r4, r5
	vmov d15, r6, r7

reg2_loop
	
	/* Check all the VFP registers still contain the values set above.
	First save registers that are clobbered by the test. */
	push { r0-r1 }
	
	vmov r0, r1, d0
	cmp r0, #-1
	bne reg2_error_loopf
	cmp r1, #1
	bne reg2_error_loopf
	vmov r0, r1, d1
	cmp r0, #2
	bne reg2_error_loopf
	cmp r1, #3
	bne reg2_error_loopf
	vmov r0, r1, d2
	cmp r0, #4
	bne reg2_error_loopf
	cmp r1, #5
	bne reg2_error_loopf
	vmov r0, r1, d3
	cmp r0, #6
	bne reg2_error_loopf
	cmp r1, #7
	bne reg2_error_loopf
	vmov r0, r1, d4
	cmp r0, #8
	bne reg2_error_loopf
	cmp r1, #9
	bne reg2_error_loopf
	vmov r0, r1, d5
	cmp r0, #10
	bne reg2_error_loopf
	cmp r1, #11
	bne reg2_error_loopf
	vmov r0, r1, d6
	cmp r0, #-1
	bne reg2_error_loopf
	cmp r1, #1
	bne reg2_error_loopf
	vmov r0, r1, d7
	cmp r0, #2
	bne reg2_error_loopf
	cmp r1, #3
	bne reg2_error_loopf
	vmov r0, r1, d8
	cmp r0, #4
	bne reg2_error_loopf
	cmp r1, #5
	bne reg2_error_loopf
	vmov r0, r1, d9
	cmp r0, #6
	bne reg2_error_loopf
	cmp r1, #7
	bne reg2_error_loopf
	vmov r0, r1, d10
	cmp r0, #8
	bne reg2_error_loopf
	cmp r1, #9
	bne reg2_error_loopf
	vmov r0, r1, d11
	cmp r0, #10
	bne reg2_error_loopf
	cmp r1, #11
	bne reg2_error_loopf
	vmov r0, r1, d12
	cmp r0, #-1
	bne reg2_error_loopf
	cmp r1, #1
	bne reg2_error_loopf
	vmov r0, r1, d13
	cmp r0, #2
	bne reg2_error_loopf
	cmp r1, #3
	bne reg2_error_loopf
	vmov r0, r1, d14
	cmp r0, #4
	bne reg2_error_loopf
	cmp r1, #5
	bne reg2_error_loopf
	vmov r0, r1, d15
	cmp r0, #6
	bne reg2_error_loopf
	cmp r1, #7
	bne reg2_error_loopf
	
	/* Restore the registers that were clobbered by the test. */
	pop {r0-r1}
	
	/* VFP register test passed.  Jump to the core register test. */
	b reg2_loopf_pass

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
	cmp r3, #3
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
	
	/* Increment the loop counter to indicate this test is still functioning
	correctly. */
	push { r0-r1 }
	ldr	r0, =ulRegTest2LoopCounter
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]
	
	/* Yield to increase test coverage. */
	movs r0, #0x01
	ldr r1, =0xe000ed04 /*NVIC_INT_CTRL */
	lsl r0, r0, #28 /* Shift to PendSV bit */
	str r0, [r1]
	dsb
	
	pop { r0-r1 }
	
	/* Start again. */
	b reg2_loop

reg2_error_loop
	/* If this line is hit then there was an error in a core register value.
	This loop ensures the loop counter variable stops incrementing. */
	b reg2_error_loop
}
/*-----------------------------------------------------------*/

__asm vRegTestClearFlopRegistersToParameterValue( unsigned long ulValue	)
{
	PRESERVE8

	/* Clobber the auto saved registers. */
	vmov d0, r0, r0
	vmov d1, r0, r0
	vmov d2, r0, r0
	vmov d3, r0, r0
	vmov d4, r0, r0
	vmov d5, r0, r0
	vmov d6, r0, r0
	vmov d7, r0, r0
	bx lr
}
/*-----------------------------------------------------------*/

__asm ulRegTestCheckFlopRegistersContainParameterValue( unsigned long ulValue )
{
	PRESERVE8

	vmov r1, s0
	cmp r0, r1
	bne return_error
	vmov r1, s1
	cmp r0, r1
	bne return_error
	vmov r1, s2
	cmp r0, r1
	bne return_error
	vmov r1, s3
	cmp r0, r1
	bne return_error
	vmov r1, s4
	cmp r0, r1
	bne return_error
	vmov r1, s5
	cmp r0, r1
	bne return_error
	vmov r1, s6
	cmp r0, r1
	bne return_error
	vmov r1, s7
	cmp r0, r1
	bne return_error
	vmov r1, s8
	cmp r0, r1
	bne return_error
	vmov r1, s9
	cmp r0, r1
	bne return_error
	vmov r1, s10
	cmp r0, r1
	bne return_error
	vmov r1, s11
	cmp r0, r1
	bne return_error
	vmov r1, s12
	cmp r0, r1
	bne return_error
	vmov r1, s13
	cmp r0, r1
	bne return_error
	vmov r1, s14
	cmp r0, r1
	bne return_error
	vmov r1, s15
	cmp r0, r1
	bne return_error
	
return_pass
	mov r0, #1
	bx lr

return_error
	mov r0, #0
	bx lr
}

	
