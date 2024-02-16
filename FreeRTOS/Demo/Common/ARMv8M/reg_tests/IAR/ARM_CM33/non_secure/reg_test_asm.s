/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 * "Reg tests" - These tests fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 */

    SECTION .text:CODE:NOROOT(2)
    THUMB

    EXTERN ulRegTest1LoopCounter
    EXTERN ulRegTest2LoopCounter
    EXTERN ulRegTest3LoopCounter
    EXTERN ulRegTest4LoopCounter

    PUBLIC vRegTest1Asm_NonSecure
    PUBLIC vRegTest2Asm_NonSecure
    PUBLIC vRegTest3Asm_NonSecure
    PUBLIC vRegTest4Asm_NonSecure
    PUBLIC vRegTestAsm_NonSecureCallback

/*-----------------------------------------------------------*/

vRegTest1Asm_NonSecure:
    /* Fill the core registers with known values. */
    movs r0,  #100
    movs r1,  #101
    movs r2,  #102
    movs r3,  #103
    movs r4,  #104
    movs r5,  #105
    movs r6,  #106
    movs r7,  #107
    mov  r8,  #108
    mov  r9,  #109
    mov  r10, #110
    mov  r11, #111
    mov  r12, #112

    /* Fill the FPU registers with known values. */
    vmov.f32 s1,  #1.5
    vmov.f32 s2,  #2.5
    vmov.f32 s3,  #3.5
    vmov.f32 s4,  #4.5
    vmov.f32 s5,  #5.5
    vmov.f32 s6,  #6.5
    vmov.f32 s7,  #7.5
    vmov.f32 s8,  #8.5
    vmov.f32 s9,  #9.5
    vmov.f32 s10, #10.5
    vmov.f32 s11, #11.5
    vmov.f32 s12, #12.5
    vmov.f32 s13, #13.5
    vmov.f32 s14, #14.5
    vmov.f32 s15, #1.0
    vmov.f32 s16, #2.0
    vmov.f32 s17, #3.0
    vmov.f32 s18, #4.0
    vmov.f32 s19, #5.0
    vmov.f32 s20, #6.0
    vmov.f32 s21, #7.0
    vmov.f32 s22, #8.0
    vmov.f32 s23, #9.0
    vmov.f32 s24, #10.0
    vmov.f32 s25, #11.0
    vmov.f32 s26, #12.0
    vmov.f32 s27, #13.0
    vmov.f32 s28, #14.0
    vmov.f32 s29, #1.5
    vmov.f32 s30, #2.5
    vmov.f32 s31, #3.5

    reg1_loop:
        /* Verify that core registers contain correct values. */
        cmp r0, #100
        bne reg1_error_loop
        cmp r1, #101
        bne reg1_error_loop
        cmp r2, #102
        bne reg1_error_loop
        cmp r3, #103
        bne reg1_error_loop
        cmp r4, #104
        bne reg1_error_loop
        cmp r5, #105
        bne reg1_error_loop
        cmp r6, #106
        bne reg1_error_loop
        cmp r7, #107
        bne reg1_error_loop
        cmp r8, #108
        bne reg1_error_loop
        cmp r9, #109
        bne reg1_error_loop
        cmp r10, #110
        bne reg1_error_loop
        cmp r11, #111
        bne reg1_error_loop
        cmp r12, #112
        bne reg1_error_loop

        /* Verify that FPU registers contain correct values. */
        vmov.f32 s0, #1.5           /* s0 = 1.5. */
        vcmp.f32 s1, s0             /* Compare s0 and s1. */
        vmrs     APSR_nzcv, FPSCR   /* Copy floating point flags (FPSCR flags) to ASPR flags - needed for next bne to work. */
        bne      reg1_error_loop
        vmov.f32 s0, #2.5
        vcmp.f32 s2, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #3.5
        vcmp.f32 s3, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #4.5
        vcmp.f32 s4, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #5.5
        vcmp.f32 s5, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #6.5
        vcmp.f32 s6, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #7.5
        vcmp.f32 s7, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #8.5
        vcmp.f32 s8, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #9.5
        vcmp.f32 s9, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #10.5
        vcmp.f32 s10, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #11.5
        vcmp.f32 s11, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #12.5
        vcmp.f32 s12, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #13.5
        vcmp.f32 s13, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #14.5
        vcmp.f32 s14, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #1.0
        vcmp.f32 s15, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #2.0
        vcmp.f32 s16, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #3.0
        vcmp.f32 s17, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #4.0
        vcmp.f32 s18, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #5.0
        vcmp.f32 s19, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #6.0
        vcmp.f32 s20, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #7.0
        vcmp.f32 s21, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #8.0
        vcmp.f32 s22, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #9.0
        vcmp.f32 s23, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #10.0
        vcmp.f32 s24, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #11.0
        vcmp.f32 s25, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #12.0
        vcmp.f32 s26, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #13.0
        vcmp.f32 s27, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #14.0
        vcmp.f32 s28, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #1.5
        vcmp.f32 s29, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #2.5
        vcmp.f32 s30, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop
        vmov.f32 s0, #3.5
        vcmp.f32 s31, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg1_error_loop

        /* Everything passed, inc the loop counter. */
        push { r0, r1 }
        ldr  r0, =ulRegTest1LoopCounter
        ldr  r1, [r0]
        adds r1, r1, #1
        str  r1, [r0]

        /* Yield to increase test coverage. */
        movs r0, #0x01
        ldr  r1, =0xe000ed04    /* NVIC_ICSR. */
        lsls r0, #28            /* Shift to PendSV bit. */
        str  r0, [r1]
        dsb
        pop  { r0, r1 }

        /* Start again. */
        b reg1_loop

    reg1_error_loop:
        /* If this line is hit then there was an error in
         * a core register value. The loop ensures the
         * loop counter stops incrementing. */
        b reg1_error_loop
        nop
        ltorg
/*-----------------------------------------------------------*/

vRegTest2Asm_NonSecure:
    /* Fill the core registers with known values. */
    movs r0, #0
    movs r1, #1
    movs r2, #2
    movs r3, #3
    movs r4, #4
    movs r5, #5
    movs r6, #6
    movs r7, #7
    mov  r8, #8
    mov  r9, #9
    movs r10, #10
    movs r11, #11
    movs r12, #12

    /* Fill the FPU registers with known values. */
    vmov.f32 s1,  #1.0
    vmov.f32 s2,  #2.0
    vmov.f32 s3,  #3.0
    vmov.f32 s4,  #4.0
    vmov.f32 s5,  #5.0
    vmov.f32 s6,  #6.0
    vmov.f32 s7,  #7.0
    vmov.f32 s8,  #8.0
    vmov.f32 s9,  #9.0
    vmov.f32 s10, #10.0
    vmov.f32 s11, #11.0
    vmov.f32 s12, #12.0
    vmov.f32 s13, #13.0
    vmov.f32 s14, #14.0
    vmov.f32 s15, #1.5
    vmov.f32 s16, #2.5
    vmov.f32 s17, #3.5
    vmov.f32 s18, #4.5
    vmov.f32 s19, #5.5
    vmov.f32 s20, #6.5
    vmov.f32 s21, #7.5
    vmov.f32 s22, #8.5
    vmov.f32 s23, #9.5
    vmov.f32 s24, #10.5
    vmov.f32 s25, #11.5
    vmov.f32 s26, #12.5
    vmov.f32 s27, #13.5
    vmov.f32 s28, #14.5
    vmov.f32 s29, #1.0
    vmov.f32 s30, #2.0
    vmov.f32 s31, #3.0

    reg2_loop:
        /* Verify that core registers contain correct values. */
        cmp  r0, #0
        bne  reg2_error_loop
        cmp  r1, #1
        bne  reg2_error_loop
        cmp  r2, #2
        bne  reg2_error_loop
        cmp  r3, #3
        bne  reg2_error_loop
        cmp  r4, #4
        bne  reg2_error_loop
        cmp  r5, #5
        bne  reg2_error_loop
        cmp  r6, #6
        bne  reg2_error_loop
        cmp  r7, #7
        bne  reg2_error_loop
        cmp  r8, #8
        bne  reg2_error_loop
        cmp  r9, #9
        bne  reg2_error_loop
        cmp  r10, #10
        bne  reg2_error_loop
        cmp  r11, #11
        bne  reg2_error_loop
        cmp  r12, #12
        bne  reg2_error_loop

        /* Verify that FPU registers contain correct values. */
        vmov.f32 s0, #1.0
        vcmp.f32 s1, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #2.0
        vcmp.f32 s2, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #3.0
        vcmp.f32 s3, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #4.0
        vcmp.f32 s4, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #5.0
        vcmp.f32 s5, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #6.0
        vcmp.f32 s6, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #7.0
        vcmp.f32 s7, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #8.0
        vcmp.f32 s8, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #9.0
        vcmp.f32 s9, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #10.0
        vcmp.f32 s10, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #11.0
        vcmp.f32 s11, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #12.0
        vcmp.f32 s12, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #13.0
        vcmp.f32 s13, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #14.0
        vcmp.f32 s14, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #1.5
        vcmp.f32 s15, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #2.5
        vcmp.f32 s16, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #3.5
        vcmp.f32 s17, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #4.5
        vcmp.f32 s18, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #5.5
        vcmp.f32 s19, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #6.5
        vcmp.f32 s20, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #7.5
        vcmp.f32 s21, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #8.5
        vcmp.f32 s22, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #9.5
        vcmp.f32 s23, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #10.5
        vcmp.f32 s24, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #11.5
        vcmp.f32 s25, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #12.5
        vcmp.f32 s26, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #13.5
        vcmp.f32 s27, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #14.5
        vcmp.f32 s28, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #1.0
        vcmp.f32 s29, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #2.0
        vcmp.f32 s30, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop
        vmov.f32 s0, #3.0
        vcmp.f32 s31, s0
        vmrs     APSR_nzcv, FPSCR
        bne      reg2_error_loop

        /* Everything passed, inc the loop counter. */
        push { r0, r1 }
        ldr  r0, =ulRegTest2LoopCounter
        ldr  r1, [r0]
        adds r1, r1, #1
        str  r1, [r0]
        pop  { r0, r1 }

        /* Start again. */
        b reg2_loop

    reg2_error_loop:
        /* If this line is hit then there was an error in
         * a core register value. The loop ensures the
         * loop counter stops incrementing. */
        b reg2_error_loop
        nop
        ltorg
/*-----------------------------------------------------------*/

vRegTest3Asm_NonSecure:
    /* Fill the core registers with known values. */
    movs r0,  #100
    movs r1,  #101
    movs r2,  #102
    movs r3,  #103
    movs r4,  #104
    movs r5,  #105
    movs r6,  #106
    movs r7,  #107
    mov  r8,  #108
    mov  r9,  #109
    mov  r10, #110
    mov  r11, #111
    mov  r12, #112

    /* Fill the FPU registers with known values. */
    vmov.f32 s0,  #1.5
    vmov.f32 s2,  #2.0
    vmov.f32 s3,  #3.5
    vmov.f32 s4,  #4.0
    vmov.f32 s5,  #5.5
    vmov.f32 s6,  #6.0
    vmov.f32 s7,  #7.5
    vmov.f32 s8,  #8.0
    vmov.f32 s9,  #9.5
    vmov.f32 s10, #10.0
    vmov.f32 s11, #11.5
    vmov.f32 s12, #12.0
    vmov.f32 s13, #13.5
    vmov.f32 s14, #14.0
    vmov.f32 s15, #1.5
    vmov.f32 s16, #2.0
    vmov.f32 s17, #3.5
    vmov.f32 s18, #4.0
    vmov.f32 s19, #5.5
    vmov.f32 s20, #6.0
    vmov.f32 s21, #7.5
    vmov.f32 s22, #8.0
    vmov.f32 s23, #9.5
    vmov.f32 s24, #10.0
    vmov.f32 s25, #11.5
    vmov.f32 s26, #12.0
    vmov.f32 s27, #13.5
    vmov.f32 s28, #14.0
    vmov.f32 s29, #1.5
    vmov.f32 s30, #2.0
    vmov.f32 s31, #3.5

    reg3_loop:
        /* Verify that core registers contain correct values. */
        cmp r0, #100
        bne reg3_error_loop
        cmp r1, #101
        bne reg3_error_loop
        cmp r2, #102
        bne reg3_error_loop
        cmp r3, #103
        bne reg3_error_loop
        cmp r4, #104
        bne reg3_error_loop
        cmp r5, #105
        bne reg3_error_loop
        cmp r6, #106
        bne reg3_error_loop
        cmp r7, #107
        bne reg3_error_loop
        cmp r8, #108
        bne reg3_error_loop
        cmp r9, #109
        bne reg3_error_loop
        cmp r10, #110
        bne reg3_error_loop
        cmp r11, #111
        bne reg3_error_loop
        cmp r12, #112
        bne reg3_error_loop

        /* Verify that FPU registers contain correct values. */
        vmov.f32 s1, #1.5
        vcmp.f32 s0, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #2.0
        vcmp.f32 s2, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #3.5
        vcmp.f32 s3, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #4.0
        vcmp.f32 s4, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #5.5
        vcmp.f32 s5, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #6.0
        vcmp.f32 s6, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #7.5
        vcmp.f32 s7, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #8.0
        vcmp.f32 s8, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #9.5
        vcmp.f32 s9, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #10.0
        vcmp.f32 s10, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #11.5
        vcmp.f32 s11, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #12.0
        vcmp.f32 s12, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #13.5
        vcmp.f32 s13, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #14.0
        vcmp.f32 s14, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #1.5
        vcmp.f32 s15, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #2.0
        vcmp.f32 s16, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #3.5
        vcmp.f32 s17, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #4.0
        vcmp.f32 s18, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #5.5
        vcmp.f32 s19, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #6.0
        vcmp.f32 s20, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #7.5
        vcmp.f32 s21, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #8.0
        vcmp.f32 s22, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #9.5
        vcmp.f32 s23, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #10.0
        vcmp.f32 s24, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #11.5
        vcmp.f32 s25, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #12.0
        vcmp.f32 s26, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #13.5
        vcmp.f32 s27, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #14.0
        vcmp.f32 s28, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #1.5
        vcmp.f32 s29, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #2.0
        vcmp.f32 s30, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop
        vmov.f32 s1, #3.5
        vcmp.f32 s31, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg3_error_loop

        /* Everything passed, inc the loop counter. */
        push { r0, r1 }
        ldr  r0, =ulRegTest3LoopCounter
        ldr  r1, [r0]
        adds r1, r1, #1
        str  r1, [r0]

        /* Yield to increase test coverage. */
        movs r0, #0x01
        ldr  r1, =0xe000ed04    /* NVIC_ICSR. */
        lsls r0, #28            /* Shift to PendSV bit. */
        str  r0, [r1]
        dsb
        pop  { r0, r1 }

        /* Start again. */
        b reg3_loop

    reg3_error_loop:
        /* If this line is hit then there was an error in
         * a core register value. The loop ensures the
         * loop counter stops incrementing. */
        b reg3_error_loop
        nop
        ltorg
/*-----------------------------------------------------------*/

vRegTest4Asm_NonSecure:
    /* Fill the core registers with known values. */
    movs r0, #0
    movs r1, #1
    movs r2, #2
    movs r3, #3
    movs r4, #4
    movs r5, #5
    movs r6, #6
    movs r7, #7
    mov  r8, #8
    mov  r9, #9
    movs r10, #10
    movs r11, #11
    movs r12, #12

    /* Fill the FPU registers with known values. */
    vmov.f32 s0,  #1.5
    vmov.f32 s2,  #2.0
    vmov.f32 s3,  #3.0
    vmov.f32 s4,  #4.5
    vmov.f32 s5,  #5.0
    vmov.f32 s6,  #6.0
    vmov.f32 s7,  #7.5
    vmov.f32 s8,  #8.0
    vmov.f32 s9,  #9.0
    vmov.f32 s10, #10.5
    vmov.f32 s11, #11.0
    vmov.f32 s12, #12.0
    vmov.f32 s13, #13.5
    vmov.f32 s14, #14.0
    vmov.f32 s15, #1.0
    vmov.f32 s16, #2.5
    vmov.f32 s17, #3.0
    vmov.f32 s18, #4.0
    vmov.f32 s19, #5.5
    vmov.f32 s20, #6.0
    vmov.f32 s21, #7.0
    vmov.f32 s22, #8.5
    vmov.f32 s23, #9.0
    vmov.f32 s24, #10.0
    vmov.f32 s25, #11.5
    vmov.f32 s26, #12.0
    vmov.f32 s27, #13.0
    vmov.f32 s28, #14.5
    vmov.f32 s29, #1.0
    vmov.f32 s30, #2.0
    vmov.f32 s31, #3.5

    reg4_loop:
        /* Verify that core registers contain correct values. */
        cmp  r0, #0
        bne  reg4_error_loop
        cmp  r1, #1
        bne  reg4_error_loop
        cmp  r2, #2
        bne  reg4_error_loop
        cmp  r3, #3
        bne  reg4_error_loop
        cmp  r4, #4
        bne  reg4_error_loop
        cmp  r5, #5
        bne  reg4_error_loop
        cmp  r6, #6
        bne  reg4_error_loop
        cmp  r7, #7
        bne  reg4_error_loop
        cmp  r8, #8
        bne  reg4_error_loop
        cmp  r9, #9
        bne  reg4_error_loop
        cmp  r10, #10
        bne  reg4_error_loop
        cmp  r11, #11
        bne  reg4_error_loop
        cmp  r12, #12
        bne  reg4_error_loop

        /* Verify that FPU registers contain correct values. */
        vmov.f32 s1, #1.5
        vcmp.f32 s0, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #2.0
        vcmp.f32 s2, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #3.0
        vcmp.f32 s3, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #4.5
        vcmp.f32 s4, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #5.0
        vcmp.f32 s5, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #6.0
        vcmp.f32 s6, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #7.5
        vcmp.f32 s7, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #8.0
        vcmp.f32 s8, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #9.0
        vcmp.f32 s9, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #10.5
        vcmp.f32 s10, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #11.0
        vcmp.f32 s11, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #12.0
        vcmp.f32 s12, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #13.5
        vcmp.f32 s13, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #14.0
        vcmp.f32 s14, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #1.0
        vcmp.f32 s15, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #2.5
        vcmp.f32 s16, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #3.0
        vcmp.f32 s17, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #4.0
        vcmp.f32 s18, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #5.5
        vcmp.f32 s19, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #6.0
        vcmp.f32 s20, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #7.0
        vcmp.f32 s21, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #8.5
        vcmp.f32 s22, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #9.0
        vcmp.f32 s23, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #10.0
        vcmp.f32 s24, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #11.5
        vcmp.f32 s25, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #12.0
        vcmp.f32 s26, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #13.0
        vcmp.f32 s27, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #14.5
        vcmp.f32 s28, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #1.0
        vcmp.f32 s29, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #2.0
        vcmp.f32 s30, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop
        vmov.f32 s1, #3.5
        vcmp.f32 s31, s1
        vmrs     APSR_nzcv, FPSCR
        bne      reg4_error_loop

        /* Everything passed, inc the loop counter. */
        push { r0, r1 }
        ldr  r0, =ulRegTest4LoopCounter
        ldr  r1, [r0]
        adds r1, r1, #1
        str  r1, [r0]
        pop  { r0, r1 }

        /* Start again. */
        b reg4_loop

    reg4_error_loop:
        /* If this line is hit then there was an error in
         * a core register value. The loop ensures the
         * loop counter stops incrementing. */
        b reg4_error_loop
        nop
        ltorg
/*-----------------------------------------------------------*/

vRegTestAsm_NonSecureCallback:
    /* Store callee saved registers. */
    push { r4-r12 }

    /* Fill the core registers with known values. */
    movs r0, #150
    movs r1, #151
    movs r2, #152
    movs r3, #153
    movs r4, #154
    movs r5, #155
    movs r6, #156
    movs r7, #157
    movs r8, #158
    movs r9, #159
    movs r10, #160
    movs r11, #161
    movs r12, #162

    /* Fill the FPU registers with known values. */
    vmov.f32 s0,  #1.0
    vmov.f32 s2,  #2.5
    vmov.f32 s3,  #3.5
    vmov.f32 s4,  #4.0
    vmov.f32 s5,  #5.5
    vmov.f32 s6,  #6.5
    vmov.f32 s7,  #7.0
    vmov.f32 s8,  #8.5
    vmov.f32 s9,  #9.5
    vmov.f32 s10, #10.0
    vmov.f32 s11, #11.5
    vmov.f32 s12, #12.5
    vmov.f32 s13, #13.0
    vmov.f32 s14, #14.5
    vmov.f32 s15, #1.5
    vmov.f32 s16, #2.0
    vmov.f32 s17, #3.5
    vmov.f32 s18, #4.5
    vmov.f32 s19, #5.0
    vmov.f32 s20, #6.5
    vmov.f32 s21, #7.5
    vmov.f32 s22, #8.0
    vmov.f32 s23, #9.5
    vmov.f32 s24, #10.5
    vmov.f32 s25, #11.0
    vmov.f32 s26, #12.5
    vmov.f32 s27, #13.5
    vmov.f32 s28, #14.0
    vmov.f32 s29, #1.5
    vmov.f32 s30, #2.5
    vmov.f32 s31, #3.0

    /* Force a context switch by pending sv. */
    push { r0, r1 }
    movs r0, #0x01
    ldr  r1, =0xe000ed04    /* NVIC_ICSR. */
    lsls r0, #28            /* Shift to PendSV bit. */
    str  r0, [r1]
    dsb
    pop  { r0, r1 }

    /* Verify that core registers contain correct values. */
    cmp  r0, #150
    bne  reg_nscb_error_loop
    cmp  r1, #151
    bne  reg_nscb_error_loop
    cmp  r2, #152
    bne  reg_nscb_error_loop
    cmp  r3, #153
    bne  reg_nscb_error_loop
    cmp  r4, #154
    bne  reg_nscb_error_loop
    cmp  r5, #155
    bne  reg_nscb_error_loop
    cmp  r6, #156
    bne  reg_nscb_error_loop
    cmp  r7, #157
    bne  reg_nscb_error_loop
    cmp  r8, #158
    bne  reg_nscb_error_loop
    cmp  r9, #159
    bne  reg_nscb_error_loop
    cmp  r10, #160
    bne  reg_nscb_error_loop
    cmp  r11, #161
    bne  reg_nscb_error_loop
    cmp  r12, #162
    bne  reg_nscb_error_loop

    /* Verify that FPU registers contain correct values. */
    vmov.f32 s1, #1.0
    vcmp.f32 s0, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #2.5
    vcmp.f32 s2, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s3, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #4.0
    vcmp.f32 s4, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #5.5
    vcmp.f32 s5, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #6.5
    vcmp.f32 s6, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #7.0
    vcmp.f32 s7, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #8.5
    vcmp.f32 s8, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #9.5
    vcmp.f32 s9, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #10.0
    vcmp.f32 s10, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #11.5
    vcmp.f32 s11, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #12.5
    vcmp.f32 s12, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #13.0
    vcmp.f32 s13, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #14.5
    vcmp.f32 s14, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #1.5
    vcmp.f32 s15, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s16, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s17, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #4.5
    vcmp.f32 s18, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #5.0
    vcmp.f32 s19, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #6.5
    vcmp.f32 s20, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #7.5
    vcmp.f32 s21, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #8.0
    vcmp.f32 s22, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #9.5
    vcmp.f32 s23, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #10.5
    vcmp.f32 s24, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #11.0
    vcmp.f32 s25, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #12.5
    vcmp.f32 s26, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #13.5
    vcmp.f32 s27, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #14.0
    vcmp.f32 s28, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #1.5
    vcmp.f32 s29, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #2.5
    vcmp.f32 s30, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop
    vmov.f32 s1, #3.0
    vcmp.f32 s31, s1
    vmrs     APSR_nzcv, FPSCR
    bne      reg_nscb_error_loop

    /* Everything passed, finish. */
    b reg_nscb_success

    reg_nscb_error_loop:
        /* If this line is hit then there was an error in
         * a core register value. The loop ensures the
         * loop counter stops incrementing. */
        b reg_nscb_error_loop
        nop

    reg_nscb_success:
        /* Restore callee saved registers. */
        pop { r4-r12 }
        bx lr
        ltorg
/*-----------------------------------------------------------*/

    END
