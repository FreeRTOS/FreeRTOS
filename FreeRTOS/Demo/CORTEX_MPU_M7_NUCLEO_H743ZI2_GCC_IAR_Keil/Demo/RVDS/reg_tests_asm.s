;/*
; * FreeRTOS V202212.00
; * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
; *
; * Permission is hereby granted, free of charge, to any person obtaining a copy of
; * this software and associated documentation files (the "Software"), to deal in
; * the Software without restriction, including without limitation the rights to
; * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
; * the Software, and to permit persons to whom the Software is furnished to do so,
; * subject to the following conditions:
; *
; * The above copyright notice and this permission notice shall be included in all
; * copies or substantial portions of the Software.
; *
; * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
; * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
; * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
; * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
; * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
; *
; * https://www.FreeRTOS.org
; * https://github.com/FreeRTOS
; *
; */

;/*
; * "Reg test" tasks - These fill the registers with known values, then check
; * that each register maintains its expected value for the lifetime of the
; * task.  Each task uses a different set of values.  The reg test tasks execute
; * with a very low priority, so get preempted very frequently.  A register
; * containing an unexpected value is indicative of an error in the context
; * switching mechanism.
; */
;/*-----------------------------------------------------------*/

    IMPORT ulRegTest1LoopCounter
    IMPORT ulRegTest2LoopCounter
    IMPORT ulRegTest3LoopCounter
    IMPORT ulRegTest4LoopCounter

    EXPORT vRegTest1Asm
    EXPORT vRegTest2Asm
    EXPORT vRegTest3Asm
    EXPORT vRegTest4Asm

    AREA REG_TESTS_ASM, CODE, READONLY
;/*-----------------------------------------------------------*/

vRegTest1Asm

    PRESERVE8

    ;/* Fill the core registers with known values. */
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

    ;/* Fill the FPU registers with known values. */
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

reg1_loop
    ;/* Verify that core registers contain correct values. */
    cmp r0, #100
    bne.w reg1_error_loop
    cmp r1, #101
    bne.w reg1_error_loop
    cmp r2, #102
    bne.w reg1_error_loop
    cmp r3, #103
    bne.w reg1_error_loop
    cmp r4, #104
    bne.w reg1_error_loop
    cmp r5, #105
    bne.w reg1_error_loop
    cmp r6, #106
    bne.w reg1_error_loop
    cmp r7, #107
    bne.w reg1_error_loop
    cmp r8, #108
    bne.w reg1_error_loop
    cmp r9, #109
    bne.w reg1_error_loop
    cmp r10, #110
    bne.w reg1_error_loop
    cmp r11, #111
    bne.w reg1_error_loop
    cmp r12, #112
    bne.w reg1_error_loop

    ;/* Verify that FPU registers contain correct values. */
    vmov.f32 s0, #1.5           ;/* s0 = 1.5. */
    vcmp.f32 s1, s0             ;/* Compare s0 and s1. */
    vmrs     APSR_nzcv, FPSCR   ;/* Copy floating point flags (FPSCR flags) to ASPR flags - needed for next bne.w to work. */
    bne.w      reg1_error_loop
    vmov.f32 s0, #2.5
    vcmp.f32 s2, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #3.5
    vcmp.f32 s3, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #4.5
    vcmp.f32 s4, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #5.5
    vcmp.f32 s5, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #6.5
    vcmp.f32 s6, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #7.5
    vcmp.f32 s7, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #8.5
    vcmp.f32 s8, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #9.5
    vcmp.f32 s9, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #10.5
    vcmp.f32 s10, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #11.5
    vcmp.f32 s11, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #12.5
    vcmp.f32 s12, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #13.5
    vcmp.f32 s13, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #14.5
    vcmp.f32 s14, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #1.0
    vcmp.f32 s15, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #2.0
    vcmp.f32 s16, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #3.0
    vcmp.f32 s17, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #4.0
    vcmp.f32 s18, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #5.0
    vcmp.f32 s19, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #6.0
    vcmp.f32 s20, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #7.0
    vcmp.f32 s21, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #8.0
    vcmp.f32 s22, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #9.0
    vcmp.f32 s23, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #10.0
    vcmp.f32 s24, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #11.0
    vcmp.f32 s25, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #12.0
    vcmp.f32 s26, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #13.0
    vcmp.f32 s27, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #14.0
    vcmp.f32 s28, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #1.5
    vcmp.f32 s29, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #2.5
    vcmp.f32 s30, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop
    vmov.f32 s0, #3.5
    vcmp.f32 s31, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg1_error_loop

    ;/* Everything passed, inc the loop counter. */
    push { r0, r1 }
    ldr  r0, =ulRegTest1LoopCounter
    ldr  r1, [r0]
    adds r1, r1, #1
    str  r1, [r0]

    ;/* Yield to increase test coverage. */
    movs r0, #0x01
    ldr  r1, =0xe000ed04 ;/* NVIC_ICSR. */
    lsls r0, #28         ;/* Shift to PendSV bit. */
    str  r0, [r1]
    dsb
    pop  { r0, r1 }

    ;/* Start again. */
    b reg1_loop

reg1_error_loop
    b reg1_error_loop
    LTORG
;/*-----------------------------------------------------------*/

vRegTest2Asm

    PRESERVE8

    ;/* Fill the core registers with known values. */
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

    ;/* Fill the FPU registers with known values. */
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

reg2_loop
    ;/* Verify that core registers contain correct values. */
    cmp  r0, #0
    bne.w  reg2_error_loop
    cmp  r1, #1
    bne.w  reg2_error_loop
    cmp  r2, #2
    bne.w  reg2_error_loop
    cmp  r3, #3
    bne.w  reg2_error_loop
    cmp  r4, #4
    bne.w  reg2_error_loop
    cmp  r5, #5
    bne.w  reg2_error_loop
    cmp  r6, #6
    bne.w  reg2_error_loop
    cmp  r7, #7
    bne.w  reg2_error_loop
    cmp  r8, #8
    bne.w  reg2_error_loop
    cmp  r9, #9
    bne.w  reg2_error_loop
    cmp  r10, #10
    bne.w  reg2_error_loop
    cmp  r11, #11
    bne.w  reg2_error_loop
    cmp  r12, #12
    bne.w  reg2_error_loop

    ;/* Verify that FPU registers contain correct values. */
    vmov.f32 s0, #1.0
    vcmp.f32 s1, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #2.0
    vcmp.f32 s2, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #3.0
    vcmp.f32 s3, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #4.0
    vcmp.f32 s4, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #5.0
    vcmp.f32 s5, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #6.0
    vcmp.f32 s6, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #7.0
    vcmp.f32 s7, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #8.0
    vcmp.f32 s8, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #9.0
    vcmp.f32 s9, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #10.0
    vcmp.f32 s10, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #11.0
    vcmp.f32 s11, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #12.0
    vcmp.f32 s12, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #13.0
    vcmp.f32 s13, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #14.0
    vcmp.f32 s14, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #1.5
    vcmp.f32 s15, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #2.5
    vcmp.f32 s16, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #3.5
    vcmp.f32 s17, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #4.5
    vcmp.f32 s18, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #5.5
    vcmp.f32 s19, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #6.5
    vcmp.f32 s20, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #7.5
    vcmp.f32 s21, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #8.5
    vcmp.f32 s22, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #9.5
    vcmp.f32 s23, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #10.5
    vcmp.f32 s24, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #11.5
    vcmp.f32 s25, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #12.5
    vcmp.f32 s26, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #13.5
    vcmp.f32 s27, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #14.5
    vcmp.f32 s28, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #1.0
    vcmp.f32 s29, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #2.0
    vcmp.f32 s30, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop
    vmov.f32 s0, #3.0
    vcmp.f32 s31, s0
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg2_error_loop

    ;/* Everything passed, inc the loop counter. */
    push { r0, r1 }
    ldr  r0, =ulRegTest2LoopCounter
    ldr  r1, [r0]
    adds r1, r1, #1
    str  r1, [r0]
    pop  { r0, r1 }

    ;/* Start again. */
    b reg2_loop

reg2_error_loop
    b reg2_error_loop
    LTORG
;/*-----------------------------------------------------------*/

vRegTest3Asm

    PRESERVE8

    ;/* Fill the core registers with known values. */
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

    ;/* Fill the FPU registers with known values. */
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

reg3_loop
    ;/* Verify that core registers contain correct values. */
    cmp r0, #100
    bne.w reg3_error_loop
    cmp r1, #101
    bne.w reg3_error_loop
    cmp r2, #102
    bne.w reg3_error_loop
    cmp r3, #103
    bne.w reg3_error_loop
    cmp r4, #104
    bne.w reg3_error_loop
    cmp r5, #105
    bne.w reg3_error_loop
    cmp r6, #106
    bne.w reg3_error_loop
    cmp r7, #107
    bne.w reg3_error_loop
    cmp r8, #108
    bne.w reg3_error_loop
    cmp r9, #109
    bne.w reg3_error_loop
    cmp r10, #110
    bne.w reg3_error_loop
    cmp r11, #111
    bne.w reg3_error_loop
    cmp r12, #112
    bne.w reg3_error_loop

    ;/* Verify that FPU registers contain correct values. */
    vmov.f32 s1, #1.5
    vcmp.f32 s0, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s2, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s3, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #4.0
    vcmp.f32 s4, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #5.5
    vcmp.f32 s5, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #6.0
    vcmp.f32 s6, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #7.5
    vcmp.f32 s7, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #8.0
    vcmp.f32 s8, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #9.5
    vcmp.f32 s9, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #10.0
    vcmp.f32 s10, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #11.5
    vcmp.f32 s11, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #12.0
    vcmp.f32 s12, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #13.5
    vcmp.f32 s13, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #14.0
    vcmp.f32 s14, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #1.5
    vcmp.f32 s15, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s16, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s17, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #4.0
    vcmp.f32 s18, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #5.5
    vcmp.f32 s19, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #6.0
    vcmp.f32 s20, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #7.5
    vcmp.f32 s21, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #8.0
    vcmp.f32 s22, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #9.5
    vcmp.f32 s23, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #10.0
    vcmp.f32 s24, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #11.5
    vcmp.f32 s25, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #12.0
    vcmp.f32 s26, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #13.5
    vcmp.f32 s27, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #14.0
    vcmp.f32 s28, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #1.5
    vcmp.f32 s29, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s30, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s31, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg3_error_loop

    ;/* Everything passed, inc the loop counter. */
    push { r0, r1 }
    ldr  r0, =ulRegTest3LoopCounter
    ldr  r1, [r0]
    adds r1, r1, #1
    str  r1, [r0]

    ;/* Yield to increase test coverage. */
    movs r0, #0x01
    ldr  r1, =0xe000ed04    ;/* NVIC_ICSR. */
    lsls r0, #28            ;/* Shift to PendSV bit. */
    str  r0, [r1]
    dsb
    pop  { r0, r1 }

    ;/* Start again. */
    b reg3_loop

reg3_error_loop
    b reg3_error_loop
    LTORG
;/*-----------------------------------------------------------*/

vRegTest4Asm

    PRESERVE8

    ;/* Fill the core registers with known values. */
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

    ;/* Fill the FPU registers with known values. */
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

reg4_loop
    ;/* Verify that core registers contain correct values. */
    cmp  r0, #0
    bne.w  reg4_error_loop
    cmp  r1, #1
    bne.w  reg4_error_loop
    cmp  r2, #2
    bne.w  reg4_error_loop
    cmp  r3, #3
    bne.w  reg4_error_loop
    cmp  r4, #4
    bne.w  reg4_error_loop
    cmp  r5, #5
    bne.w  reg4_error_loop
    cmp  r6, #6
    bne.w  reg4_error_loop
    cmp  r7, #7
    bne.w  reg4_error_loop
    cmp  r8, #8
    bne.w  reg4_error_loop
    cmp  r9, #9
    bne.w  reg4_error_loop
    cmp  r10, #10
    bne.w  reg4_error_loop
    cmp  r11, #11
    bne.w  reg4_error_loop
    cmp  r12, #12
    bne.w  reg4_error_loop

    ;/* Verify that FPU registers contain correct values. */
    vmov.f32 s1, #1.5
    vcmp.f32 s0, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s2, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #3.0
    vcmp.f32 s3, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #4.5
    vcmp.f32 s4, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #5.0
    vcmp.f32 s5, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #6.0
    vcmp.f32 s6, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #7.5
    vcmp.f32 s7, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #8.0
    vcmp.f32 s8, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #9.0
    vcmp.f32 s9, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #10.5
    vcmp.f32 s10, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #11.0
    vcmp.f32 s11, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #12.0
    vcmp.f32 s12, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #13.5
    vcmp.f32 s13, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #14.0
    vcmp.f32 s14, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #1.0
    vcmp.f32 s15, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #2.5
    vcmp.f32 s16, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #3.0
    vcmp.f32 s17, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #4.0
    vcmp.f32 s18, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #5.5
    vcmp.f32 s19, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #6.0
    vcmp.f32 s20, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #7.0
    vcmp.f32 s21, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #8.5
    vcmp.f32 s22, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #9.0
    vcmp.f32 s23, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #10.0
    vcmp.f32 s24, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #11.5
    vcmp.f32 s25, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #12.0
    vcmp.f32 s26, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #13.0
    vcmp.f32 s27, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #14.5
    vcmp.f32 s28, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #1.0
    vcmp.f32 s29, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s30, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s31, s1
    vmrs     APSR_nzcv, FPSCR
    bne.w      reg4_error_loop

    ;/* Everything passed, inc the loop counter. */
    push { r0, r1 }
    ldr  r0, =ulRegTest4LoopCounter
    ldr  r1, [r0]
    adds r1, r1, #1
    str  r1, [r0]
    pop  { r0, r1 }

    ;/* Start again. */
    b reg4_loop

reg4_error_loop
    b reg4_error_loop
    LTORG
;/*-----------------------------------------------------------*/

    END