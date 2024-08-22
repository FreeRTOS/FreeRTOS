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

    SECTION .text:CODE:NOROOT(2)
    THUMB

    PUBLIC vRegTestAsm_SecureImpl
/*-----------------------------------------------------------*/

vRegTestAsm_SecureImpl:
    /* Store callee saved registers. */
    push { r4-r12 }

    /* Fill the core registers with known values. */
    movs r0, #200
    movs r1, #201
    movs r1, #201
    movs r2, #202
    movs r3, #203
    movs r4, #204
    movs r5, #205
    movs r6, #206
    movs r7, #207
    movs r8, #208
    movs r9, #209
    movs r10, #210
    movs r11, #211
    movs r12, #212

    /* Fill the FPU registers with known values. */
    vmov.f32 s0,  #1.0
    vmov.f32 s2,  #2.0
    vmov.f32 s3,  #3.5
    vmov.f32 s4,  #4.5
    vmov.f32 s5,  #5.0
    vmov.f32 s6,  #6.0
    vmov.f32 s7,  #7.5
    vmov.f32 s8,  #8.5
    vmov.f32 s9,  #9.0
    vmov.f32 s10, #10.0
    vmov.f32 s11, #11.5
    vmov.f32 s12, #12.5
    vmov.f32 s13, #13.0
    vmov.f32 s14, #14.0
    vmov.f32 s15, #1.5
    vmov.f32 s16, #2.5
    vmov.f32 s17, #3.0
    vmov.f32 s18, #4.0
    vmov.f32 s19, #5.5
    vmov.f32 s20, #6.5
    vmov.f32 s21, #7.0
    vmov.f32 s22, #8.0
    vmov.f32 s23, #9.5
    vmov.f32 s24, #10.5
    vmov.f32 s25, #11.0
    vmov.f32 s26, #12.0
    vmov.f32 s27, #13.5
    vmov.f32 s28, #14.5
    vmov.f32 s29, #1.0
    vmov.f32 s30, #2.0
    vmov.f32 s31, #3.5

    /* Force a context switch by pending non-secure sv. */
    push { r0, r1 }
    movs r0, #0x01
    ldr  r1, =0xe002ed04    /* NVIC_ICSR_NS. */
    lsls r0, #28            /* Shift to PendSV bit. */
    str  r0, [r1]
    dsb
    pop  { r0, r1 }

    /* Verify that core registers contain correct values. */
    cmp  r0, #200
    bne  secure_reg_test_error_loop
    cmp  r1, #201
    bne  secure_reg_test_error_loop
    cmp  r2, #202
    bne  secure_reg_test_error_loop
    cmp  r3, #203
    bne  secure_reg_test_error_loop
    cmp  r4, #204
    bne  secure_reg_test_error_loop
    cmp  r5, #205
    bne  secure_reg_test_error_loop
    cmp  r6, #206
    bne  secure_reg_test_error_loop
    cmp  r7, #207
    bne  secure_reg_test_error_loop
    cmp  r8, #208
    bne  secure_reg_test_error_loop
    cmp  r9, #209
    bne  secure_reg_test_error_loop
    cmp  r10, #210
    bne  secure_reg_test_error_loop
    cmp  r11, #211
    bne  secure_reg_test_error_loop
    cmp  r12, #212
    bne  secure_reg_test_error_loop

    /* Verify that FPU registers contain correct values. */
    vmov.f32 s1, #1.0
    vcmp.f32 s0, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s2, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s3, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #4.5
    vcmp.f32 s4, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #5.0
    vcmp.f32 s5, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #6.0
    vcmp.f32 s6, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #7.5
    vcmp.f32 s7, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #8.5
    vcmp.f32 s8, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #9.0
    vcmp.f32 s9, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #10.0
    vcmp.f32 s10, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #11.5
    vcmp.f32 s11, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #12.5
    vcmp.f32 s12, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #13.0
    vcmp.f32 s13, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #14.0
    vcmp.f32 s14, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #1.5
    vcmp.f32 s15, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #2.5
    vcmp.f32 s16, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #3.0
    vcmp.f32 s17, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #4.0
    vcmp.f32 s18, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #5.5
    vcmp.f32 s19, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #6.5
    vcmp.f32 s20, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #7.0
    vcmp.f32 s21, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #8.0
    vcmp.f32 s22, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #9.5
    vcmp.f32 s23, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #10.5
    vcmp.f32 s24, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #11.0
    vcmp.f32 s25, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #12.0
    vcmp.f32 s26, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #13.5
    vcmp.f32 s27, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #14.5
    vcmp.f32 s28, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #1.0
    vcmp.f32 s29, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #2.0
    vcmp.f32 s30, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop
    vmov.f32 s1, #3.5
    vcmp.f32 s31, s1
    vmrs     APSR_nzcv, FPSCR
    bne      secure_reg_test_error_loop

    /* Everything passed, finish. */
    b secure_reg_test_success

    secure_reg_test_error_loop:
        /* If this line is hit then there was an error in
         * a core register value. The loop ensures the
         * loop counter stops incrementing. */
        b secure_reg_test_error_loop
        nop

    secure_reg_test_success:
        /* Restore callee saved registers. */
        pop { r4-r12 }
        bx lr
/*-----------------------------------------------------------*/

    END
