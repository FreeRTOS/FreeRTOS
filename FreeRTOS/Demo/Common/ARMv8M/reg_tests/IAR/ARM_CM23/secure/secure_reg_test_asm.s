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
    push { r4-r7 }
    mov r0, r8
    mov r1, r9
    mov r2, r10
    mov r3, r11
    mov r4, r12
    push { r0-r4 }

    /* Fill the core registers with known values. */
    movs r1, #201
    movs r2, #202
    movs r3, #203
    movs r4, #204
    movs r5, #205
    movs r6, #206
    movs r7, #207
    movs r0, #208
    mov  r8, r0
    movs r0, #209
    mov  r9, r0
    movs r0, #210
    mov  r10, r0
    movs r0, #211
    mov  r11, r0
    movs r0, #212
    mov  r12, r0
    movs r0, #200

    /* Force a context switch by pending non-secure sv. */
    push { r0, r1 }
    movs r0, #0x01
    ldr  r1, =0xe002ed04    /* NVIC_ICSR_NS. */
    lsls r0, r0, #28        /* Shift to PendSV bit. */
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
    movs r0, #208
    cmp  r8, r0
    bne  secure_reg_test_error_loop
    movs r0, #209
    cmp  r9, r0
    bne  secure_reg_test_error_loop
    movs r0, #210
    cmp  r10, r0
    bne  secure_reg_test_error_loop
    movs r0, #211
    cmp  r11, r0
    bne  secure_reg_test_error_loop
    movs r0, #212
    cmp  r12, r0
    bne  secure_reg_test_error_loop

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
        pop { r0-r4 }
        mov r8, r0
        mov r9, r1
        mov r10, r2
        mov r11, r3
        mov r12, r4
        pop { r4-r7 }
        bx lr
/*-----------------------------------------------------------*/

    END
