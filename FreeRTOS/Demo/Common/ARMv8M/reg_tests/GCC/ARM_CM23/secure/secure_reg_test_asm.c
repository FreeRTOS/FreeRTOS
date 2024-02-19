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

/* Standard includes. */
#include <stdint.h>
#include <arm_cmse.h>

/* Interface includes. */
#include "secure_reg_test_asm.h"

/* FreeRTOS includes. */
#include "secure_port_macros.h"

/* typedef for non-secure callback function. */
typedef RegTestCallback_t NonSecureRegTestCallback_t __attribute__( ( cmse_nonsecure_call ) );
/*-----------------------------------------------------------*/

secureportNON_SECURE_CALLABLE void vRegTestAsm_Secure( void )
{
    __asm volatile
    (
        ".syntax unified                                                \n"
        "                                                               \n"
        "    /* Store callee saved registers. */                        \n"
        "    push { r4-r7 }                                             \n"
        "    mov r0, r8                                                 \n"
        "    mov r1, r9                                                 \n"
        "    mov r2, r10                                                \n"
        "    mov r3, r11                                                \n"
        "    mov r4, r12                                                \n"
        "    push { r0-r4 }                                             \n"
        "                                                               \n"
        "    /* Fill the core registers with known values. */           \n"
        "    movs r1, #201                                              \n"
        "    movs r2, #202                                              \n"
        "    movs r3, #203                                              \n"
        "    movs r4, #204                                              \n"
        "    movs r5, #205                                              \n"
        "    movs r6, #206                                              \n"
        "    movs r7, #207                                              \n"
        "    movs r0, #208                                              \n"
        "    mov  r8, r0                                                \n"
        "    movs r0, #209                                              \n"
        "    mov  r9, r0                                                \n"
        "    movs r0, #210                                              \n"
        "    mov  r10, r0                                               \n"
        "    movs r0, #211                                              \n"
        "    mov  r11, r0                                               \n"
        "    movs r0, #212                                              \n"
        "    mov  r12, r0                                               \n"
        "    movs r0, #200                                              \n"
        "                                                               \n"
        "    /* Force a context switch by pending non-secure sv. */     \n"
        "    push { r0, r1 }                                            \n"
        "    movs r0, #0x01                                             \n"
        "    ldr  r1, =0xe002ed04                                       \n" /* NVIC_ICSR_NS. */
        "    lsls r0, #28                                               \n" /* Shift to PendSV bit. */
        "    str  r0, [r1]                                              \n"
        "    dsb                                                        \n"
        "    pop  { r0, r1 }                                            \n"
        "                                                               \n"
        "    /* Verify that core registers contain correct values. */   \n"
        "    cmp  r0, #200                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r1, #201                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r2, #202                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r3, #203                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r4, #204                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r5, #205                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r6, #206                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r7, #207                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    movs r0, #208                                              \n"
        "    cmp  r8, r0                                                \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    movs r0, #209                                              \n"
        "    cmp  r9, r0                                                \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    movs r0, #210                                              \n"
        "    cmp  r10, r0                                               \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    movs r0, #211                                              \n"
        "    cmp  r11, r0                                               \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    movs r0, #212                                              \n"
        "    cmp  r12, r0                                               \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "                                                               \n"
        "    /* Everything passed, finish. */                           \n"
        "    b secure_reg_test_success                                  \n"
        "                                                               \n"
        "secure_reg_test_error_loop:                                    \n"
        "    /* If this line is hit then there was an error in          \n"
        "     * a core register value. The loop ensures the             \n"
        "     * loop counter stops incrementing. */                     \n"
        "    b secure_reg_test_error_loop                               \n"
        "    nop                                                        \n"
        "                                                               \n"
        "secure_reg_test_success:                                       \n"
        "    /* Restore callee saved registers. */                      \n"
        "    pop { r0-r4 }                                              \n"
        "    mov r8, r0                                                 \n"
        "    mov r9, r1                                                 \n"
        "    mov r10, r2                                                \n"
        "    mov r11, r3                                                \n"
        "    mov r12, r4                                                \n"
        "    pop { r4-r7 }                                              \n"
    );
}
/*-----------------------------------------------------------*/

secureportNON_SECURE_CALLABLE void vRegTest_NonSecureCallback( RegTestCallback_t pxRegTestCallback )
{
    NonSecureRegTestCallback_t pxNonSecureRegTestCallback;

    /* Return function pointer with cleared LSB. */
    pxNonSecureRegTestCallback = ( NonSecureRegTestCallback_t ) cmse_nsfptr_create( pxRegTestCallback );

    /* Invoke the callback which runs reg tests. */
    pxNonSecureRegTestCallback();
}
/*-----------------------------------------------------------*/
