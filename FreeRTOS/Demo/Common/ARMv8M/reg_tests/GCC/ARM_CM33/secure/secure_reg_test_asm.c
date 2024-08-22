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
        "    push { r4-r12 }                                            \n"
        "                                                               \n"
        "    /* Fill the core registers with known values. */           \n"
        "    movs r0, #200                                              \n"
        "    movs r1, #201                                              \n"
        "    movs r1, #201                                              \n"
        "    movs r2, #202                                              \n"
        "    movs r3, #203                                              \n"
        "    movs r4, #204                                              \n"
        "    movs r5, #205                                              \n"
        "    movs r6, #206                                              \n"
        "    movs r7, #207                                              \n"
        "    movs r8, #208                                              \n"
        "    movs r9, #209                                              \n"
        "    movs r10, #210                                             \n"
        "    movs r11, #211                                             \n"
        "    movs r12, #212                                             \n"
        "                                                               \n"
        "    /* Fill the FPU registers with known values. */            \n"
        "    vmov.f32 s0,  #1.0                                         \n"
        "    vmov.f32 s2,  #2.0                                         \n"
        "    vmov.f32 s3,  #3.5                                         \n"
        "    vmov.f32 s4,  #4.5                                         \n"
        "    vmov.f32 s5,  #5.0                                         \n"
        "    vmov.f32 s6,  #6.0                                         \n"
        "    vmov.f32 s7,  #7.5                                         \n"
        "    vmov.f32 s8,  #8.5                                         \n"
        "    vmov.f32 s9,  #9.0                                         \n"
        "    vmov.f32 s10, #10.0                                        \n"
        "    vmov.f32 s11, #11.5                                        \n"
        "    vmov.f32 s12, #12.5                                        \n"
        "    vmov.f32 s13, #13.0                                        \n"
        "    vmov.f32 s14, #14.0                                        \n"
        "    vmov.f32 s15, #1.5                                         \n"
        "    vmov.f32 s16, #2.5                                         \n"
        "    vmov.f32 s17, #3.0                                         \n"
        "    vmov.f32 s18, #4.0                                         \n"
        "    vmov.f32 s19, #5.5                                         \n"
        "    vmov.f32 s20, #6.5                                         \n"
        "    vmov.f32 s21, #7.0                                         \n"
        "    vmov.f32 s22, #8.0                                         \n"
        "    vmov.f32 s23, #9.5                                         \n"
        "    vmov.f32 s24, #10.5                                        \n"
        "    vmov.f32 s25, #11.0                                        \n"
        "    vmov.f32 s26, #12.0                                        \n"
        "    vmov.f32 s27, #13.5                                        \n"
        "    vmov.f32 s28, #14.5                                        \n"
        "    vmov.f32 s29, #1.0                                         \n"
        "    vmov.f32 s30, #2.0                                         \n"
        "    vmov.f32 s31, #3.5                                         \n"
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
        "    cmp  r8, #208                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r9, #209                                              \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r10, #210                                             \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r11, #211                                             \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "    cmp  r12, #212                                             \n"
        "    bne  secure_reg_test_error_loop                            \n"
        "                                                               \n"
        "    /* Verify that FPU registers contain correct values. */    \n"
        "    vmov.f32 s1, #1.0                                          \n"
        "    vcmp.f32 s0, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #2.0                                          \n"
        "    vcmp.f32 s2, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #3.5                                          \n"
        "    vcmp.f32 s3, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #4.5                                          \n"
        "    vcmp.f32 s4, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #5.0                                          \n"
        "    vcmp.f32 s5, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #6.0                                          \n"
        "    vcmp.f32 s6, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #7.5                                          \n"
        "    vcmp.f32 s7, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #8.5                                          \n"
        "    vcmp.f32 s8, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #9.0                                          \n"
        "    vcmp.f32 s9, s1                                            \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #10.0                                         \n"
        "    vcmp.f32 s10, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #11.5                                         \n"
        "    vcmp.f32 s11, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #12.5                                         \n"
        "    vcmp.f32 s12, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #13.0                                         \n"
        "    vcmp.f32 s13, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #14.0                                         \n"
        "    vcmp.f32 s14, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #1.5                                          \n"
        "    vcmp.f32 s15, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #2.5                                          \n"
        "    vcmp.f32 s16, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #3.0                                          \n"
        "    vcmp.f32 s17, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #4.0                                          \n"
        "    vcmp.f32 s18, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #5.5                                          \n"
        "    vcmp.f32 s19, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #6.5                                          \n"
        "    vcmp.f32 s20, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #7.0                                          \n"
        "    vcmp.f32 s21, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #8.0                                          \n"
        "    vcmp.f32 s22, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #9.5                                          \n"
        "    vcmp.f32 s23, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #10.5                                         \n"
        "    vcmp.f32 s24, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #11.0                                         \n"
        "    vcmp.f32 s25, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #12.0                                         \n"
        "    vcmp.f32 s26, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #13.5                                         \n"
        "    vcmp.f32 s27, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #14.5                                         \n"
        "    vcmp.f32 s28, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #1.0                                          \n"
        "    vcmp.f32 s29, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #2.0                                          \n"
        "    vcmp.f32 s30, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
        "    vmov.f32 s1, #3.5                                          \n"
        "    vcmp.f32 s31, s1                                           \n"
        "    vmrs     APSR_nzcv, FPSCR                                  \n"
        "    bne      secure_reg_test_error_loop                        \n"
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
        "    pop { r4-r12 }                                             \n"
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
