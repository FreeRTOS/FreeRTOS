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
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 */
/*-----------------------------------------------------------*/

/* Functions that implement reg tests. */
void vRegTest1Asm( void ) __attribute__( ( naked ) );
void vRegTest2Asm( void ) __attribute__( ( naked ) );
void vRegTest3Asm( void ) __attribute__( ( naked ) );
void vRegTest4Asm( void ) __attribute__( ( naked ) );
/*-----------------------------------------------------------*/

void vRegTest1Asm( void ) /* __attribute__( ( naked ) ) */
{
    __asm volatile
    (
    ".extern ulRegTest1LoopCounter                              \n"
    ".syntax unified                                            \n"
    "                                                           \n"
    "    /* Fill the core registers with known values. */       \n"
    "    movs r0,  #100                                         \n"
    "    movs r1,  #101                                         \n"
    "    movs r2,  #102                                         \n"
    "    movs r3,  #103                                         \n"
    "    movs r4,  #104                                         \n"
    "    movs r5,  #105                                         \n"
    "    movs r6,  #106                                         \n"
    "    movs r7,  #107                                         \n"
    "    mov  r8,  #108                                         \n"
    "    mov  r9,  #109                                         \n"
    "    mov  r10, #110                                         \n"
    "    mov  r11, #111                                         \n"
    "    mov  r12, #112                                         \n"
    "                                                           \n"
    "reg1_loop:                                                 \n"
    "                                                           \n"
    " /* Verify that core registers contain correct values. */  \n"
    "    cmp r0, #100                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r1, #101                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r2, #102                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r3, #103                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r4, #104                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r5, #105                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r6, #106                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r7, #107                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r8, #108                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r9, #109                                           \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r10, #110                                          \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r11, #111                                          \n"
    "    bne reg1_error_loop                                    \n"
    "    cmp r12, #112                                          \n"
    "    bne reg1_error_loop                                    \n"
    "                                                           \n"
    "    /* Everything passed, inc the loop counter. */         \n"
    "    push { r0, r1 }                                        \n"
    "    ldr  r0, =ulRegTest1LoopCounter                        \n"
    "    ldr  r1, [r0]                                          \n"
    "    adds r1, r1, #1                                        \n"
    "    str  r1, [r0]                                          \n"
    "                                                           \n"
    "    /* Yield to increase test coverage. */                 \n"
    "    movs r0, #0x01                                         \n"
    "    ldr  r1, =0xe000ed04                                   \n" /* NVIC_ICSR. */
    "    lsls r0, #28                                           \n" /* Shift to PendSV bit. */
    "    str  r0, [r1]                                          \n"
    "    dsb                                                    \n"
    "    pop  { r0, r1 }                                        \n"
    "                                                           \n"
    "    /* Start again. */                                     \n"
    "    b reg1_loop                                            \n"
    "                                                           \n"
    "reg1_error_loop:                                           \n"
    "    /* If this line is hit then there was an error in      \n"
    "     * a core register value. The loop ensures the         \n"
    "     * loop counter stops incrementing. */                 \n"
    "    b reg1_error_loop                                      \n"
    "    nop                                                    \n"
    ".ltorg                                                     \n"
    );
}
/*-----------------------------------------------------------*/

void vRegTest2Asm( void ) /* __attribute__( ( naked ) ) */
{
    __asm volatile
    (
    ".extern ulRegTest2LoopCounter                              \n"
    ".syntax unified                                            \n"
    "                                                           \n"
    "    /* Fill the core registers with known values. */       \n"
    "    movs r0, #0                                            \n"
    "    movs r1, #1                                            \n"
    "    movs r2, #2                                            \n"
    "    movs r3, #3                                            \n"
    "    movs r4, #4                                            \n"
    "    movs r5, #5                                            \n"
    "    movs r6, #6                                            \n"
    "    movs r7, #7                                            \n"
    "    mov  r8, #8                                            \n"
    "    mov  r9, #9                                            \n"
    "    movs r10, #10                                          \n"
    "    movs r11, #11                                          \n"
    "    movs r12, #12                                          \n"
    "                                                           \n"
    "reg2_loop:                                                 \n"
    "                                                           \n"
    " /* Verify that core registers contain correct values. */  \n"
    "    cmp  r0, #0                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r1, #1                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r2, #2                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r3, #3                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r4, #4                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r5, #5                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r6, #6                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r7, #7                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r8, #8                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r9, #9                                            \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r10, #10                                          \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r11, #11                                          \n"
    "    bne  reg2_error_loop                                   \n"
    "    cmp  r12, #12                                          \n"
    "    bne  reg2_error_loop                                   \n"
    "                                                           \n"
    "    /* Everything passed, inc the loop counter. */         \n"
    "    push { r0, r1 }                                        \n"
    "    ldr  r0, =ulRegTest2LoopCounter                        \n"
    "    ldr  r1, [r0]                                          \n"
    "    adds r1, r1, #1                                        \n"
    "    str  r1, [r0]                                          \n"
    "    pop  { r0, r1 }                                        \n"
    "                                                           \n"
    "    /* Start again. */                                     \n"
    "    b reg2_loop                                            \n"
    "                                                           \n"
    "reg2_error_loop:                                           \n"
    "    /* If this line is hit then there was an error in      \n"
    "     * a core register value. The loop ensures the         \n"
    "     * loop counter stops incrementing. */                 \n"
    "    b reg2_error_loop                                      \n"
    "    nop                                                    \n"
    ".ltorg                                                     \n"
    );
}
/*-----------------------------------------------------------*/

void vRegTest3Asm( void ) /* __attribute__( ( naked ) ) */
{
    __asm volatile
    (
    ".extern ulRegTest3LoopCounter                              \n"
    ".syntax unified                                            \n"
    "                                                           \n"
    "    /* Fill the core registers with known values. */       \n"
    "    movs r0,  #100                                         \n"
    "    movs r1,  #101                                         \n"
    "    movs r2,  #102                                         \n"
    "    movs r3,  #103                                         \n"
    "    movs r4,  #104                                         \n"
    "    movs r5,  #105                                         \n"
    "    movs r6,  #106                                         \n"
    "    movs r7,  #107                                         \n"
    "    mov  r8,  #108                                         \n"
    "    mov  r9,  #109                                         \n"
    "    mov  r10, #110                                         \n"
    "    mov  r11, #111                                         \n"
    "    mov  r12, #112                                         \n"
    "                                                           \n"
    "reg3_loop:                                                 \n"
    "                                                           \n"
    " /* Verify that core registers contain correct values. */  \n"
    "    cmp r0, #100                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r1, #101                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r2, #102                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r3, #103                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r4, #104                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r5, #105                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r6, #106                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r7, #107                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r8, #108                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r9, #109                                           \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r10, #110                                          \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r11, #111                                          \n"
    "    bne reg3_error_loop                                    \n"
    "    cmp r12, #112                                          \n"
    "    bne reg3_error_loop                                    \n"
    "                                                           \n"
    "    /* Everything passed, inc the loop counter. */         \n"
    "    push { r0, r1 }                                        \n"
    "    ldr  r0, =ulRegTest3LoopCounter                        \n"
    "    ldr  r1, [r0]                                          \n"
    "    adds r1, r1, #1                                        \n"
    "    str  r1, [r0]                                          \n"
    "                                                           \n"
    "    /* Yield to increase test coverage. */                 \n"
    "    movs r0, #0x01                                         \n"
    "    ldr  r1, =0xe000ed04                                   \n" /* NVIC_ICSR. */
    "    lsls r0, #28                                           \n" /* Shift to PendSV bit. */
    "    str  r0, [r1]                                          \n"
    "    dsb                                                    \n"
    "    pop  { r0, r1 }                                        \n"
    "                                                           \n"
    "    /* Start again. */                                     \n"
    "    b reg3_loop                                            \n"
    "                                                           \n"
    "reg3_error_loop:                                           \n"
    "    /* If this line is hit then there was an error in      \n"
    "     * a core register value. The loop ensures the         \n"
    "     * loop counter stops incrementing. */                 \n"
    "    b reg3_error_loop                                      \n"
    "    nop                                                    \n"
    ".ltorg                                                     \n"
    );
}
/*-----------------------------------------------------------*/

void vRegTest4Asm( void ) /* __attribute__( ( naked ) ) */
{
    __asm volatile
    (
    ".extern ulRegTest4LoopCounter                              \n"
    ".syntax unified                                            \n"
    "                                                           \n"
    "    /* Fill the core registers with known values. */       \n"
    "    movs r0, #0                                            \n"
    "    movs r1, #1                                            \n"
    "    movs r2, #2                                            \n"
    "    movs r3, #3                                            \n"
    "    movs r4, #4                                            \n"
    "    movs r5, #5                                            \n"
    "    movs r6, #6                                            \n"
    "    movs r7, #7                                            \n"
    "    mov  r8, #8                                            \n"
    "    mov  r9, #9                                            \n"
    "    movs r10, #10                                          \n"
    "    movs r11, #11                                          \n"
    "    movs r12, #12                                          \n"
    "                                                           \n"
    "reg4_loop:                                                 \n"
    "                                                           \n"
    " /* Verify that core registers contain correct values. */  \n"
    "    cmp  r0, #0                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r1, #1                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r2, #2                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r3, #3                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r4, #4                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r5, #5                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r6, #6                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r7, #7                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r8, #8                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r9, #9                                            \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r10, #10                                          \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r11, #11                                          \n"
    "    bne  reg4_error_loop                                   \n"
    "    cmp  r12, #12                                          \n"
    "    bne  reg4_error_loop                                   \n"
    "                                                           \n"
    "    /* Everything passed, inc the loop counter. */         \n"
    "    push { r0, r1 }                                        \n"
    "    ldr  r0, =ulRegTest4LoopCounter                        \n"
    "    ldr  r1, [r0]                                          \n"
    "    adds r1, r1, #1                                        \n"
    "    str  r1, [r0]                                          \n"
    "    pop  { r0, r1 }                                        \n"
    "                                                           \n"
    "    /* Start again. */                                     \n"
    "    b reg4_loop                                            \n"
    "                                                           \n"
    "reg4_error_loop:                                           \n"
    "    /* If this line is hit then there was an error in      \n"
    "     * a core register value. The loop ensures the         \n"
    "     * loop counter stops incrementing. */                 \n"
    "    b reg4_error_loop                                      \n"
    "    nop                                                    \n"
    ".ltorg                                                     \n"
    );
}
/*-----------------------------------------------------------*/
