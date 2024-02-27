/*
 * FreeRTOS V202212.00
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#define FREERTOS_ASSEMBLY
    #include "portmacro_asm.h"
    #include "FreeRTOSConfig.h"
#undef FREERTOS_ASSEMBLY

    .global vRegTest1Implementation
    .global vRegTest2Implementation
    .extern vPortYield
    .extern MPU_vTaskDelay
    .extern
    .extern loopCounter
    .text
    .arm

/*-----------------------------------------------------------*/
    /* This function is explained in the comments at the top of main-full.c. */
.type vRegTest1Implementation, %function
vRegTest1Implementation:

    /* Fill each general purpose register with a known value. */
    MOV     R0,  #0xFF
    MOV     R1,  #0x11
    MOV     R2,  #0x22
    MOV     R3,  #0x33
    MOV     R4,  #0x44
    MOV     R5,  #0x55
    MOV     R6,  #0x66
    MOV     R7,  #0x77
    MOV     R8,  #0x88
    MOV     R9,  #0x99
    MOV     R10, #0xAA
    MOV     R11, #0xBB
    MOV     R12, #0xCC
    MOV     R14, #0xEE

    /* Fill each FPU register with a known value. */
    VMOV     D0,  R0,  R1
    VMOV     D1,  R2,  R3
    VMOV     D2,  R4,  R5
    VMOV     D3,  R6,  R7
    VMOV     D4,  R8,  R9
    VMOV     D5,  R10, R11
    VMOV     D6,  R0,  R1
    VMOV     D7,  R2,  R3
    VMOV     D8,  R4,  R5
    VMOV     D9,  R6,  R7
    VMOV     D10, R8,  R9
    VMOV     D11, R10, R11
    VMOV     D12, R0,  R1
    VMOV     D13, R2,  R3
    VMOV     D14, R4,  R5
    VMOV     D15, R6,  R7

    /* Loop, checking each iteration that each register still contains the
    expected value. */
reg1_loop:
    /* Perform a yield to increase test coverage */
    PUSH    {R0, R14}
    BLX     vPortYield
    POP     {R0, R14}

    /* Check all the VFP registers still contain the values set above.
    First save registers that are clobbered by the test. */
    PUSH    { R0-R1 }

    VMOV     R0, R1, D0
    CMP      R0, #0xFF
    BLNE     reg1_error_loopf
    CMP      R1, #0x11
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D1
    CMP      R0, #0x22
    BLNE     reg1_error_loopf
    CMP      R1, #0x33
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D2
    CMP      R0, #0x44
    BLNE     reg1_error_loopf
    CMP      R1, #0x55
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D3
    CMP      R0, #0x66
    BLNE     reg1_error_loopf
    CMP      R1, #0x77
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D4
    CMP      R0, #0x88
    BLNE     reg1_error_loopf
    CMP      R1, #0x99
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D5
    CMP      R0, #0xAA
    BLNE     reg1_error_loopf
    CMP      R1, #0xBB
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D6
    CMP      R0, #0xFF
    BLNE     reg1_error_loopf
    CMP      R1, #0x11
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D7
    CMP      R0, #0x22
    BLNE     reg1_error_loopf
    CMP      R1, #0x33
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D8
    CMP      R0, #0x44
    BLNE     reg1_error_loopf
    CMP      R1, #0x55
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D9
    CMP      R0, #0x66
    BLNE     reg1_error_loopf
    CMP      R1, #0x77
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D10
    CMP      R0, #0x88
    BLNE     reg1_error_loopf
    CMP      R1, #0x99
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D11
    CMP      R0, #0xAA
    BLNE     reg1_error_loopf
    CMP      R1, #0xBB
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D12
    CMP      R0, #0xFF
    BLNE     reg1_error_loopf
    CMP      R1, #0x11
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D13
    CMP      R0, #0x22
    BLNE     reg1_error_loopf
    CMP      R1, #0x33
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D14
    CMP      R0, #0x44
    BLNE     reg1_error_loopf
    CMP      R1, #0x55
    BLNE     reg1_error_loopf
    VMOV     R0, R1, D15
    CMP      R0, #0x66
    BLNE     reg1_error_loopf
    CMP      R1, #0x77
    BLNE     reg1_error_loopf


    /* Restore the registers that were clobbered by the test. */
    POP      {R0-R1}

    /* VFP register test passed.  Jump to the core register test. */
    B       reg1_loopf_pass

reg1_error_loopf:
    /* If this line is hit then a VFP register value was found to be
    incorrect. */
    B       reg1_error_loopf
    B        0xDEACFC

reg1_loopf_pass:

    /* Test each general purpose register to check that it still contains the
    expected known value, jumping to reg1_error_loop if any register contains
    an unexpected value. */
    CMP      R0, #0xFF
    BLNE     reg1_error_loop
    CMP      R1, #0x11
    BLNE     reg1_error_loop
    CMP      R2, #0x22
    BLNE     reg1_error_loop
    CMP      R3, #0x33
    BLNE     reg1_error_loop
    CMP      R4, #0x44
    BLNE     reg1_error_loop
    CMP      R5, #0x55
    BLNE     reg1_error_loop
    CMP      R6, #0x66
    BLNE     reg1_error_loop
    CMP      R7, #0x77
    BLNE     reg1_error_loop
    CMP      R8, #0x88
    BLNE     reg1_error_loop
    CMP      R9, #0x99
    BLNE     reg1_error_loop
    CMP      R10, #0xAA
    BLNE     reg1_error_loop
    CMP      R11, #0xBB
    BLNE     reg1_error_loop
    CMP      R12, #0xCC
    BLNE     reg1_error_loop
    CMP      R14, #0xEE
    BLNE     reg1_error_loop

    /* Everything passed, increment the loop counter. */
    PUSH    { R0-R1 }
    LDR     R0, =loopCounter
    LDR     R1, [R0]
    ADD     R1, R1, #1
    STR     R1, [R0]
    POP     { R0-R1 }

    /* Delay for 0x100 ticks before running again */
    PUSH    { R0-R4, R12, R14 }
    MOV     R0, #0x100
    /* As this is a privileged task, it can directly call vTaskDelay */
    LDR     R1, =vTaskDelay
    BLX     R1
    POP     { R0-R4, R12, R14 }

    /* Start again. */
    B       reg1_loop

reg1_error_loop:
    /* If this line is hit then there was an error in a core register value.
    The loop ensures the loop counter stops incrementing. */
    B       0xDEACFD
    NOP

/*-----------------------------------------------------------*/

.type vRegTest2Implementation, %function
vRegTest2Implementation:

    /* Put a known value in each register. */
    MOV      R0,  #0xFF000000
    MOV      R1,  #0x11000000
    MOV      R2,  #0x22000000
    MOV      R3,  #0x33000000
    MOV      R4,  #0x44000000
    MOV      R5,  #0x55000000
    MOV      R6,  #0x66000000
    MOV      R7,  #0x77000000
    MOV      R8,  #0x88000000
    MOV      R9,  #0x99000000
    MOV      R10, #0xAA000000
    MOV      R11, #0xBB000000
    MOV      R12, #0xCC000000
    MOV      R14, #0xEE000000

    /* Likewise the floating point registers */
    VMOV     D0,  R0,  R1
    VMOV     D1,  R2,  R3
    VMOV     D2,  R4,  R5
    VMOV     D3,  R6,  R7
    VMOV     D4,  R8,  R9
    VMOV     D5,  R10, R11
    VMOV     D6,  R0,  R1
    VMOV     D7,  R2,  R3
    VMOV     D8,  R4,  R5
    VMOV     D9,  R6,  R7
    VMOV     D10, R8,  R9
    VMOV     D11, R10, R11
    VMOV     D12, R0,  R1
    VMOV     D13, R2,  R3
    VMOV     D14, R4,  R5
    VMOV     D15, R6,  R7

    /* Loop, checking each iteration that each register still contains the
    expected value. */
reg2_loop:

    /* Yield to increase test coverage */
    PUSH    {R0, R14}
    BLX     vPortYield
    POP     {R0, R14}

    /* Check all the VFP registers still contain the values set above.
    First save registers that are clobbered by the test. */
    PUSH     { R0-R1 }

    VMOV     R0, R1, D0
    CMP      R0, #0xFF000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x11000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D1
    CMP      R0, #0x22000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x33000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D2
    CMP      R0, #0x44000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x55000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D3
    CMP      R0, #0x66000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x77000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D4
    CMP      R0, #0x88000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x99000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D5
    CMP      R0, #0xAA000000
    BLNE     reg2_error_loopf
    CMP      R1, #0xBB000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D6
    CMP      R0, #0xFF000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x11000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D7
    CMP      R0, #0x22000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x33000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D8
    CMP      R0, #0x44000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x55000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D9
    CMP      R0, #0x66000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x77000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D10
    CMP      R0, #0x88000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x99000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D11
    CMP      R0, #0xAA000000
    BLNE     reg2_error_loopf
    CMP      R1, #0xBB000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D12
    CMP      R0, #0xFF000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x11000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D13
    CMP      R0, #0x22000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x33000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D14
    CMP      R0, #0x44000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x55000000
    BLNE     reg2_error_loopf
    VMOV     R0, R1, D15
    CMP      R0, #0x66000000
    BLNE     reg2_error_loopf
    CMP      R1, #0x77000000
    BLNE     reg2_error_loopf

    /* Restore the registers that were clobbered by the test. */
    POP     {R0-R1}

    /* VFP register test passed.  Jump to the core register test. */
    B       reg2_loopf_pass

reg2_error_loopf:
    /* If this line is hit then a VFP register value was found to be
    incorrect. */
    B        0xDEACFE

reg2_loopf_pass:

    CMP      R0, #0xFF000000
    BLNE     reg2_error_loop
    CMP      R1, #0x11000000
    BLNE     reg2_error_loop
    CMP      R2, #0x22000000
    BLNE     reg2_error_loop
    CMP      R3, #0x33000000
    BLNE     reg2_error_loop
    CMP      R4, #0x44000000
    BLNE     reg2_error_loop
    CMP      R5, #0x55000000
    BLNE     reg2_error_loop
    CMP      R6, #0x66000000
    BLNE     reg2_error_loop
    CMP      R7, #0x77000000
    BLNE     reg2_error_loop
    CMP      R8, #0x88000000
    BLNE     reg2_error_loop
    CMP      R9, #0x99000000
    BLNE     reg2_error_loop
    CMP      R10, #0xAA000000
    BLNE     reg2_error_loop
    CMP      R11, #0xBB000000
    BLNE     reg2_error_loop
    CMP      R12, #0xCC000000
    BLNE     reg2_error_loop
    CMP      R14, #0xEE000000
    BLNE     reg2_error_loop

    /* Everything passed, increment the loop counter. */
    PUSH    { R0-R1 }
    LDR     R0, =loopCounter
    LDR     R1, [R0, #+0x4]
    ADD     R1, R1, #1
    STR     R1, [R0, #+0x4]
    POP     { R0-R1 }

    /* Delay for 0x200 ticks before running again */
    PUSH    { R0-R4, R12, R14 }
    MOV     R0, #0x200
    /* Unprivileged tasks need to use the MPU wrapped functions.
     * Change this to be BLX vTaskDelay to trigger a pre-fetch abort. */
    BLX     MPU_vTaskDelay
    POP     { R0-R4, R12, R14 }

    /* Start again. */
    B     reg2_loop

reg2_error_loop:
    /* If this line is hit then there was an error in a core register value.
    The loop ensures the loop counter stops incrementing. */
    B     0xDEACFF
    NOP

/* End of file */
.end


