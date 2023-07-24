// Copyright (c) 2019, XMOS Ltd, All rights reserved

    .text
    .issue_mode  single
    .globl  prvRegisterCheck_asm1
    .align 4
    .type   prvRegisterCheck_asm1,@function
    .cc_top prvRegisterCheck_asm1.function,prvRegisterCheck_asm1

    #define NSTACKWORDS 9

/*
void prvRegisterCheck_asm1( void );
*/
prvRegisterCheck_asm1:
    ENTSP_lu6 NSTACKWORDS

    stw r4, sp[1]
    stw r5, sp[2]
    stw r6, sp[3]
    stw r7, sp[4]
    stw r8, sp[5]
    stw r9, sp[6]
    stw r10, sp[7]
    stw r11, sp[8]

    /* Load known values */
    /* Since eq can only do immediates 0-11, load values 0-11*/
    ldc r0, 9
    ldc r1, 3
    ldc r2, 2
    ldc r3, 11
    ldc r4, 4
    ldc r5, 6
    ldc r6, 10
    ldc r7, 8
    ldc r8, 7
    ldc r9, 1
    ldc r10, 0
    ldc r11, 5

forever:
    /* Verify values are unchanged */
    /* Since we cannot compare without clobbering, we will use r11 for
    all comparisons and restore its value */

    eq r11, r0, 9
        bf r11, failure
    eq r11, r1, 3
        bf r11, failure
    eq r11, r2, 2
        bf r11, failure
    eq r11, r3, 11
        bf r11, failure
    eq r11, r4, 4
        bf r11, failure
    eq r11, r5, 6
        bf r11, failure
    eq r11, r6, 10
        bf r11, failure
    eq r11, r7, 8
        bf r11, failure
    eq r11, r8, 7
        bf r11, failure
    eq r11, r9, 1
        bf r11, failure
    eq r11, r10, 0
        bf r11, failure

    /* r11 should equal 1; therefore, adding 4 to it should
    make it 5, the expected value, for this final comparison */
    add r11, r11, 4
    eq r11, r11, 5
        bf r11, failure

    /* Repeat */
    bu forever

failure:
    ldw r4, sp[1]
    ldw r5, sp[2]
    ldw r6, sp[3]
    ldw r7, sp[4]
    ldw r8, sp[5]
    ldw r9, sp[6]
    ldw r10, sp[7]
    ldw r11, sp[8]

    retsp NSTACKWORDS

    // RETURN_REG_HOLDER
    .cc_bottom prvRegisterCheck_asm1.function
    .set    prvRegisterCheck_asm1.nstackwords,NSTACKWORDS
    .globl  prvRegisterCheck_asm1.nstackwords
    .set    prvRegisterCheck_asm1.maxcores,1
    .globl  prvRegisterCheck_asm1.maxcores
    .set    prvRegisterCheck_asm1.maxtimers,0
    .globl  prvRegisterCheck_asm1.maxtimers
    .set    prvRegisterCheck_asm1.maxchanends,0
    .globl  prvRegisterCheck_asm1.maxchanends
.Ltmp0:
    .size   prvRegisterCheck_asm1, .Ltmp0-prvRegisterCheck_asm1

    .issue_mode  single
