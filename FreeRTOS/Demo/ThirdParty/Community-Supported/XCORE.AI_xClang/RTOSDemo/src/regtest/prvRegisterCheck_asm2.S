// Copyright (c) 2019, XMOS Ltd, All rights reserved

    .text
    .issue_mode  single
    .globl  prvRegisterCheck_asm2
    .align 4
    .type   prvRegisterCheck_asm2,@function
    .cc_top prvRegisterCheck_asm2.function,prvRegisterCheck_asm2

    #define NSTACKWORDS 9

/*
void prvRegisterCheck_asm2( void );
*/
prvRegisterCheck_asm2:
    ENTSP_lu6 NSTACKWORDS

    stw r4, sp[1]
    stw r5, sp[2]
    stw r6, sp[3]
    stw r7, sp[4]
    stw r8, sp[5]
    stw r9, sp[6]
    stw r10, sp[7]
    stw r11, sp[8]

    /* load known values */
    ldc r0, 0
    mkmsk r1, 1
    mkmsk r2, 2
    mkmsk r3, 3
    mkmsk r4, 4
    mkmsk r5, 5
    mkmsk r6, 6
    mkmsk r7, 7
    mkmsk r8, 8
    mkmsk r9, 16
    mkmsk r10, 24
    mkmsk r11, 32

forever:
    /* verify values are unchanged */
    /* Since we cannot compare without clobbering, we will use r0 for
    all comparisons and restore its value */

    mkmsk r0, 1
    eq r0, r0, r1
        bt r0, .L0
            bu failure
.L0:
    mkmsk r0, 2
    eq r0, r0, r2
        bt r0, .L1
            bu failure
.L1:
    mkmsk r0, 3
    eq r0, r0, r3
        bt r0, .L2
            bu failure
.L2:
    mkmsk r0, 4
    eq r0, r0, r4
        bt r0, .L3
            bu failure
.L3:
    mkmsk r0, 5
    eq r0, r0, r5
        bt r0, .L4
            bu failure
.L4:
    mkmsk r0, 6
    eq r0, r0, r6
        bt r0, .L5
            bu failure
.L5:
    mkmsk r0, 7
    eq r0, r0, r7
        bt r0, .L6
            bu failure
.L6:
    mkmsk r0, 8
    eq r0, r0, r8
        bt r0, .L7
            bu failure
.L7:
    mkmsk r0, 16
    eq r0, r0, r9
        bt r0, .L8
            bu failure
.L8:
    mkmsk r0, 24
    eq r0, r0, r10
        bt r0, .L9
            bu failure
.L9:
    mkmsk r0, 32
    eq r0, r0, r11
        bt r0, .L10
            bu failure
.L10:
    /* r0 should equal 1; therefore, subtracting 1 to it should
    make it 0, the expected value, for this final comparison */
    sub r0, r0, 1
    eq r0, r0, 0
        bt r0, .L11
            bu failure
.L11:
    /* repeat */
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
    .cc_bottom prvRegisterCheck_asm2.function
    .set    prvRegisterCheck_asm2.nstackwords,NSTACKWORDS
    .globl  prvRegisterCheck_asm2.nstackwords
    .set    prvRegisterCheck_asm2.maxcores,1
    .globl  prvRegisterCheck_asm2.maxcores
    .set    prvRegisterCheck_asm2.maxtimers,0
    .globl  prvRegisterCheck_asm2.maxtimers
    .set    prvRegisterCheck_asm2.maxchanends,0
    .globl  prvRegisterCheck_asm2.maxchanends
.Ltmp0:
    .size   prvRegisterCheck_asm2, .Ltmp0-prvRegisterCheck_asm2

    .issue_mode  single
