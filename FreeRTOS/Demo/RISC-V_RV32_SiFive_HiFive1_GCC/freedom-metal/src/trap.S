/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#define METAL_MSTATUS_MIE_SHIFT 8
#define METAL_MSTATUS_MPP_M     3
#define METAL_MSTATUS_MPP_SHIFT 11

#define METAL_MTVEC_MODE_MASK   3

/* void _metal_trap(int ecode)
 *
 * Trigger a machine-mode trap with exception code ecode
 */
.global _metal_trap
.type _metal_trap, @function

_metal_trap:

    /* Store the instruction which called _metal_trap in mepc */
    addi t0, ra, -1
    csrw mepc, t0

    /* Set mcause to the desired exception code */
    csrw mcause, a0

    /* Read mstatus */
    csrr t0, mstatus

    /* Set MIE=0 */
    li t1, -1
    xori t1, t1, METAL_MSTATUS_MIE_SHIFT
    and t0, t0, t1

    /* Set MPP=M */
    li t1, METAL_MSTATUS_MPP_M
    slli t1, t1, METAL_MSTATUS_MPP_SHIFT
    or t0, t0, t1

    /* Write mstatus */
    csrw mstatus, t0

    /* Read mtvec */
    csrr t0, mtvec

    /*
     * Mask the mtvec MODE bits
     * Exceptions always jump to mtvec.BASE regradless of the vectoring mode.
     */
    andi t0, t0, METAL_MTVEC_MODE_MASK

    /* Jump to mtvec */
    jr t0

