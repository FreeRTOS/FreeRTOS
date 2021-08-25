/*******************************************************************************
 * Copyright 2021 Microchip Corporation.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/***************************************************************************
 * @file mss_utils.S
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief utilities used by mpfs-hal startup code
 *
 */
  .section .text.init,"ax", %progbits
  .align 3

/***********************************************************************************
 *
 * pdma_transfer
 * Only used by the mpfs hal. App code uses the provided driver.
 *
 *   a0 = dest
 *   a1 = src
 *   a2 = length
 *   a3 = PDMA Base Address - 0x3000000 + (0x01000 * PDMA_CHANNEL)
 */
    .globl  pdma_transfer
    .type   pdma_transfer, @function
pdma_transfer:
    mv  t1,a0
    mv t0, a3           // Base address
    li t1, 1
    sw t1, 0(t0)        // claim
    li t1, 0
    sw t1, 4(t0)        // read[31:28]/write[27:24] size 0=>1byte, 1 =>2 bytes etx
    mv t1, a2           // SIZE
    sd t1, 8(t0)        // bytes
    mv t1, a0           // dest address
    sd t1, 16(t0)       // dest
    mv t1, a1           // source address
    sd t1, 24(t0)       // src
    li t1, 0xff000000
    sw t1, 4(t0)        // full speed copy
    li t1, 3
    sw t1, 0(t0)        // start transfer
    fence
    ret

/***********************************************************************************
 *
 * pdma_transfer_complete
 * Loops until transfer complete
 * Only used by the mpfs hal. App code uses the provided driver.
 *
 *    a0 = PDMA Base Address - 0x3000000 + (0x01000 * PDMA_CHANNEL)
 */
    //
    .globl  pdma_transfer_complete
    .type   pdma_transfer_complete, @function
pdma_transfer_complete:
    mv t0, a0           // Base address
1: // wait for completion
    lw t1, 0(t0)
    andi t1, t1, 2
    bnez t1, 1b
    // release DMA
    sw zero, 0(t0)
    ret


 /***********************************************************************************
 *
 * memfill() - fills memory, alternate to lib function when not available
 */
    // memfill helper function:
    //  a0 = dest
    //  a1 = value to fill
    //  a2 = length
    .globl  memfill
    .type   memfill, @function
memfill:
    mv  t1,a0
    mv  t2,a1
    beqz    a2,2f
1:
    sb  t2,0(t1)
    addi    a2,a2,-1
    addi    t1,t1,1
    bnez    a2,1b
2:
    ret

/***********************************************************************************
 *
 * The following config_copy() symbol overrides the weak symbol in the HAL and does
 * a safe copy of HW config data
 */
    // config_copy helper function:
    //  a0 = dest
    //  a1 = src
    //  a2 = length
    .globl  config_copy
    .type   config_copy, @function
config_copy:
    mv  t1,a0
    beqz    a2,2f
1:
    lb  t2,0(a1)
    sb  t2,0(t1)
    addi    a2,a2,-1
    addi    t1,t1,1
    addi    a1,a1,1
    bnez    a2,1b
2:
    ret

 /***********************************************************************************
 *
 * config_16_copy () Copies a word at a time, used when copying to contigous registers
 */
    // config_16_copy helper function:
    //  a0 = dest
    //  a1 = src
    //  a2 = length
    .globl  config_16_copy
    .type   config_16_copy, @function
config_16_copy:
    mv  t1,a0
    beqz    a2,2f
1:
    lh  t2,0(a1)
    sh  t2,0(t1)
    addi    a2,a2,-2
    addi    t1,t1,2
    addi    a1,a1,2
    bnez    a2,1b
2:
    ret

/***********************************************************************************
 *
 * config_32_copy () Copies a word at a time, used when copying to contigous registers
 */
    // config_copy helper function:
    //  a0 = dest
    //  a1 = src
    //  a2 = length
    .globl  config_32_copy
    .type   config_32_copy, @function
config_32_copy:
    mv  t1,a0
    beqz    a2,2f
1:
    lw  t2,0(a1)
    sw  t2,0(t1)
    addi    a2,a2,-4
    addi    t1,t1,4
    addi    a1,a1,4
    bnez    a2,1b
2:
    ret

 /***********************************************************************************
 *
 * config_64_copy - copying using 64 bit loads, addresses must be on 64 bit boundary
 */
    // config_64_copy helper function:
    //  a0 = dest
    //  a1 = src
    //  a2 = length
    .globl  config_64_copy
    .type   config_64_copy, @function
config_64_copy:
    mv  t1,a0
    beqz    a2,2f
1:
    ld  t2,0(a1)
    sd  t2,0(t1)
    addi    a2,a2,-8
    addi    t1,t1,8
    addi    a1,a1,8
    bnez    a2,1b
2:
    ret


