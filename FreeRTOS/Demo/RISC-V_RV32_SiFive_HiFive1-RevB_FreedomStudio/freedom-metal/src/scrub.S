/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Scrub memory with zeroes
 */

/* Keep it in metal.init section with _enter */
.section .text.metal.init.scrub
/* Disable linker relaxation */
.option push
.option norelax

/* Function to zero-scrub specified memory
 * a0 : start address for zero-scrub
 * a1 : size memory region size in bytes
 */
.global metal_mem_scrub
.type metal_mem_scrub, @function
metal_mem_scrub:

    /* Disable machine interrupts,
    restore previous mstatus value at exit */
    li      a3, 8
    csrrc   t1, mstatus, a3

#if __riscv_xlen == 32
    addi    t0, x0, 4
1:
    blt     a1, t0, 2f
    andi    a2, a0, 3
    beqz    a2, 3f
2:
    sb      x0, 0(a0)
    addi    a0, a0, 1
    addi    a1, a1, -1
    bgtz    a1, 1b
    csrw    mstatus, t1
    ret
3:
    sw      x0, 0(a0)
    addi    a0, a0, 4
    addi    a1, a1, -4
    bgtz    a1, 1b
    csrw    mstatus, t1
    ret
#else
    addi    t0, x0, 8
1:
    blt     a1, t0, 2f
    andi    a2, a0, 7
    beqz    a2, 3f
2:
    sb      x0, 0(a0)
    addi    a0, a0, 1
    addi    a1, a1, -1
    bgtz    a1, 1b
    csrw    mstatus, t1
    ret
3:
    sd      x0, 0(a0)
    addi    a0, a0, 8
    addi    a1, a1, -8
    bgtz    a1, 1b
    csrw    mstatus, t1
    ret
#endif

.type __metal_memory_scrub, @function
__metal_memory_scrub:
/* Zero out specified memory regions */
1:
#if __riscv_xlen == 32
    sw      x0, 0(t1)
    addi    t1, t1, 4
    blt     t1, t2, 1b
#else
    sd      x0, 0(t1)
    addi    t1, t1, 8
    blt     t1, t2, 1b
#endif
    ret

/*
 * Initialize memories to zero
 * This must be called before setting up any stack(s)
 */
.weak __metal_eccscrub_bit
.weak __metal_before_start
.global __metal_before_start
.type __metal_before_start, @function
__metal_before_start:
    /* Save caller ra */
    mv      s0, ra

    la      t0, __metal_eccscrub_bit
    beqz    t0, skip_scrub

    la      t0, __metal_boot_hart
    csrr    a5, mhartid

    /* Disable machine interrupts to be safe */
    li      a3, 8
    csrc    mstatus, a3

    /* Zero out per hart stack */
    mv      t1, sp
    la      t2, __stack_size
    add     t2, t2, sp
    beq     t1, t2, 1f
    jal     __metal_memory_scrub
1:
    bne     a5, t0, skip_scrub

    /* Zero out data segment */
    la      t1, metal_segment_data_target_start
    la      t2, metal_segment_data_target_end
    beq     t1, t2, 1f
    jal     __metal_memory_scrub
1:
    /* Zero out itim memory */
    la      t1, metal_segment_itim_target_start
    la      t2, metal_segment_itim_target_end
    beq     t1, t2, skip_scrub
    jal     __metal_memory_scrub

skip_scrub:
    /* Restore caller ra */
    mv      ra, s0
    ret

.option pop
