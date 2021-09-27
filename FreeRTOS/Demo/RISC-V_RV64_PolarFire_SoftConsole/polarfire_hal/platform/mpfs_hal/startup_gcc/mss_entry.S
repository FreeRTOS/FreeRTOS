/*******************************************************************************
 * Copyright 2019-2021 Microchip Corporation.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file entry.S
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief entry functions.
 *
 */

#include "../common/bits.h"
#include "../common/encoding.h"
#include "../common/mss_mtrap.h"
#include "system_startup_defs.h"
#include "mpfs_hal_config/mss_sw_config.h"

  .option norvc
  .section .text.init,"ax", %progbits
  .globl reset_vector
  .globl _start

reset_vector:
_start:
#if (IMAGE_LOADED_BY_BOOTLOADER == 0)
    /*
     * clear the Return Address Stack
     */
    call .clear_ras
    /* Setup trap handler */
    la a4, trap_vector
    csrw mtvec, a4          # initalise machine trap vector address
    /* Make sure that mtvec is updated before continuing */
    1:
    csrr    a5, mtvec
    bne a4, a5, 1b
    /* Disable and clear all interrupts */
    li a2,  MSTATUS_MIE
    csrc mstatus, a2        # clear interrupt enable bit
    csrw mie, zero
    csrw mip, zero
    # Init delegation registers, mideleg, medeleg, if a U54
    # These are not initialised by the hardware and come up in a random state
    csrr a0, mhartid
    beqz a0, .skip_e51
    csrw mideleg, 0
    csrw medeleg, 0
.skip_e51:
    # mscratch must be init to zero- we are not using scratch memory
    csrw mscratch, zero
    csrw mcause, zero
    csrw mepc, zero
    /*
     * clear PMP enables
     */
    csrw pmpcfg0, zero
    csrw pmpcfg2, zero
    /*
     * clear regs
     */
    li  x1, 0
    li  x2, 0
    li  x3, 0
    li  x4, 0
    li  x5, 0
    li  x6, 0
    li  x7, 0
    li  x8, 0
    li  x9, 0
    li  x10,0
    li  x11,0
    li  x12,0
    li  x13,0
    li  x14,0
    li  x15,0
    li  x16,0
    li  x17,0
    li  x18,0
    li  x19,0
    li  x20,0
    li  x21,0
    li  x22,0
    li  x23,0
    li  x24,0
    li  x25,0
    li  x26,0
    li  x27,0
    li  x28,0
    li  x29,0
    li  x30,0
    li  x31,0

    # enable FPU and accelerator if present, setting ignored on E51
    li t0, MSTATUS_FS | MSTATUS_XS
    csrs mstatus, t0

    # Init floating point control register to zero
    # skip if e51
    csrr a0, mhartid
    beqz a0, .no_float
#ifdef __riscv_flen
    fscsr x0
#endif
.no_float:

     # make sure XLEN agrees with compilation choice, if not will loop here
.LxlenCheck:
    csrr t0, misa
#if __riscv_xlen == 64
    bltz t0, .LxlenPass
#else
    bgez t0, .LxlenPass
#endif
    j .LxlenCheck
.LxlenPass:

    # initialize global pointer, global data
    # The __global_pointer is allocated in the linker script. It points to a
    # location 2k after sdata start as the offsets used in the gp are +/- 2k
    # See https://www.sifive.com/blog/2017/08/28/all-aboard-part-3-linker-relaxation-in-riscv-toolchain/
    # see: http://www.rowleydownload.co.uk/arm/documentation/gnu/as/RISC_002dV_002dDirectives.html
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    # get core id
    csrr a0, mhartid
    li a1,  0
    beq a0, a1, .hart0
    li a1,  1
    beq a0, a1, .hart1
    li a1,  2
    beq a0, a1, .hart2
    li a1,  3
    beq a0, a1, .hart3
    li a1,  4
    beq a0, a1, .hart4

.hart0:
    la a4, __stack_bottom_h0$  # keep bottom of stack in a5 so we can init later
    la sp, __stack_top_h0$
    j .continue
.hart1:
    la a4, __stack_bottom_h1$  # keep bottom of stack in a5 so we can init later
    la sp, __stack_top_h1$
    j .continue
.hart2:
    la a4, __stack_bottom_h2$  # keep bottom of stack in a5 so we can init later
    la sp, __stack_top_h2$
    j .continue
.hart3:
    la a4, __stack_bottom_h3$  # keep bottom of stack in a5 so we can init later
    la sp, __stack_top_h3$
    j .continue
.hart4:
    la a4, __stack_bottom_h4$  # keep bottom of stack in a5 so we can init later
    la sp, __stack_top_h4$

.continue:
    # clear HLS and stack
    mv  a5, sp
.init_stack:
    #csrw mepc, zero
    STORE x0, 0(a4)
    add a4, a4, __SIZEOF_POINTER__
    blt a4, a5, .init_stack
    # Allocate some space at top of stack for the HLS
    addi sp, sp, -HLS_DEBUG_AREA_SIZE
    # HLS grows up from new top of stack
    mv tp, sp
    # get core id
    csrr a0, mhartid
    li a1, MPFS_HAL_FIRST_HART
    bne a0, a1, .LOtherHartstoWFI
    # clear the common heap
    la  a4, __heap_start
    la  a5, __heap_end
.init_heap:
    #csrw mepc, zero
    STORE x0, 0(a4)
    add a4, a4, __SIZEOF_POINTER__
    blt a4, a5, .init_heap
    #
    # clear DTIM - this is required to stop memory errors on initial access by
    # cache
    # Also, stops x propagation in simulation, when cache/stack reads unused
    # area
    #
    li a2, MPFS_HAL_CLEAR_MEMORY
    beq x0, a2, .skip_mem_clear
    call    .clear_dtim
    call    .clear_l2lim
.skip_mem_clear:
    /*
     * Clear bus error unit accrued register on start-up
     * This is cleared by the first hart only
     */
    la a4,0x01700020UL
    sb   x0, 0(a4)
    la a4,0x01701020UL
    sb   x0, 0(a4)
    la a4,0x01702020UL
    sb   x0, 0(a4)
    la a4,0x01703020UL
    sb   x0, 0(a4)
    la a4,0x01704020UL
    sb   x0, 0(a4)
    # now core MPFS_HAL_FIRST_HART jumps to main_first_hart
.main_hart:
    # pass HLS address
    mv  a0, tp
    j main_first_hart
.LoopForeverMain:
    #in case of return, loop forever. nop's added so can be seen in debugger
    nop
    nop
    j .LoopForeverMain

.LOtherHartstoWFI:
    li a2,  MSTATUS_MIE
    csrc mstatus, a2       # clear interrupt enable bit
    csrw mie, zero
    csrw mip, zero
    li a2, MIP_MSIP
    csrw mie, a2           # Set MSIE bit to receive IPI. This needs to be
                           # enabled- otherwise stays in wfi.
                           # Other interrupts appera to bring out of wfi,even if
                           # not enabled.
    #
    # Wait here until main hart is up and running
    #
    li a3, HLS_MAIN_HART_STARTED
    la a1, (__stack_top_h0$ - HLS_DEBUG_AREA_SIZE)
.wait_main_hart:
    LWU a2, 0(a1)
    bne a3, a2, .wait_main_hart
    # Flag we are here to the main hart
    li a1, HLS_OTHER_HART_IN_WFI
    sw a1, 0(tp)
    /* flush the instruction cache */
    fence.i
.LwaitOtherHart:
    # We assume wfi instruction will be run before main hart attampts to take
    # out of wfi
    wfi
    # Only start if MIP_MSIP is set - the wfi will ensure this, but adding
    # breakpoints in the debugger (halt)
    # will wakeup wfi, so the following code will make sure we remain here until
    # we get a software interrupt
    csrr a2, mip
    andi a2, a2, MIP_MSIP
    beqz a2, .LwaitOtherHart
    /* Disable and clear all interrupts- should be only a sw interrupt */
    li a2,  MSTATUS_MIE
    csrc mstatus, a2        # clear interrupt enable bit
    csrw mie, zero
    csrw mip, zero
    # set marker as to where we are
    li a1, HLS_OTHER_HART_PASSED_WFI
    sw a1, 0(tp)
    # pass HLS address
    mv  a0, tp
    j main_other_hart
.LoopForeverOther:
    #in case of return, loop forever. nop's added so can be seen in debugger
    nop
    nop
    j .LoopForeverOther

#else /* IMAGE_LOADED_BY_BOOTLOADER == 1 */

/***********************************************************************************
 *The program has been loaded by a bootloader
 * a0 - contains the hart ID
 * a1 - contains pointer to bootloader -Hart Local Storage, for this hart.
 */
_start_non_bootloader_image:
    /* ebreak called at the start of the program if required when debuging.   */
    /* DEBUG_EBREAK_AT_START is set to one in the debug build, 0 in the       */
    /* release build                                                          */
    /* uncomment the 3 lines below if you want to use this method to for      */
    /* debugging                                                              */
    /* li a2, DEBUG_EBREAK_AT_START
    beq x0, a2, 1f
    ebreak */
1:
    /* store the value here received from boot-loader */
    /* a0 will always contain the hart ID */
    /* If a1 is null, boot-loader is not passing pointer to the HLS */
    /* If this is the case, point HLS to out own and fill with hart ID */
    /* Setup trap handler */
    /* we are currently only supporting mmode */
    /* m-mode/s-mode set-up option will be added here */
    la a4, trap_vector
    csrw mtvec, a4          # initalise machine trap vector address
    /* Make sure that mtvec is updated before continuing */
2:
    csrr    a5, mtvec
    bne a4, a5, 2b
    /* Disable and clear all interrupts */
    /* assumption is this has been done by the Boot-loader */
    # Init delegation registers, mideleg, medeleg, if a U54
    # These are not initialised by the hardware and come up in a random state
    # mhartid is in a0
    beqz a0, 3f
    csrw mideleg, 0
    csrw medeleg, 0
3:
    # mscratch must be init to zero- we are not using scratch memory
    csrw mscratch, zero
    csrw mcause, zero
    csrw mepc, zero

    # Init floating point control register to zero
    # skip if e51
    # mhartid is in a0
    beqz a0, 1f
#ifdef __riscv_flen
    fscsr x0
#endif
1:  # no float
    # make sure XLEN agrees with compilation choice, if not will loop here
    csrr t0, misa
#if __riscv_xlen == 64
    bltz t0, 2f
#else
    bgez t0, 2f
#endif
    j 1b
2:
    # initialize global pointer, global data
    # The __global_pointer is allocated in the linker script. It points to a
    # location 2k after sdata start as the offsets used in the gp are +/- 2k
    # See https://www.sifive.com/blog/2017/08/28/all-aboard-part-3-linker-relaxation-in-riscv-toolchain/
    # see: http://www.rowleydownload.co.uk/arm/documentation/gnu/as/RISC_002dV_002dDirectives.html
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    la a4, __app_stack_bottom  # keep bottom of stack in a5 so we can init later
    la a5, __app_stack_top
    la sp, __app_stack_top
1:
    STORE x0, 0(a4)
    add a4, a4, __SIZEOF_POINTER__
    blt a4, a5, 1b
    # clear the common heap
    la  a4, __heap_start
    la  a5, __heap_end
2:
    STORE x0, 0(a4)
    add a4, a4, __SIZEOF_POINTER__
    blt a4, a5, 2b
    # check if HLS passed by BL, if not allocate one here
    bnez a1, 1f
    # Allocate some space at top of stack for the HLS, as HLS mem not passed
    addi sp, sp, -HLS_DEBUG_AREA_SIZE
    # HLS grows up from new top of stack
    mv tp, sp
    mv a0, tp
    j u54_single_hart
1:
    # pass HLS address from the boot-loader
    mv a0, a1
    j u54_single_hart
2:
    # in case of return, loop forever. nop's added so can be seen in debugger
    nop
    nop
    j 2b
#endif /* IMAGE_LOADED_BY_BOOTLOADER */

/******************************************************************************/
/******************************interrupt handeling below here******************/
/******************************************************************************/

trap_vector:
    # The mscratch register is an XLEN-bit read/write register dedicated for use by machine mode.
    # Typically, it is used to hold a pointer to a machine-mode hart-local context space and swapped
    # with a user register upon entry to an M-mode trap handler.
    # In this implementation, we are noty using HLS
    # csrrw sp, mscratch, sp                    #copy sp to mscratch, and mscrath to sp

    addi sp, sp, -INTEGER_CONTEXT_SIZE     # moves sp down stack to make I
                                           # INTEGER_CONTEXT_SIZE area
    # Preserve the registers.
    STORE sp, 2*REGBYTES(sp)               # sp
    STORE a0, 10*REGBYTES(sp)              # save a0,a1 in the created CONTEXT
    STORE a1, 11*REGBYTES(sp)
    STORE ra, 1*REGBYTES(sp)
    STORE gp, 3*REGBYTES(sp)
    STORE tp, 4*REGBYTES(sp)
    STORE t0, 5*REGBYTES(sp)
    STORE t1, 6*REGBYTES(sp)
    STORE t2, 7*REGBYTES(sp)
    STORE s0, 8*REGBYTES(sp)
    STORE s1, 9*REGBYTES(sp)
    STORE a2,12*REGBYTES(sp)
    STORE a3,13*REGBYTES(sp)
    STORE a4,14*REGBYTES(sp)
    STORE a5,15*REGBYTES(sp)
    STORE a6,16*REGBYTES(sp)
    STORE a7,17*REGBYTES(sp)
    STORE s2,18*REGBYTES(sp)
    STORE s3,19*REGBYTES(sp)
    STORE s4,20*REGBYTES(sp)
    STORE s5,21*REGBYTES(sp)
    STORE s6,22*REGBYTES(sp)
    STORE s7,23*REGBYTES(sp)
    STORE s8,24*REGBYTES(sp)
    STORE s9,25*REGBYTES(sp)
    STORE s10,26*REGBYTES(sp)
    STORE s11,27*REGBYTES(sp)
    STORE t3,28*REGBYTES(sp)
    STORE t4,29*REGBYTES(sp)
    STORE t5,30*REGBYTES(sp)
    STORE t6,31*REGBYTES(sp)
    # Invoke the handler.
    mv a0, sp                          # a0 <- regs
    # Please note: mtval is the newer name for register mbadaddr
    # If you get a compile failure here, use the newer name
    # At this point (2019), both are supported in latest compiler
    # older compiler versions only support mbadaddr, so going with this.
    # See: https://github.com/riscv/riscv-gcc/issues/133
    csrr a1, mbadaddr                 # useful for anaysis when things go wrong
    csrr a2, mepc
    jal trap_from_machine_mode

restore_regs:
    # Restore all of the registers.
    LOAD ra, 1*REGBYTES(sp)
    LOAD gp, 3*REGBYTES(sp)
    LOAD tp, 4*REGBYTES(sp)
    LOAD t0, 5*REGBYTES(sp)
    LOAD t1, 6*REGBYTES(sp)
    LOAD t2, 7*REGBYTES(sp)
    LOAD s0, 8*REGBYTES(sp)
    LOAD s1, 9*REGBYTES(sp)
    LOAD a0,10*REGBYTES(sp)
    LOAD a1,11*REGBYTES(sp)
    LOAD a2,12*REGBYTES(sp)
    LOAD a3,13*REGBYTES(sp)
    LOAD a4,14*REGBYTES(sp)
    LOAD a5,15*REGBYTES(sp)
    LOAD a6,16*REGBYTES(sp)
    LOAD a7,17*REGBYTES(sp)
    LOAD s2,18*REGBYTES(sp)
    LOAD s3,19*REGBYTES(sp)
    LOAD s4,20*REGBYTES(sp)
    LOAD s5,21*REGBYTES(sp)
    LOAD s6,22*REGBYTES(sp)
    LOAD s7,23*REGBYTES(sp)
    LOAD s8,24*REGBYTES(sp)
    LOAD s9,25*REGBYTES(sp)
    LOAD s10,26*REGBYTES(sp)
    LOAD s11,27*REGBYTES(sp)
    LOAD t3,28*REGBYTES(sp)
    LOAD t4,29*REGBYTES(sp)
    LOAD t5,30*REGBYTES(sp)
    LOAD t6,31*REGBYTES(sp)
    LOAD sp, 2*REGBYTES(sp)
    addi sp, sp, +INTEGER_CONTEXT_SIZE  # moves sp up stack to reclaim
                                        # INTEGER_CONTEXT_SIZE area
    mret

 /*****************************************************************************/
 /******************************interrupt handeling above here*****************/
 /*****************************************************************************/

.enable_sw_int:
    li a2, MIP_MSIP
    csrw mie, a2            # Set MSIE bit to receive IPI
    li a2,  MSTATUS_MIE
    csrs mstatus, a2        # enable interrupts
    /* flush the instruction cache */
    fence.i
    ret

 /***********************************************************************************
 *
 * The following init_memory() symbol overrides the weak symbol in the HAL and does
 * a safe copy of RW data and clears zero-init memory
 *
 */
    // zero_section helper function:
    //       a0 = exec_start_addr
    //       a1 = exec_end_addr
    //
    .globl  zero_section
    .type   zero_section, @function
zero_section:
    bge a0, a1, .zero_section_done
    sd  zero, (a0)
    addi    a0, a0, 8
    j   zero_section
.zero_section_done:
    ret

    // zero_section helper function:
    //       a0 = exec_start_addr
    //       a1 = exec_end_addr
    //       a2 = start count
    //
    .globl  count_section
    .type   count_section, @function
count_section:
    beq a0, a1, .count_section_done
    sd  a2, (a0)
    addi    a0, a0, 8
    addi    a2, a2, 8
    j   count_section
.count_section_done:
    ret

    // copy_section helper function:
    //  a0 = load_addr
    //  a1 = exec_start_addr
    //  a2 = exec_end_addr
    .globl  copy_section
    .type   copy_section, @function
copy_section:
    beq a1, a0, .copy_section_done // if load_addr == exec_start_addr, goto copy_section_done
.check_if_copy_section_done:
    beq a1, a2, .copy_section_done // if offset != length, goto keep_copying
.keep_copying:
    ld  a3, 0(a0)                  // val = *load_addr
    sd  a3, 0(a1)                  // *exec_start_addr = val;
    addi    a0, a0, 8              // load_addr = load_addr + 8
    addi    a1, a1, 8              // exec_start_addr = exec_start_addr + 8
    j   .check_if_copy_section_done
.copy_section_done:
    ret


/***********************************************************************************
 *
 * The following copy_switch_code() symbol overrides the weak symbol in the HAL and does
 * a safe copy of HW config data
 */
    .globl  copy_switch_code
    .type   copy_switch_code, @function
copy_switch_code:
    la      a5, __sc_start           // a5 = __sc_start
    la      a4, __sc_load            // a4 = __sc_load
    beq a5,a4,.copy_switch_code_done // if a5 == a4, goto copy_switch_code_done
    la      a3, __sc_end             // a3 = __sc_end
    beq a5,a3,.copy_switch_code_done // if a5 == a3, goto copy_switch_code_done
.copy_switch_code_loop:
    lw  a2,0(a4)                     // a2 = *a4
    sw  a2,0(a5)                     // *a5 = a2
    addi    a5,a5,4                  // a5+=4
    addi    a4,a4,4                  // a4+=4

    bltu    a5,a3,.copy_switch_code_loop // if a5 < a3, goto copy_switch_code_loop
.copy_switch_code_done:
    ret

/*******************************************************************************
 *
 */
#define START__OF_LIM 0x08000000
#define END__OF_LIM   0x08200000
#define START__OF_DTM 0x01000000
#define END__OF_DTM   0x01002000


.clear_l2lim:
    // Clear the LIM
    //
    // On reset, the first 15 ways are L2 and the last way is cache
    // We can initialize all, as cache write through to DDR is blocked
    // until DDR in initialized, so will have no effect other than clear ECC
    //
    // NOTE: we need to check if we are debugging from LIM,if so do not
    // initialize.
    //
    la a2, _start
    la  a4, 0x08000000          # start of LIM address
    and a2, a2, a4
    bnez a2, .done_clear
    la  a5, 0x08200000          # end of LIM address
    j   1f
.clear_dtim:
    //
    // Clear the E51 DTIM to prevent any ECC memory errors on initial access
    //
    la  a4, 0x01000000          # DTIM start
    la  a5, 0x01002000          # DTIM end
1:
    // common loop used by both .clear_l2lim and .clear_dtim
    sd   x0, 0(a4)
    add a4, a4, __SIZEOF_POINTER__
    blt a4, a5, 1b
.done_clear:
    ret

/*
 * record_ecc_error_counts on reset
 * These are non-zero in the coreplex.
 * Can be checked later on to see if values have changed
 *      a0 = mECCDataFailCount save address
        a1 = mECCDataCorrectionCount save address
        a2 = mECCDirFixCount save address
 */
.record_ecc_error_counts:
    # Store initial ECC errors
    #define mECCDataFailCount               0x02010168U
    la  a5, mECCDataFailCount
    mv  a4, a0// eg. Use stat of DTIM in not used for anything else  0x01000100
    lw  t2,0(a5)
    sw  t2,0(a4)
    #define mECCDataCorrectionCount         0x02010148U
    la  a5, mECCDataCorrectionCount
    mv  a4, a1// eg. Use stat of DTIM in not used for anything else 0x01000110
    lw  t2,0(a5)
    sw  t2,0(a4)
    #define mECCDirFixCount                 0x02010108u
    la  a5, mECCDirFixCount
    mv  a4, a2// eg. Use stat of DTIM in not used for anything else 0x01000120
    lw  t2,0(a5)
    sw  t2,0(a4)
    ret

/*
 * clear_ras , clear_ras_2_deep
 * Two deep function calls.
 * Used to clear the interal processor Return Address Stack
 * This is belt and braces, may not be required
 */
.clear_ras:
    mv a5, x1
    nop
    call .clear_ras_2_deep
    nop
    nop
    nop
    nop
    nop
    nop
    mv  x1, a5
    ret

.clear_ras_2_deep:
    nop
    nop
    nop
    nop
    nop
    nop
    ret

