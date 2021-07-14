/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

/* This code executes before _start, which is contained inside the C library.
 * In embedded systems we want to ensure that _enter, which contains the first
 * code to be executed, can be loaded at a specific address.  To enable this
 * feature we provide the '.text.metal.init.enter' section, which is
 * defined to have the first address being where execution should start. */
.section .text.metal.init.enter
.global _enter
_enter:
    .cfi_startproc

    /* Inform the debugger that there is nowhere to backtrace past _enter. */
    .cfi_undefined ra

    /* The absolute first thing that must happen is configuring the global
     * pointer register, which must be done with relaxation disabled because
     * it's not valid to obtain the address of any symbol without GP
     * configured.  The C environment might go ahead and do this again, but
     * that's safe as it's a fixed register. */
.option push
.option norelax
    la gp, __global_pointer$
.option pop

    /* trap over the chicken bit register clearing, aloe & fe310 dont have it */
    la t0, 1f
    csrw mtvec, t0
    /* chicken bit is enable if core are sifive series. */
    la t0, __metal_chicken_bit
    beqz t0, 1f
    /* If set, always clear the feature disable register for all cores series */
    csrwi 0x7C1, 0
.align 4
1:
    /* Set up a simple trap vector to catch anything that goes wrong early in
     * the boot process. */
    la t0, early_trap_vector
    csrw mtvec, t0

    /* There may be pre-initialization routines inside the MBI code that run in
     * C, so here we set up a C environment. First we set up a stack pointer,
     * which is left as a weak reference in order to allow initialization
     * routines that do not need a stack to be set up to transparently be
     * called. */
    .weak __metal_stack_pointer
    la sp, __metal_stack_pointer

   /* The METAL is designed for a bare-metal environment and therefore is expected
    * to define its own stack pointer. We also align the stack pointer here
    * because the only RISC-V ABI that's currently defined, mandates 16-byte
    * stack alignment. */

    bne sp, zero, 1f
    la sp, _sp
1:
    /* Increment by hartid number of stack sizes */
    csrr a0, mhartid
    li t0, 0
    la t1, __stack_size
1:
    andi sp, sp, -16
    beq t0, a0, 1f
    add sp, sp, t1
    addi t0, t0, 1
    j 1b
1:

    /* Check for an initialization routine and call it if one exists, otherwise
     * just skip over the call entirely.   Note that __metal_initialize isn't
     * actually a full C function, as it doesn't end up with the .bss or .data
     * segments having been initialized.  This is done to avoid putting a
     * burden on systems that can be initialized without having a C environment
     * set up. */
    la ra, __metal_before_start
    beqz ra, 1f
    jalr ra
1:

    /* At this point we can enter the C runtime's startup file.  The arguments
     * to this function are designed to match those provided to the SEE, just
     * so we don't have to write another ABI. */
    csrr a0, mhartid
    li a1, 0
    li a2, 0
    call _start

    /* If we've made it back here then there's probably something wrong.  We
     * allow the METAL to register a handler here. */
    .weak __metal_after_main
    la ra, __metal_after_main
    beqz ra, 1f
    jalr ra
1:

    /* If that handler returns then there's not a whole lot we can do.  Just
     * try to make some noise. */
     la t0, 1f
     csrw mtvec, t0
1:
     lw t1, 0(x0)
     j 1b

    .cfi_endproc

/* The GCC port might not emit a __register_frame_info symbol, which eventually
 * results in a weak undefined reference that eventually causes crash when it
 * is dereference early in boot.  We really shouldn't need to put this here,
 * but to deal with what I think is probably a bug in the linker script I'm
 * going to leave this in for now.  At least it's fairly cheap :) */
.weak __register_frame_info
.global __register_frame_info
.section .text.metal.init.__register_frame_info
__register_frame_info:
    .cfi_startproc
    ret
    .cfi_endproc
