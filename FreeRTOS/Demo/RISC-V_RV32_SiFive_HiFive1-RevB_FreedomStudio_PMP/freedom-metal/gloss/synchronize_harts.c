/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/machine/platform.h>
#include <metal/io.h>
#include <metal/cpu.h>

#define METAL_REG(base, offset)   (((unsigned long)(base) + (offset)))
#define METAL_REGW(base, offset)  (__METAL_ACCESS_ONCE((__metal_io_u32 *)METAL_REG((base), (offset))))
#define METAL_MSIP(base, hart)    (METAL_REGW((base),4*(hart)))

/*
 * _synchronize_harts() is called by crt0.S to cause harts > 0 to wait for
 * hart 0 to finish copying the datat section, zeroing the BSS, and running
 * the libc contstructors.
 */
void _synchronize_harts() {
#if __METAL_DT_MAX_HARTS > 1

    int hart = metal_cpu_get_current_hartid();
    uintptr_t msip_base = 0;

    /* Get the base address of the MSIP registers */
#ifdef __METAL_DT_RISCV_CLINT0_HANDLE
    msip_base = __metal_driver_sifive_clint0_control_base(__METAL_DT_RISCV_CLINT0_HANDLE);
    msip_base += METAL_RISCV_CLINT0_MSIP_BASE;
#elif __METAL_DT_RISCV_CLIC0_HANDLE
    msip_base = __metal_driver_sifive_clic0_control_base(__METAL_DT_RISCV_CLIC0_HANDLE);
    msip_base += METAL_RISCV_CLIC0_MSIP_BASE;
#else
#warning No handle for CLINT or CLIC found, harts may be unsynchronized after init!
#endif

    /* Disable machine interrupts as a precaution */
    __asm__ volatile("csrc mstatus, %0" :: "r" (METAL_MSTATUS_MIE));

    if (hart == 0) {
        /* Hart 0 waits for all harts to set their MSIP bit */
        for (int i = 1 ; i < __METAL_DT_MAX_HARTS; i++) {
            while (METAL_MSIP(msip_base, i) == 0) ;
        }

        /* Hart 0 clears everyone's MSIP bit */
        for (int i = 1 ; i < __METAL_DT_MAX_HARTS; i++) {
            METAL_MSIP(msip_base, i) = 0;
        }
    } else {
        /* Other harts set their MSIP bit to indicate they're ready */
        METAL_MSIP(msip_base, hart) = 1;
        __asm__ volatile ("fence w,rw");

        /* Wait for hart 0 to clear the MSIP bit */
        while (METAL_MSIP(msip_base, hart) == 1) ;
    }

#endif /* __METAL_DT_MAX_HARTS > 1 */
}

