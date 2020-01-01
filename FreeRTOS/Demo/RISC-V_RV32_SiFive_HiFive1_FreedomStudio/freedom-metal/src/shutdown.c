/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/shutdown.h>

extern __inline__ void __metal_shutdown_exit(const struct __metal_shutdown *sd, int code);

#if defined(__METAL_DT_SHUTDOWN_HANDLE)
void metal_shutdown(int code)
{
    __metal_shutdown_exit(__METAL_DT_SHUTDOWN_HANDLE, code);
}
#else
#pragma message("There is no defined shutdown mechanism, metal_shutdown() will spin.")
void metal_shutdown(int code)
{
    while (1) {
      __asm__ volatile ("nop");
    }
}
#endif
