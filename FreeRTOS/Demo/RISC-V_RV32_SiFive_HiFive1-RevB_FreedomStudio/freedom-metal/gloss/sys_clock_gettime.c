#define _POSIX_MONOTONIC_CLOCK 200809L
#define _POSIX_TIMERS
#include <errno.h>
#include <metal/drivers/riscv_cpu.h>
#include <metal/machine.h>
#include <time.h>

#ifdef MTIME_RATE_HZ_DEF
#undef MTIME_RATE_HZ
#define MTIME_RATE_HZ MTIME_RATE_HZ_DEF
#endif

#ifndef MTIME_RATE_HZ
#define MTIME_RATE_HZ 32768
#endif

#if !defined(mtime_interrupt_controller) &&                                    \
    defined(__METAL_DT_RISCV_CLINT0_HANDLE)
#define mtime_interrupt_controller __METAL_DT_RISCV_CLINT0_HANDLE
#endif

#if !defined(mtime_interrupt_controller) &&                                    \
    defined(__METAL_DT_SIFIVE_CLIC0_HANDLE)
#define mtime_interrupt_controller __METAL_DT_SIFIVE_CLIC0_HANDLE
#endif

int clock_getres(clockid_t clk_id, struct timespec *res) {
    switch (clk_id) {
    case CLOCK_MONOTONIC:
        res->tv_sec = 0;
        res->tv_nsec = 1000000000 / MTIME_RATE_HZ;
        return 0;
        break;
    default:
        errno = EINVAL;
        return -1;
    }
}

int clock_gettime(clockid_t clk_id, struct timespec *tp) {
    unsigned long long ticks;

    switch (clk_id) {
    case CLOCK_MONOTONIC:
        mtime_interrupt_controller->vtable->command_request(
            mtime_interrupt_controller, METAL_TIMER_MTIME_GET, &ticks);
        tp->tv_sec = ticks / MTIME_RATE_HZ;
        tp->tv_nsec = ((ticks % (MTIME_RATE_HZ)) * 1000000000) / MTIME_RATE_HZ;
        return 0;
        break;
    default:
        errno = EINVAL;
        return -1;
    }
}

int clock_settime(clockid_t clk_id, const struct timespec *tp) {
    errno = EINVAL;
    return -1;
}
