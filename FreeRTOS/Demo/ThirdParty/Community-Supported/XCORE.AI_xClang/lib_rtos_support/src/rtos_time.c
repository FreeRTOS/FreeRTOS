// Copyright 2020-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#include "rtos_time.h"
#include "rtos_locks.h"

static rtos_time_t current_time;

#define US_FRACTIONAL_BITS 12
#define ONE_SECOND_US (1000000 << US_FRACTIONAL_BITS)

void rtos_time_increment(uint32_t tick_period)
{
    rtos_lock_acquire(0);
    {
        current_time.microseconds += tick_period;
        if (current_time.microseconds >= ONE_SECOND_US) {
            current_time.microseconds -= ONE_SECOND_US;
            current_time.seconds++;
        }
    }
    rtos_lock_release(0);
}

void rtos_time_set(rtos_time_t new_time)
{
    new_time.microseconds <<= US_FRACTIONAL_BITS;

    rtos_lock_acquire(0);
    {
        current_time = new_time;
    }
    rtos_lock_release(0);
}

rtos_time_t rtos_time_get(void)
{
    rtos_time_t tmp_time;

    rtos_lock_acquire(0);
    {
        tmp_time = current_time;
    }
    rtos_lock_release(0);

    tmp_time.microseconds >>= US_FRACTIONAL_BITS;

    return tmp_time;
}
