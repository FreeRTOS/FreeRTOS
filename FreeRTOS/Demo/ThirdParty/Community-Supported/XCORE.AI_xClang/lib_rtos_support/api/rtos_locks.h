// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#ifndef RTOS_LOCKS_H_
#define RTOS_LOCKS_H_

#if !defined(__XC__)

#include "rtos_support_rtos_config.h"
#include <xcore/lock.h>
#include <xcore/assert.h>

#ifndef RTOS_LOCK_COUNT
#error You must define RTOS_LOCK_COUNT in rtos_support_rtos_config.h
#endif

#if RTOS_LOCK_COUNT == 0
/* If the RTOS does not need any locks
 * that is fine, but the IRQ functions still
 * need one. */
#undef RTOS_LOCK_COUNT
#define RTOS_LOCK_COUNT 1
#endif

#if RTOS_LOCK_COUNT > 4
#error XCORE does not support more than 4 hardware locks
#endif

void rtos_locks_initialize(void);

inline int rtos_lock_acquire(int lock_id)
{
    extern lock_t rtos_locks[RTOS_LOCK_COUNT];
    extern int rtos_lock_counters[RTOS_LOCK_COUNT];

    xassert(lock_id >= 0 && lock_id < RTOS_LOCK_COUNT);
    if (rtos_locks[lock_id] != -1) {
        lock_acquire(rtos_locks[lock_id]);
        rtos_lock_counters[lock_id]++;
    }

    return rtos_lock_counters[lock_id];
}

/**
 *
 * \warning Be careful not to release a lock that the calling
 *          core does not own or else bad things will happen.
 *          Defining RTOS_LOCKS_SAFE to 1 will enable a check
 *          to see the lock is owned. If it is not it will
 *          throw an exception.
 */
inline int rtos_lock_release(int lock_id)
{
    extern lock_t rtos_locks[RTOS_LOCK_COUNT];
    extern int rtos_lock_counters[RTOS_LOCK_COUNT];
    int counter = 0;

    xassert(lock_id >= 0 && lock_id < RTOS_LOCK_COUNT);
    if (rtos_locks[lock_id] != -1) {
        #if RTOS_LOCKS_SAFE
            lock_acquire(rtos_locks[lock_id]);
            xassert(rtos_lock_counters[lock_id] > 0);
        #endif
        counter = --rtos_lock_counters[lock_id];
        if (counter == 0) {
            lock_release(rtos_locks[lock_id]);
        }
    }

    return counter;
}

#endif // !defined(__XC__)

#endif /* RTOS_LOCKS_H_ */
