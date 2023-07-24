// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#include <xs1.h>

#include "rtos_support.h"

/*
 * This is indexed by the logical core ID
 * returned by get_logical_core_id().
 * It returns the RTOS core ID which is
 * guaranteed to be between 0 and the number of
 * cores used by the RTOS - 1.
 *
 * Not static so that it can be accessed directly by
 * RTOS functions written in assembly.
 */
int rtos_core_map[RTOS_MAX_CORE_COUNT] = {0};

/*
 * This is indexed by the RTOS core ID
 * which must be between 0 and the number of
 * cores used by the RTOS - 1.
 * It returns the logical core ID  which is
 * returned by get_logical_core_id().
 */
static int rtos_core_map_reverse[RTOS_MAX_CORE_COUNT];

/*
 * The number of RTOS cores that have been initialized.
 *
 * TODO: I don't think this needs to be volatile anymore
 * since it is only read through rtos_core_count(), which
 * should always read the value in memory.
 */
static /*volatile*/ int rtos_core_init_count;

/*
 * Registers a new RTOS core. Returns its core ID.
 * Note this is not the necessarily the same as the
 * ID returned by get_logical_core_id().
 */
int rtos_core_register(void)
{
    int core_id;

    core_id = (int) get_logical_core_id();

    rtos_lock_acquire(0);
    {
        rtos_core_map[core_id] = rtos_core_init_count;
        rtos_core_map_reverse[rtos_core_init_count] = core_id;
        core_id = rtos_core_init_count++;
    }
    rtos_lock_release(0);

    return core_id;
}

/* Note, always returns 0 before the scheduler is started. */
int rtos_core_id_get(void)
{
    return rtos_core_map[get_logical_core_id()];
}

int rtos_logical_core_id_get(int core_id)
{
    xassert(core_id < rtos_core_init_count);
    return rtos_core_map_reverse[ core_id ];
}

int rtos_core_count(void)
{
    return rtos_core_init_count;
}
