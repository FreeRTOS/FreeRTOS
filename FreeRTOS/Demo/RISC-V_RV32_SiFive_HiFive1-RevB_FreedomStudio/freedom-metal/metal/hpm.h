/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__HPM_H
#define METAL__HPM_H

#include <metal/cpu.h>

/*! @brief Macros for valid Event IDs */
#define METAL_HPM_EVENTID_8 (1UL << 8)
#define METAL_HPM_EVENTID_9 (1UL << 9)
#define METAL_HPM_EVENTID_10 (1UL << 10)
#define METAL_HPM_EVENTID_11 (1UL << 11)
#define METAL_HPM_EVENTID_12 (1UL << 12)
#define METAL_HPM_EVENTID_13 (1UL << 13)
#define METAL_HPM_EVENTID_14 (1UL << 14)
#define METAL_HPM_EVENTID_15 (1UL << 15)
#define METAL_HPM_EVENTID_16 (1UL << 16)
#define METAL_HPM_EVENTID_17 (1UL << 17)
#define METAL_HPM_EVENTID_18 (1UL << 18)
#define METAL_HPM_EVENTID_19 (1UL << 19)
#define METAL_HPM_EVENTID_20 (1UL << 20)
#define METAL_HPM_EVENTID_21 (1UL << 21)
#define METAL_HPM_EVENTID_22 (1UL << 22)
#define METAL_HPM_EVENTID_23 (1UL << 23)
#define METAL_HPM_EVENTID_24 (1UL << 24)
#define METAL_HPM_EVENTID_25 (1UL << 25)
#define METAL_HPM_EVENTID_26 (1UL << 26)
#define METAL_HPM_EVENTID_27 (1UL << 27)
#define METAL_HPM_EVENTID_28 (1UL << 28)
#define METAL_HPM_EVENTID_29 (1UL << 29)
#define METAL_HPM_EVENTID_30 (1UL << 30)
#define METAL_HPM_EVENTID_31 (1UL << 31)

/*! @brief Macros for valid Event Class */
#define METAL_HPM_EVENTCLASS_0 (0UL)
#define METAL_HPM_EVENTCLASS_1 (1UL)
#define METAL_HPM_EVENTCLASS_2 (2UL)
#define METAL_HPM_EVENTCLASS_3 (3UL)
#define METAL_HPM_EVENTCLASS_4 (4UL)
#define METAL_HPM_EVENTCLASS_5 (5UL)
#define METAL_HPM_EVENTCLASS_6 (6UL)
#define METAL_HPM_EVENTCLASS_7 (7UL)
#define METAL_HPM_EVENTCLASS_8 (8UL)

/*! @brief Enums for available HPM counters */
typedef enum {
    METAL_HPM_CYCLE = 0,
    METAL_HPM_TIME = 1,
    METAL_HPM_INSTRET = 2,
    METAL_HPM_COUNTER_3 = 3,
    METAL_HPM_COUNTER_4 = 4,
    METAL_HPM_COUNTER_5 = 5,
    METAL_HPM_COUNTER_6 = 6,
    METAL_HPM_COUNTER_7 = 7,
    METAL_HPM_COUNTER_8 = 8,
    METAL_HPM_COUNTER_9 = 9,
    METAL_HPM_COUNTER_10 = 10,
    METAL_HPM_COUNTER_11 = 11,
    METAL_HPM_COUNTER_12 = 12,
    METAL_HPM_COUNTER_13 = 13,
    METAL_HPM_COUNTER_14 = 14,
    METAL_HPM_COUNTER_15 = 15,
    METAL_HPM_COUNTER_16 = 16,
    METAL_HPM_COUNTER_17 = 17,
    METAL_HPM_COUNTER_18 = 18,
    METAL_HPM_COUNTER_19 = 19,
    METAL_HPM_COUNTER_20 = 20,
    METAL_HPM_COUNTER_21 = 21,
    METAL_HPM_COUNTER_22 = 22,
    METAL_HPM_COUNTER_23 = 23,
    METAL_HPM_COUNTER_24 = 24,
    METAL_HPM_COUNTER_25 = 25,
    METAL_HPM_COUNTER_26 = 26,
    METAL_HPM_COUNTER_27 = 27,
    METAL_HPM_COUNTER_28 = 28,
    METAL_HPM_COUNTER_29 = 29,
    METAL_HPM_COUNTER_30 = 30,
    METAL_HPM_COUNTER_31 = 31
} metal_hpm_counter;

/*! @brief Initialize hardware performance monitor counters.
 * @param cpu The CPU device handle.
 * @return 0 If no error.*/
int metal_hpm_init(struct metal_cpu *cpu);

/*! @brief Disables hardware performance monitor counters.
 *         Note - Disabled HPM counters may reduce power consumption.
 * @param cpu The CPU device handle.
 * @return 0 If no error.*/
int metal_hpm_disable(struct metal_cpu *cpu);

/*! @brief Set events which will cause the specified counter to increment.
 *         Counter will start incrementing from the moment events are set.
 * @param cpu The CPU device handle.
 * @param counter Hardware counter to be incremented by selected events.
 * @param bitmask Bit-mask to select events for a particular counter,
 *                refer core reference manual for selection of events.
 *                Event bit mask is partitioned as follows:
 *                [XLEN-1:8] - Event selection mask [7:0] - Event class
 * @return 0 If no error.*/
int metal_hpm_set_event(struct metal_cpu *cpu, metal_hpm_counter counter,
                        unsigned int bitmask);

/*! @brief Get events selection mask set for specified counter.
 * @param cpu The CPU device handle.
 * @param counter Hardware counter.
 * @return Event selection bit mask. refer core reference manual for details.*/
unsigned int metal_hpm_get_event(struct metal_cpu *cpu,
                                 metal_hpm_counter counter);

/*! @brief Clear event selector bits as per specified bit-mask.
 * @param cpu The CPU device handle.
 * @param counter Hardware counter.
 * @return 0 If no error.*/
int metal_hpm_clr_event(struct metal_cpu *cpu, metal_hpm_counter counter,
                        unsigned int bitmask);

/*! @brief Enable counter access to next lower privilege mode.
 * @param cpu The CPU device handle.
 * @param counter Hardware counter.
 * @return 0 If no error.*/
int metal_hpm_enable_access(struct metal_cpu *cpu, metal_hpm_counter counter);

/*! @brief Disable counter access to next lower privilege mode.
 * @param cpu The CPU device handle.
 * @param counter Hardware counter.
 * @return 0 If no error.*/
int metal_hpm_disable_access(struct metal_cpu *cpu, metal_hpm_counter counter);

/*! @brief Reads current value of specified hardware counter.
 *         Note: 'mtime' register is memory mapped into CLINT block.
 *                Use CLINT APIs to access this register.
 * @param cpu The CPU device handle.
 * @param counter Hardware counter.
 * @return Current value of hardware counter on success, 0 on failure.*/
unsigned long long metal_hpm_read_counter(struct metal_cpu *cpu,
                                          metal_hpm_counter counter);

/*! @brief Clears off specified counter.
 * @param cpu The CPU device handle.
 * @param counter Hardware counter.
 * @return 0 If no error.*/
int metal_hpm_clear_counter(struct metal_cpu *cpu, metal_hpm_counter counter);

#endif
