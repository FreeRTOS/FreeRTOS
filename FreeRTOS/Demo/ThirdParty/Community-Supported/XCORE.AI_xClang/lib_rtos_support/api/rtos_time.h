// Copyright 2020-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#ifndef RTOS_TIME_H_
#define RTOS_TIME_H_

#include <stdint.h>

/**
 * \defgroup RTOS time standard periods
 *
 * These values represent the period of various
 * standard interrupt frequencies that may be
 * used as the parameter for rtos_time_increment().
 * @{
 */
/** Period of 1000 Hz in microseconds in Q12 format */
#define RTOS_TICK_PERIOD_1000_HZ   4096000  /* 1000000 / 1000  * 2^12 */
/** Period of 100 Hz in microseconds in Q12 format */
#define RTOS_TICK_PERIOD_100_HZ   40960000  /* 1000000 / 100   * 2^12 */
/** Period of 32768 Hz in microseconds in Q12 format */
#define RTOS_TICK_PERIOD_32768_HZ   125000  /* 1000000 / 32768 * 2^12 */
/**@}*/

/**
 * Converts a frequency in hertz to its period in
 * microseconds in Q12 format that may be used as
 * the parameter for rtos_time_increment().
 */
#define RTOS_TICK_PERIOD(hz) ((uint32_t)(((uint64_t)1000000 << 12) / (hz)))

/**
 * Structure representing the time.
 */
typedef struct {
    uint64_t seconds;      /**< The number of seconds. */
    uint32_t microseconds; /**< The number of microseconds. */
} rtos_time_t;


/**
 * This function increments the current time by
 * \p tick_period microseconds.
 *
 * It is intended to be called by a periodic
 * interrupt, either the system tick interrupt
 * or an RTC interrupt, at a frequency of 1 /
 * \p tick_period.
 *
 * \param[in] tick_period The number of microseconds
 * to increment the current time by. It must be
 * formatted as a fixed point number with 12
 * fractional bits.
 */
void rtos_time_increment(uint32_t tick_period);

/**
 * This function sets the current time to \p new_time.
 *
 * \param[in] new_time The value to set the current time to.
 *                     See rtos_time_t.
 */
void rtos_time_set(rtos_time_t new_time);

/**
 * This function returns the current time.
 *
 * \returns the current time. See rtos_time_t.
 */
rtos_time_t rtos_time_get(void);

#endif /* RTOS_TIME_H_ */
