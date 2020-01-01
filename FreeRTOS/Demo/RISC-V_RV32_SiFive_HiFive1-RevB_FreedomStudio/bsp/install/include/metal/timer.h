/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__TIMER_H
#define METAL__TIMER_H

/*!
 * @file timer.h
 * @brief API for reading and manipulating the machine timer
 */

/*!
 * @brief Read the machine cycle count
 * @param hartid The hart ID to read the cycle count of
 * @param cyclecount The variable to hold the value
 * @return 0 upon success
 */
int metal_timer_get_cyclecount(int hartid, unsigned long long *cyclecount);

/*!
 * @brief Get the machine timebase frequency
 * @param hartid The hart ID to read the timebase of
 * @param timebase The variable to hold the value
 * @return 0 upon success
 */
int metal_timer_get_timebase_frequency(int hartid, unsigned long long *timebase);

/*! 
 * @brief Set the machine timer tick interval in seconds
 * @param hartid The hart ID to read the timebase of
 * @param second The number of seconds to set the tick interval to
 * @return 0 upon success
 */
int metal_timer_set_tick(int hartid, int second);

#endif
