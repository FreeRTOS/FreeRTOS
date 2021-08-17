/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__TIME_H
#define METAL__TIME_H

#include <time.h>
#ifndef __SEGGER_LIBC__
#include <sys/time.h>
#endif

/*!
 * @file time.h
 * @brief API for dealing with time
 */

int metal_gettimeofday(struct timeval *tp, void *tzp);

time_t metal_time(void);

#endif
