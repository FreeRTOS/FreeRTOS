/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#ifndef _TIME_H_
#define _TIME_H_

/********************************************************************************
 * Included Files
 ********************************************************************************/
#include <stdint.h>

/********************************************************************************
 * Pre-processor Definitions
 ********************************************************************************/

/* Clock tick of the system (frequency Hz).
 *
 * NOTE: This symbolic name CLK_TCK has been removed from the standard.  It is
 * replaced with CLOCKS_PER_SEC.  Both are defined here.
 *
 * The default value is 1Mz
 */
#define CLK_TCK           (1000000)
#define CLOCKS_PER_SEC    (1000000)

#define NSEC_PER_SEC        1000000000
#define USEC_PER_SEC        1000000
#define NSEC_PER_USEC       1000
#define USEC_PER_MSEC       1000
#define MSEC_PER_SEC        1000
#define NSEC_PER_MSEC       1000000
#define TICK2MSEC(tick)     ((tick)* (1000 / CLOCKS_PER_SEC))

/* CLOCK_REALTIME refers to the standard time source.  For most
 * implementations, the standard time source is the system timer interrupt.
 * However, if the platform supports an RTC, then the standard time source
 * will be the RTC for the clock_gettime() and clock_settime() interfaces
 * (the system timer is still the time source for all of the interfaces).
 *
 * CLOCK_REALTIME represents the machine's best-guess as to the current
 * wall-clock, time-of-day time. This means that CLOCK_REALTIME can jump
 * forward and backward as the system time-of-day clock is changed.
 */

#define CLOCK_REALTIME     0

/* Clock that cannot be set and represents monotonic time since some
 * unspecified starting point. It is not affected by changes in the
 * system time-of-day clock.
 */
#define CLOCK_MONOTONIC  1

/* This is a flag that may be passed to the timer_settime() function */

#define TIMER_ABSTIME      1

/* Local time is the same as gmtime in this implementation */
#define localtime_r(c,r)   gmtime_r(c,r)

/********************************************************************************
 * Public Types
 ********************************************************************************/
/* Scalar types */

#if !defined(__time_t_defined) && !defined(_TIME_T_DECLARED)
typedef int32_t  time_t;         /* Holds time in seconds */
#define __time_t_defined
#define _TIME_T_DECLARED
#endif
#if !defined(__clockid_t_defined) && !defined(_CLOCKID_T_DECLARED)
typedef uint8_t   clockid_t;      /* Identifies one time base source */
#define __clockid_t_defined
#define _CLOCKID_T_DECLARED
#endif

/* struct timespec is the standard representation of time as seconds and
 * nanoseconds.
 */

#ifndef _SYS__TIMESPEC_H_
#define _SYS__TIMESPEC_H_
struct timespec {
    time_t tv_sec;                   /* Seconds */
    long   tv_nsec;                  /* Nanoseconds */
};
#endif

/* struct tm is the standard representation for "broken out" time.
 *
 * REVISIT: This structure could be packed better using uint8_t's and
 * uint16_t's.  The standard definition does, however, call out type int for
 * all of the members.  NOTE: Any changes to this structure must be also be
 * reflected in struct rtc_time defined in include/nuttx/timers/rtc.h; these
 * two structures must be cast compatible.
 */

struct tm {
    int tm_sec;     /* Seconds (0-61, allows for leap seconds) */
    int tm_min;     /* Minutes (0-59) */
    int tm_hour;    /* Hours (0-23) */
    int tm_mday;    /* Day of the month (1-31) */
    int tm_mon;     /* Month (0-11) */
    int tm_year;    /* Years since 1900 */
    int tm_wday;    /* Day of the week (0-6) */
    int tm_yday;    /* Day of the year (0-365) */
    int tm_isdst;   /* Non-0 if daylight savings time is in effect */
};

/* Struct itimerspec is used to define settings for an interval timer */

#ifndef _SYS__TIMESPEC_H_
struct itimerspec {
    struct timespec it_value;    /* First time */
    struct timespec it_interval; /* and thereafter */
};
#endif

/* forward reference (defined in signal.h) */

struct sigevent;

/********************************************************************************
 * Public Data
 ********************************************************************************/

#undef EXTERN
#if defined(__cplusplus)
#define EXTERN extern "C"
extern "C"
{
#else
#define EXTERN extern
#endif

/********************************************************************************
 * Public Function Prototypes
 ********************************************************************************/
int clock_timer_init(void);
int clock_timer_uninit(void);
int clock_timer_start(void);
int clock_timer_stop(void);
int clock_gettime(clockid_t clockid, struct timespec *tp);

time_t mktime(struct tm *tp);
struct tm *gmtime_r(const time_t *timep, struct tm *result);

#undef EXTERN
#if defined(__cplusplus)
}
#endif
#endif  /*_SYS_TIME_H_*/
