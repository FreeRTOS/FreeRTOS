/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 ****************************************************************************
 * (C) 2003 - Rolf Neugebauer - Intel Research Cambridge
 * (C) 2005 - Grzegorz Milos - Intel Research Cambridge
 ****************************************************************************
 *
 *        File: time.h
 *      Author: Rolf Neugebauer (neugebar@dcs.gla.ac.uk)
 *     Changes: Grzegorz Milos (gm281@cam.ac.uk)
 *              Robert Kaiser (kaiser@informatik.fh-wiesbaden.de)
 *              
 *        Date: Jul 2003, changes: Jun 2005, Sep 2006
 * 
 * Environment: Xen Minimal OS
 * Description: Time and timer functions
 *
 ****************************************************************************
 */

#ifndef _MINIOS_TIME_H_
#define _MINIOS_TIME_H_

/*
 * System Time
 * 64 bit value containing the nanoseconds elapsed since boot time.
 * This value is adjusted by frequency drift.
 * NOW() returns the current time.
 * The other macros are for convenience to approximate short intervals
 * of real time into system time 
 */
typedef int64_t s_time_t;
#define NOW()                   ((s_time_t)monotonic_clock())
#define SECONDS(_s)             (((s_time_t)(_s))  * 1000000000UL )
#define TENTHS(_ts)             (((s_time_t)(_ts)) * 100000000UL )
#define HUNDREDTHS(_hs)         (((s_time_t)(_hs)) * 10000000UL )
#define MILLISECS(_ms)          (((s_time_t)(_ms)) * 1000000UL )
#define MICROSECS(_us)          (((s_time_t)(_us)) * 1000UL )
#define Time_Max                ((s_time_t) 0x7fffffffffffffffLL)
#define FOREVER                 Time_Max
#define NSEC_TO_USEC(_nsec)     ((_nsec) / 1000UL)
#define NSEC_TO_MSEC(_nsec)     ((_nsec) / 1000000ULL)
#define NSEC_TO_SEC(_nsec)      ((_nsec) / 1000000000ULL)

/* wall clock time  */
typedef long time_t;
typedef long suseconds_t;

#include <sys/time.h>

#ifdef HAVE_LIBC
#include_next <time.h>
#endif

/* prototypes */
void     init_time(void);
void     fini_time(void);
s_time_t get_s_time(void);
s_time_t get_v_time(void);
uint64_t monotonic_clock(void);
void     block_domain(s_time_t until);

#endif /* _MINIOS_TIME_H_ */
