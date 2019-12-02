/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 *
 */

/**
 *	@file		ff_time.h
 *	@ingroup	TIME
 *
 *	Provides a means for receiving the time on any platform.
 **/

#ifndef _FF_TIME_H_
#define _FF_TIME_H_

#include <time.h>

#include "FreeRTOSFATConfig.h"

/* _HT_
The following declarations and functions may be moved to a common directory?
 */
typedef struct xTIME_STRUCT
{
	int tm_sec;   /* Seconds */
	int tm_min;   /* Minutes */
	int tm_hour;  /* Hour (0--23) */
	int tm_mday;  /* Day of month (1--31) */
	int tm_mon;   /* Month (0--11) */
	int tm_year;  /* Year (calendar year minus 1900) */
	int tm_wday;  /* Weekday (0--6; Sunday = 0) */
	int tm_yday;  /* Day of year (0--365) */
	int tm_isdst; /* 0 if daylight savings time is not in effect) */
} FF_TimeStruct_t;

/* Equivalent of time() : returns the number of seconds after 1-1-1970. */
time_t FreeRTOS_time( time_t *pxTime );

/* Equivalent of mktime() : calculates the number of seconds after 1-1-1970. */
time_t FreeRTOS_mktime( const FF_TimeStruct_t *pxTimeBuf );

/* Equivalent of gmtime_r() : Fills a 'struct tm'. */
FF_TimeStruct_t *FreeRTOS_gmtime_r( const time_t *pxTime, FF_TimeStruct_t *pxTimeBuf );

/**
 *	@public
 *	@brief	A TIME and DATE object for FreeRTOS+FAT. A FreeRTOS+FAT time driver must populate these values.
 *
 **/
typedef struct
{
	uint16_t Year;		/* Year	(e.g. 2009). */
	uint16_t Month;		/* Month	(e.g. 1 = Jan, 12 = Dec). */
	uint16_t Day;		/* Day	(1 - 31). */
	uint16_t Hour;		/* Hour	(0 - 23). */
	uint16_t Minute;	/* Min	(0 - 59). */
	uint16_t Second;	/* Second	(0 - 59). */
} FF_SystemTime_t;

/*---------- PROTOTYPES */

int32_t	FF_GetSystemTime(FF_SystemTime_t *pxTime);

#endif

