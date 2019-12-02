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

#include <stdio.h>
#include <time.h>
#include <string.h>

#include "FreeRTOS.h"
#include "task.h"

#include "ff_time.h"

/**
 *	@file		ff_time.c
 *	@ingroup	TIME
 *
 *	@defgroup	TIME Real-Time Clock Interface
 *	@brief		Allows FreeRTOS+FAT to time-stamp files.
 *
 *	Provides a means for receiving the time on any platform.
 **/

#if( ffconfigTIME_SUPPORT != 0 )	/* This if-block spans the rest of the source file. */
/**
 *	@public
 *	@brief	Populates an FF_SystemTime_t object with the current time from the system.
 *
 *	The developer must modify this function so that it is suitable for their platform.
 *	The function must return with 0, and if the time is not available all elements of the
 *	FF_SystemTime_t object must be zero'd, as in the examples provided.
 *
 *	@param	pxTime	Pointer to an FF_TIME object.
 *
 *	@return	Always returns 0.
 **/

int32_t	FF_GetSystemTime( FF_SystemTime_t *pxTime )
{
	FF_TimeStruct_t xTimeStruct;

	/* Fetch the current time. */
	time_t secs = FreeRTOS_time( NULL );

	/* Fill the fields in 'xTimeStruct'. */
	FreeRTOS_gmtime_r( &secs, &xTimeStruct );

	pxTime->Hour = xTimeStruct.tm_hour;
	pxTime->Minute = xTimeStruct.tm_min;
	pxTime->Second = xTimeStruct.tm_sec;
	pxTime->Day = xTimeStruct.tm_mday;
	pxTime->Month = xTimeStruct.tm_mon + 1;
	pxTime->Year = xTimeStruct.tm_year + 1900;

	return 0;
}	/* FF_GetSystemTime() */
/*-----------------------------------------------------------*/

/*
 * FreeRTOS+FAT
 * Time conversion functions:
 *
 * FF_TimeStruct_t *FreeRTOS_gmtime_r( const time_t *pxTime, FF_TimeStruct_t *pxTimeBuf )
 * time_t FreeRTOS_mktime(FF_TimeStruct_t *pxTimeBuf)
*/

#define GMTIME_FIRST_YEAR		( 1970 )
#define TM_STRUCT_FIRST_YEAR	( 1900 )
#define SECONDS_PER_MINUTE		( 60 )
#define MINUTES_PER_HOUR		( 60 )
#define HOURS_PER_DAY			( 24 )
#define SECONDS_PER_HOUR		( MINUTES_PER_HOUR * SECONDS_PER_MINUTE )
#define SECONDS_PER_DAY			( HOURS_PER_DAY * SECONDS_PER_HOUR )

/* The first weekday in 'FF_TimeStruct_t' is Sunday. */
#define WEEK_DAY_SUNDAY			0
#define WEEK_DAY_MONNDAY 		1
#define WEEK_DAY_TUESDAY 		2
#define WEEK_DAY_WEDNESDAY		3
#define WEEK_DAY_THURSDAY		4
#define WEEK_DAY_FRIDAY			5
#define WEEK_DAY_SATURDAY		6

/* Make a bitmask with a '1' for each 31-day month. */
#define _MM(month)			( 1u << ( month - 1 ) )
#define	MASK_LONG_MONTHS	( _MM(1) | _MM(3) | _MM(5) | _MM(7) | _MM(8) | _MM(10) | _MM(12) )

#define DAYS_UNTIL_1970		( ( 1970 * 365 ) + ( 1970 / 4 ) - ( 1970 / 100 ) + ( 1970 / 400 ) )
#define DAYS_BEFORE_MARCH	( 59 )

static portINLINE int iIsLeapyear( int iYear )
{
int iReturn;

	if( ( iYear % 4 ) != 0 )
	{
		/* Not a multiple of 4 years. */
		iReturn = pdFALSE;
	}
	else if( ( iYear % 400 ) == 0 )
	{
		/* Every 4 centuries there is a leap year */
		iReturn = pdTRUE;
	}
	else if( ( iYear % 100 ) == 0 )
	{
		/* Other centuries are not a leap year */
		iReturn = pdFALSE;
	}
	else
	{
		/* Otherwise every fourth year. */
		iReturn = pdTRUE;
	}

	return iReturn;
}

static portINLINE unsigned long ulDaysPerYear( int iYear )
{
int iDays;

	if( iIsLeapyear( iYear ) )
	{
		iDays = 366;
	}
	else
	{
		iDays = 365;
	}

	return iDays;
}

static int iDaysPerMonth( int iYear, int iMonth )
{
int iDays;

	/* Month is zero-based, 1 is February. */
	if (iMonth != 1 )
	{
		/* 30 or 31 days? */
		if(  ( MASK_LONG_MONTHS & ( 1u << iMonth ) ) != 0 )
		{
			iDays = 31;
		}
		else
		{
			iDays = 30;
		}
	}
	else if( iIsLeapyear( iYear ) == pdFALSE )
	{
		/* February, non leap year. */
		iDays = 28;
	}
	else
	{
		/* February, leap year. */
		iDays = 29;
	}
	return iDays;
}

FF_TimeStruct_t *FreeRTOS_gmtime_r( const time_t *pxTime, FF_TimeStruct_t *pxTimeBuf )
{
time_t xTime = *pxTime;
unsigned long ulDaySeconds, ulDayNumber;
int iYear = GMTIME_FIRST_YEAR;
int iMonth;

	/* Clear all fields, some might not get set here. */
	memset( ( void * )pxTimeBuf, '\0', sizeof( *pxTimeBuf ) );

	/* Seconds since last midnight. */
	ulDaySeconds = ( unsigned long ) ( xTime % SECONDS_PER_DAY ) ;

	/* Days since 1 Jan 1970. */
	ulDayNumber = ( unsigned long ) ( xTime / SECONDS_PER_DAY ) ;

	/* Today's HH:MM:SS */
	pxTimeBuf->tm_hour = ulDaySeconds / SECONDS_PER_HOUR;
	pxTimeBuf->tm_min = ( ulDaySeconds % SECONDS_PER_HOUR ) / 60;
	pxTimeBuf->tm_sec = ulDaySeconds % 60;

	/* Today's week day, knowing that 1-1-1970 was a THursday. */
	pxTimeBuf->tm_wday = ( ulDayNumber + WEEK_DAY_THURSDAY ) % 7;

	for( ; ; )
	{
		/* Keep subtracting 365 (or 366) days while possible. */
		unsigned long ulDays = ulDaysPerYear( iYear );
		if( ulDayNumber < ulDays )
		{
			break;
		}
		ulDayNumber -= ulDays;
		iYear++;
	}
	/* Subtract 1900. */
	pxTimeBuf->tm_year = iYear - TM_STRUCT_FIRST_YEAR;

	/* The day within this year. */
	pxTimeBuf->tm_yday = ulDayNumber;

	/* Month are counted as 0..11 */
	iMonth = 0;
	for( ; ; )
	{
		unsigned long ulDays = iDaysPerMonth( iYear, iMonth );
		/* Keep subtracting 30 (or 28, 29, or 31) days while possible. */
		if( ulDayNumber < ulDays )
		{
			break;
		}
		ulDayNumber -= ulDays;
		iMonth++;
	}
	pxTimeBuf->tm_mon = iMonth;

	/* Month days are counted as 1..31 */
	pxTimeBuf->tm_mday = ulDayNumber + 1;

	return pxTimeBuf;
}

time_t FreeRTOS_mktime( const FF_TimeStruct_t *pxTimeBuf )
{
/* Get year AD. */
int iYear = 1900 + pxTimeBuf->tm_year;	/* 20xx */
/* Get month zero-based. */
int iMonth = pxTimeBuf->tm_mon;			/* 0..11 */
uint32_t ulDays;
uint32_t ulResult;

	ulDays = pxTimeBuf->tm_mday - 1;	/* 1..31 */

	/* Make March the first month. */
	iMonth -= 2;
	if( iMonth < 0 )
	{
		/* January or February: leap day has yet to come for this year. */
		iYear--;
		iMonth += 12;
	}

	/* Add the number of days past until this month. */
	ulDays += ( ( 306 * iMonth ) + 5 ) / 10;

	/* Add days past before this year: */
	ulDays +=
		+ ( iYear * 365 )		/* Every normal year. */
		+ ( iYear / 4 )			/* Plus a day for every leap year. */
		- ( iYear / 100 )		/* Minus the centuries. */
		+ ( iYear / 400 )		/* Except every fourth century. */
		- ( DAYS_UNTIL_1970 )	/* Minus the days before 1-1-1970 */
		+ ( DAYS_BEFORE_MARCH );/* Because 2 months were subtracted. */

	ulResult =
		( ulDays * SECONDS_PER_DAY ) +
		( pxTimeBuf->tm_hour * SECONDS_PER_HOUR ) +
		( pxTimeBuf->tm_min * SECONDS_PER_MINUTE ) +
		pxTimeBuf->tm_sec;

	return ulResult;
}

#endif	/* ffconfigTIME_SUPPORT */

