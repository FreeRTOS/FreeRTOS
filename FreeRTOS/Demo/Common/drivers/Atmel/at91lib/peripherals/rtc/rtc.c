/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef trace_LEVEL
	#define trace_LEVEL trace_INFO
#endif

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "rtc.h"
#include <board.h>
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Sets the RTC in either 12- or 24-hour mode.
/// \param mode  Hour mode.
//------------------------------------------------------------------------------
void RTC_SetHourMode(unsigned int mode)
{
	SANITY_CHECK((mode & 0xFFFFFFFE) == 0);

    trace_LOG(trace_DEBUG, "-D- RTC_SetHourMode()\n\r");

	AT91C_BASE_RTC->RTC_MR = mode;
}

//------------------------------------------------------------------------------
/// Enables the selected interrupt sources of the RTC.
/// \param sources  Interrupt sources to enable.
//------------------------------------------------------------------------------
void RTC_EnableIt(unsigned int sources)
{
    SANITY_CHECK((sources & ~0x1F) == 0);

    trace_LOG(trace_DEBUG, "-D- RTC_EnableIt()\n\r");

    AT91C_BASE_RTC->RTC_IER = sources;
}

//------------------------------------------------------------------------------
/// Disables the selected interrupt sources of the RTC.
/// \param sources  Interrupt sources to disable.
//------------------------------------------------------------------------------
void RTC_DisableIt(unsigned int sources)
{
    SANITY_CHECK((sources & ~0x1F) == 0);

    trace_LOG(trace_DEBUG, "-D- RTC_DisableIt()\n\r");

    AT91C_BASE_RTC->RTC_IDR = sources;
}

//------------------------------------------------------------------------------
/// Sets the current time in the RTC.
/// \param hour  Current hour.
/// \param minute  Current minute.
/// \param second  Current second.
//------------------------------------------------------------------------------
void RTC_SetTime(unsigned char hour, unsigned char minute, unsigned char second)
{
	unsigned int time;

	SANITY_CHECK(hour < 24);
	SANITY_CHECK(minute < 60);
	SANITY_CHECK(second < 60);

    trace_LOG(trace_DEBUG, "-D- RTC_SetTime(%02d:%02d:%02d)\n\r", hour, minute, second);

	time = (second % 10) | ((second / 10) << 4)
		   | ((minute % 10) << 8) | ((minute / 10) << 12);

	// 12-hour mode
	if ((AT91C_BASE_RTC->RTC_MR & AT91C_RTC_HRMOD) == AT91C_RTC_HRMOD) {

		if (hour > 12) {

			hour -= 12;
			time |= AT91C_RTC_AMPM;
		}
	}

	time |= ((hour % 10) << 16) | ((hour / 10) << 20);

	// Set time
	AT91C_BASE_RTC->RTC_CR |= AT91C_RTC_UPDTIM;
	while ((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_ACKUPD) != AT91C_RTC_ACKUPD);
	AT91C_BASE_RTC->RTC_SCCR = AT91C_RTC_ACKUPD;
	AT91C_BASE_RTC->RTC_TIMR = time;
	AT91C_BASE_RTC->RTC_CR &= ~AT91C_RTC_UPDTIM;
	SANITY_CHECK((AT91C_BASE_RTC->RTC_CR & AT91C_RTC_UPDTIM) != AT91C_RTC_UPDTIM);
}

//------------------------------------------------------------------------------
/// Retrieves the current time as stored in the RTC in several variables.
/// \param pHour  If not null, current hour is stored in this variable.
/// \param pMinute  If not null, current minute is stored in this variable.
/// \param pSecond  If not null, current second is stored in this variable.
//------------------------------------------------------------------------------
void RTC_GetTime(
	unsigned char *pHour,
	unsigned char *pMinute,
	unsigned char *pSecond)
{
	unsigned int time;

	SANITY_CHECK(pHour || pMinute || pSecond);

    trace_LOG(trace_DEBUG, "-D- RTC_GetTime()\n\r");

	// Get current RTC time
	time = AT91C_BASE_RTC->RTC_TIMR;
	while (time != AT91C_BASE_RTC->RTC_TIMR) {

		time = AT91C_BASE_RTC->RTC_TIMR;
	}

	// Hour
	if (pHour) {

		*pHour = ((time & 0x00300000) >> 20) * 10
				 + ((time & 0x000F0000) >> 16);
		if ((time & AT91C_RTC_AMPM) == AT91C_RTC_AMPM) {

			*pHour += 12;
		}
	}
	
	// Minute
	if (pMinute) {

		*pMinute = ((time & 0x00007000) >> 12) * 10
				   + ((time & 0x00000F00) >> 8);
	}

	// Second
	if (pSecond) {

		*pSecond = ((time & 0x00000070) >> 4) * 10
				   + (time & 0x0000000F);
	}
}

//------------------------------------------------------------------------------
/// Sets a time alarm on the RTC. The match is performed only on the provided
/// variables; setting all pointers to 0 disables the time alarm.
/// Note: in AM/PM mode, the hour value must have bit #7 set for PM, cleared for
/// AM (as expected in the time registers).
/// \param pHour  If not null, the time alarm will hour-match this value.
/// \param pMinute  If not null, the time alarm will minute-match this value.
/// \param pSecond  If not null, the time alarm will second-match this value.
//------------------------------------------------------------------------------
void RTC_SetTimeAlarm(
	unsigned char *pHour,
	unsigned char *pMinute,
	unsigned char *pSecond)
{
	unsigned int alarm = 0;

    SANITY_CHECK(!pHour || ((*pHour & 0x80) == 0));
    SANITY_CHECK(!pMinute || (*pMinute < 60));
    SANITY_CHECK(!pSecond || (*pSecond < 60));

	trace_LOG(trace_DEBUG, "-D- RTC_SetTimeAlarm()\n\r");

	// Hour
	if (pHour) {

		alarm |= AT91C_RTC_HOUREN | ((*pHour / 10) << 20) | ((*pHour % 10) << 16);
	}

	// Minute
	if (pMinute) {

		alarm |= AT91C_RTC_MINEN | ((*pMinute / 10) << 12) | ((*pMinute % 10) << 8);
	}

	// Second
	if (pSecond) {

		alarm |= AT91C_RTC_SECEN | ((*pSecond / 10) << 4) | (*pSecond % 10);
	}

	AT91C_BASE_RTC->RTC_TIMALR = alarm;
}

//------------------------------------------------------------------------------
/// Retrieves the current year, month and day from the RTC. Month, day and week
/// values are numbered starting at 1.
/// \param pYear  Current year (optional).
/// \param pMonth  Current month (optional).
/// \param pDay  Current day (optional).
/// \param pWeek  Current day in current week (optional).
//------------------------------------------------------------------------------
void RTC_GetDate(
    unsigned short *pYear,
    unsigned char *pMonth,
    unsigned char *pDay,
    unsigned char *pWeek)
{
    unsigned int date;

    // Get current date (multiple reads are necessary to insure a stable value)
    do {

        date = AT91C_BASE_RTC->RTC_CALR;
    }
    while (date != AT91C_BASE_RTC->RTC_CALR);

    // Retrieve year
    if (pYear) {

        *pYear = (((date  >> 4) & 0x7) * 1000)
                 + ((date & 0xF) * 100)
                 + (((date >> 12) & 0xF) * 10)
                 + ((date >> 8) & 0xF);
    }

    // Retrieve month
    if (pMonth) {

        *pMonth = (((date >> 20) & 1) * 10) + ((date >> 16) & 0xF);
    }

    // Retrieve day
    if (pDay) {

        *pDay = (((date >> 28) & 0x3) * 10) + ((date >> 24) & 0xF);
    }

    // Retrieve week
    if (pWeek) {

        *pWeek = ((date >> 21) & 0x7);
    }
}

//------------------------------------------------------------------------------
/// Sets the current year, month and day in the RTC. Month, day and week values
/// must be numbered starting from 1.
/// \param year  Current year.
/// \param month  Current month.
/// \param day  Current day.
/// \param week  Day number in current week.
//------------------------------------------------------------------------------
void RTC_SetDate(
    unsigned short year,
    unsigned char month,
    unsigned char day,
    unsigned char week)
{
    unsigned int date;

    SANITY_CHECK((year >= 1900) && (year <= 2099));
    SANITY_CHECK((month >= 1) && (month <= 12));
    SANITY_CHECK((day >= 1) && (day <= 31));
    SANITY_CHECK((week >= 1) && (week <= 7));

    // Convert values to date register value
    date = ((year / 100) % 10)
           | ((year / 1000) << 4)
           | ((year % 10) << 8)
           | (((year / 10) % 10) << 12)
           | ((month % 10) << 16)
           | ((month / 10) << 20)
           | (week << 21)
           | ((day % 10) << 24)
           | ((day / 10) << 28);

    // Update calendar register
    AT91C_BASE_RTC->RTC_CR |= AT91C_RTC_UPDCAL;
    while ((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_ACKUPD) != AT91C_RTC_ACKUPD);
    AT91C_BASE_RTC->RTC_SCCR = AT91C_RTC_ACKUPD;
    AT91C_BASE_RTC->RTC_CALR = date;
    AT91C_BASE_RTC->RTC_CR &= ~AT91C_RTC_UPDCAL;
}

//------------------------------------------------------------------------------
/// Sets a date alarm in the RTC. The alarm will match only the provided values;
/// passing a null-pointer disables the corresponding field match.
/// \param pMonth  If not null, the RTC alarm will month-match this value.
/// \param pDay  If not null, the RTC alarm will day-match this value.
//------------------------------------------------------------------------------
void RTC_SetDateAlarm(unsigned char *pMonth, unsigned char *pDay)
{
    unsigned int alarm = 0;

    SANITY_CHECK(!pMonth || ((*pMonth >= 1) && (*pMonth <= 12)));
    SANITY_CHECK(!pDay || ((*pDay >= 1) && (*pDay <= 31)));

    trace_LOG(trace_DEBUG, "-D- RTC_SetDateAlarm()\n\r");

    // Compute alarm field value
    if (pMonth) {

        alarm |= AT91C_RTC_MONTHEN | ((*pMonth / 10) << 20) | ((*pMonth % 10) << 16);
    }
    if (pDay) {

        alarm |= AT91C_RTC_DATEEN | ((*pDay / 10) << 28) | ((*pDay % 10) << 24);
    }

    // Set alarm
    AT91C_BASE_RTC->RTC_CALALR = alarm;
}

