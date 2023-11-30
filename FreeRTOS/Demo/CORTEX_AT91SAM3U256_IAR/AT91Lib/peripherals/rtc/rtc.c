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

    TRACE_DEBUG("RTC_SetHourMode()\n\r");

    AT91C_BASE_RTC->RTC_MR = mode;
}

//------------------------------------------------------------------------------
/// Gets the RTC mode.
/// \return Hour mode.
//------------------------------------------------------------------------------
unsigned int RTC_GetHourMode()
{
    unsigned int hmode;

    TRACE_DEBUG("RTC_SetHourMode()\n\r");

    hmode = AT91C_BASE_RTC->RTC_MR;
    hmode &= 0xFFFFFFFE;

    return hmode;
}

//------------------------------------------------------------------------------
/// Enables the selected interrupt sources of the RTC.
/// \param sources  Interrupt sources to enable.
//------------------------------------------------------------------------------
void RTC_EnableIt(unsigned int sources)
{
    SANITY_CHECK((sources & ~0x1F) == 0);

    TRACE_DEBUG("RTC_EnableIt()\n\r");

    AT91C_BASE_RTC->RTC_IER = sources;
}

//------------------------------------------------------------------------------
/// Disables the selected interrupt sources of the RTC.
/// \param sources  Interrupt sources to disable.
//------------------------------------------------------------------------------
void RTC_DisableIt(unsigned int sources)
{
    SANITY_CHECK((sources & ~0x1F) == 0);

    TRACE_DEBUG("RTC_DisableIt()\n\r");

    AT91C_BASE_RTC->RTC_IDR = sources;
}

//------------------------------------------------------------------------------
/// Sets the current time in the RTC.
/// \param hour  Current hour in 24 hour mode.
/// \param minute  Current minute.
/// \param second  Current second.
/// \return 0 sucess, 1 fail to set
//------------------------------------------------------------------------------
int RTC_SetTime(unsigned char hour, unsigned char minute, unsigned char second)
{
    unsigned int time=0;
    unsigned char hour_bcd;
    unsigned char min_bcd;
    unsigned char sec_bcd;

    TRACE_DEBUG("RTC_SetTime(%02d:%02d:%02d)\n\r", hour, minute, second);
   
    // if 12-hour mode, set AMPM bit
    if ((AT91C_BASE_RTC->RTC_MR & AT91C_RTC_HRMOD) == AT91C_RTC_HRMOD) {
          
        if (hour > 12) {

            hour -= 12;
            time |= AT91C_RTC_AMPM;
        }
    }
    hour_bcd  = (hour%10) | ((hour/10)<<4);
    min_bcd   = (minute%10) | ((minute/10)<<4);
    sec_bcd   = (second%10) | ((second/10)<<4);
    
    //value overflow
    if((hour_bcd & (unsigned char)(~RTC_HOUR_BIT_LEN_MASK)) |
       (min_bcd & (unsigned char)(~RTC_MIN_BIT_LEN_MASK)) |
         (sec_bcd & (unsigned char)(~RTC_SEC_BIT_LEN_MASK)))
            return 1;
    
    time = sec_bcd | (min_bcd << 8) | (hour_bcd<<16);

//    time |= ((hour % 10) << 16) | ((hour / 10) << 20);

    // Set time
    //if((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_SECEV) != AT91C_RTC_SECEV) return 1;
    while ((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_SECEV) != AT91C_RTC_SECEV);//wait from previous set
    AT91C_BASE_RTC->RTC_CR |= AT91C_RTC_UPDTIM;
    while ((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_ACKUPD) != AT91C_RTC_ACKUPD);
    AT91C_BASE_RTC->RTC_SCCR = AT91C_RTC_ACKUPD;
    AT91C_BASE_RTC->RTC_TIMR = time;
    AT91C_BASE_RTC->RTC_CR &= ~AT91C_RTC_UPDTIM;
    AT91C_BASE_RTC->RTC_SCCR |= AT91C_RTC_SECEV;//clear SECENV in SCCR
        
    return (int)(AT91C_BASE_RTC->RTC_VER & AT91C_RTC_NVTIM);
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

    TRACE_DEBUG("RTC_GetTime()\n\r");

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
/// \return 0 success, 1 fail to set
//------------------------------------------------------------------------------
int RTC_SetTimeAlarm(
    unsigned char *pHour,
    unsigned char *pMinute,
    unsigned char *pSecond)
{
    unsigned int alarm = 0;

    TRACE_DEBUG("RTC_SetTimeAlarm()\n\r");

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
    
    return (int)(AT91C_BASE_RTC->RTC_VER & AT91C_RTC_NVTIMALR);
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
/// \return 0 success, 1 fail to set
//------------------------------------------------------------------------------
int RTC_SetDate(
    unsigned short year,
    unsigned char month,
    unsigned char day,
    unsigned char week)
{
    unsigned int date;
    unsigned char cent_bcd;
    unsigned char year_bcd;
    unsigned char month_bcd;
    unsigned char day_bcd;
    unsigned char week_bcd;
    
    cent_bcd  = ((year/100)%10) | ((year/1000)<<4);
    year_bcd  = (year%10) | ((year/10)%10);
    month_bcd = ((month%10) | (month/10)<<4);
    day_bcd   = ((day%10) | (day/10)<<4);
    week_bcd  = ((week%10) | (week/10)<<4);
    
    //value over flow
    if((cent_bcd & (unsigned char)(~RTC_CENT_BIT_LEN_MASK)) |
        (year_bcd & (unsigned char)(~RTC_YEAR_BIT_LEN_MASK)) |
          (month_bcd & (unsigned char)(~RTC_MONTH_BIT_LEN_MASK)) |
            (week_bcd & (unsigned char)(~RTC_WEEK_BIT_LEN_MASK)) |
              (day_bcd & (unsigned char)(~RTC_DATE_BIT_LEN_MASK)))
                return 1;


    // Convert values to date register value
    date = cent_bcd |
            (year_bcd << 8) |
              (month_bcd << 16) |
                (week_bcd << 21) |
                  (day_bcd << 24);
    
           
    // Update calendar register
    //if((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_SECEV) != AT91C_RTC_SECEV) return 1;
    while ((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_SECEV) != AT91C_RTC_SECEV);//wait from previous set
    AT91C_BASE_RTC->RTC_CR |= AT91C_RTC_UPDCAL;
    while ((AT91C_BASE_RTC->RTC_SR & AT91C_RTC_ACKUPD) != AT91C_RTC_ACKUPD);
    AT91C_BASE_RTC->RTC_SCCR = AT91C_RTC_ACKUPD;
    AT91C_BASE_RTC->RTC_CALR = date;
    AT91C_BASE_RTC->RTC_CR &= ~AT91C_RTC_UPDCAL;
    AT91C_BASE_RTC->RTC_SCCR |= AT91C_RTC_SECEV;//clear SECENV in SCCR
    
    return (int)(AT91C_BASE_RTC->RTC_VER & AT91C_RTC_NVCAL);
}

//------------------------------------------------------------------------------
/// Sets a date alarm in the RTC. The alarm will match only the provided values;
/// passing a null-pointer disables the corresponding field match.
/// \param pMonth  If not null, the RTC alarm will month-match this value.
/// \param pDay  If not null, the RTC alarm will day-match this value.
/// \return 0 success, 1 fail to set
//------------------------------------------------------------------------------
int RTC_SetDateAlarm(unsigned char *pMonth, unsigned char *pDay)
{
    unsigned int alarm = 0x01010000;

    TRACE_DEBUG("RTC_SetDateAlarm()\n\r");

    // Compute alarm field value
    if (pMonth) {

        alarm |= AT91C_RTC_MONTHEN | ((*pMonth / 10) << 20) | ((*pMonth % 10) << 16);
    }
    if (pDay) {

        alarm |= AT91C_RTC_DATEEN | ((*pDay / 10) << 28) | ((*pDay % 10) << 24);
    }

    // Set alarm
    AT91C_BASE_RTC->RTC_CALALR = alarm;
    
    return (int)(AT91C_BASE_RTC->RTC_VER & AT91C_RTC_NVCALALR);
}

//------------------------------------------------------------------------------
/// Clear flag bits of status clear command register in the RTC. 
/// \param mask Bits mask of cleared events
//------------------------------------------------------------------------------
void RTC_ClearSCCR(unsigned int mask)
{
    // Clear all flag bits in status clear command register
    mask &= AT91C_RTC_ACKUPD | AT91C_RTC_ALARM | AT91C_RTC_SECEV | \
                                    AT91C_RTC_TIMEV | AT91C_RTC_CALEV;
    
    AT91C_BASE_RTC->RTC_SCCR = mask;
}

//------------------------------------------------------------------------------
/// Get flag bits of status register in the RTC. 
/// \param mask Bits mask of Status Register
/// \return Status register & mask
//------------------------------------------------------------------------------
unsigned int RTC_GetSR(unsigned int mask)
{
    unsigned int event;
    
    event = AT91C_BASE_RTC->RTC_SR;
    
    return (event & mask);
}
