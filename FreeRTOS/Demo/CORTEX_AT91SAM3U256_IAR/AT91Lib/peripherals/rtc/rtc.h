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

#ifndef RTC_H
#define RTC_H

//------------------------------------------------------------------------------
//         Macro used
//------------------------------------------------------------------------------
#define RTC_HOUR_BIT_LEN_MASK   0x3F
#define RTC_MIN_BIT_LEN_MASK    0x7F
#define RTC_SEC_BIT_LEN_MASK    0x7F
#define RTC_CENT_BIT_LEN_MASK   0x7F
#define RTC_YEAR_BIT_LEN_MASK   0xFF
#define RTC_MONTH_BIT_LEN_MASK  0x1F
#define RTC_DATE_BIT_LEN_MASK   0x3F
#define RTC_WEEK_BIT_LEN_MASK   0x07

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

extern void RTC_SetHourMode(unsigned int mode);

extern unsigned int RTC_GetHourMode();

extern void RTC_EnableIt(unsigned int sources);

extern void RTC_DisableIt(unsigned int sources);

extern int RTC_SetTime(
	unsigned char hour,
	unsigned char minute,
	unsigned char second);

extern void RTC_GetTime(
	unsigned char *pHour,
	unsigned char *pMinute,
	unsigned char *pSecond);

extern int RTC_SetTimeAlarm(
	unsigned char *pHour,
	unsigned char *pMinute,
	unsigned char *pSecond);

void RTC_GetDate(
    unsigned short *pYear,
    unsigned char *pMonth,
    unsigned char *pDay,
    unsigned char *pWeek);

extern int RTC_SetDate(
    unsigned short year,
    unsigned char month,
    unsigned char day,
    unsigned char week);

extern int RTC_SetDateAlarm(unsigned char *pMonth, unsigned char *pDay);

extern void RTC_ClearSCCR(unsigned int mask);

extern unsigned int RTC_GetSR(unsigned int mask);
#endif //#ifndef RTC_H

