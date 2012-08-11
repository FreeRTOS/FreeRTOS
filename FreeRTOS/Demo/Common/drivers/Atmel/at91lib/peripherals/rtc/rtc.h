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
//         Exported functions
//------------------------------------------------------------------------------

extern void RTC_SetHourMode(unsigned int mode);

extern void RTC_EnableIt(unsigned int sources);

extern void RTC_DisableIt(unsigned int sources);

extern void RTC_SetTime(
	unsigned char hour,
	unsigned char minute,
	unsigned char second);

extern void RTC_GetTime(
	unsigned char *pHour,
	unsigned char *pMinute,
	unsigned char *pSecond);

extern void RTC_SetTimeAlarm(
	unsigned char *pHour,
	unsigned char *pMinute,
	unsigned char *pSecond);

void RTC_GetDate(
    unsigned short *pYear,
    unsigned char *pMonth,
    unsigned char *pDay,
    unsigned char *pWeek);

extern void RTC_SetDate(
    unsigned short year,
    unsigned char month,
    unsigned char day,
    unsigned char week);

extern void RTC_SetDateAlarm(unsigned char *pMonth, unsigned char *pDay);

#endif //#ifndef RTC_H

