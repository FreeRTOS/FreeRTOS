/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

/** \addtogroup rtc_module Working with RTC
 * \section Purpose
 * The RTC driver provides the interface to configure and use the RTC
 * peripheral.
 *
 * It manages date, time, and alarms.\n
 * This timer is clocked by the 32kHz system clock, and is not impacted by
 * power management settings (PMC). To be accurate, it is better to use an
 * external 32kHz crystal instead of the internal 32kHz RC.\n
 *
 * It uses BCD format, and time can be set in AM/PM or 24h mode through a
 * configuration bit in the mode register.\n
 *
 * To update date or time, the user has to follow these few steps :
 * <ul>
 * <li>Set UPDTIM and/or UPDCAL bit(s) in RTC_CR,</li>
 * <li>Polling or IRQ on the ACKUPD bit of RTC_CR,</li>
 * <li>Clear ACKUPD bit in RTC_SCCR,</li>
 * <li>Update Time and/or Calendar values in RTC_TIMR/RTC_CALR (BCD format),</li>
 * <li>Clear UPDTIM and/or UPDCAL bit in RTC_CR.</li>
 * </ul>
 * An alarm can be set to happen on month, date, hours, minutes or seconds,
 * by setting the proper "Enable" bit of each of these fields in the Time and
 * Calendar registers.
 * This allows a large number of configurations to be available for the user.
 * Alarm occurence can be detected even by polling or interrupt.
 *
 * A check of the validity of the date and time format and values written by the user is automatically done.
 * Errors are reported through the Valid Entry Register.
 *
 * \section Usage
 * <ul>
 * <li>  Enable & disable RTC interrupt using rtc_enable_it() and rtc_disable_it().
 * <li>  Set RTC data, time, alarm using rtc_set_date(), rtc_set_time(),
 * rtc_set_time_alarm() and rtc_set_date_alarm().
 * <li>  Get RTC data, time using rtc_get_date() and rtc_get_time().
 * </li>
 * </ul>
 *
 * For more accurate information, please look at the RTC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref rtc.c\n
 * \ref rtc.h.\n
*/
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of Real Time Clock (RTC) controller.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/rtc.h"
#include "trace.h"
#include <stdint.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local Defines
 *----------------------------------------------------------------------------*/

/* The BCD code shift value */
#define BCD_SHIFT      4

/* The BCD code mask value */
#define BCD_MASK       0xfu

/* The BCD mul/div factor value */
#define BCD_FACTOR     10

/*----------------------------------------------------------------------------
 *        Local Types
 *----------------------------------------------------------------------------*/

struct rtc_ppm_lookup {
	int8_t   tempr;
	int16_t  ppm;
	uint8_t  negppm;
	uint8_t  highppm;
	uint16_t correction;
};

//------------------------------------------------------------------------------
//         Local constants
//------------------------------------------------------------------------------

static const struct rtc_ppm_lookup ppm_lookup[] = {
	{-40, -168, 0, 1, 22},
	{-39, -163, 0, 1, 23},
	{-38, -158, 0, 1, 24},
	{-37, -153, 0, 1, 25},
	{-36, -148, 0, 1, 25},
	{-35, -143, 0, 1, 26},
	{-34, -138, 0, 1, 27},
	{-33, -134, 0, 1, 28},
	{-32, -129, 0, 1, 29},
	{-31, -124, 0, 1, 31},
	{-30, -120, 0, 1, 32},
	{-29, -116, 0, 1, 33},
	{-28, -111, 0, 1, 34},
	{-27, -107, 0, 1, 36},
	{-26, -103, 0, 1, 37},
	{-25, -99, 0, 1, 38},
	{-24, -95, 0, 1, 40},
	{-23, -91, 0, 1, 42},
	{-22, -87, 0, 1, 44},
	{-21, -84, 0, 1, 45},
	{-20, -80, 0, 1, 48},
	{-19, -76, 0, 1, 50},
	{-18, -73, 0, 1, 53},
	{-17, -70, 0, 1, 55},
	{-16, -66, 0, 1, 58},
	{-15, -63, 0, 1, 61},
	{-14, -60, 0, 1, 64},
	{-13, -57, 0, 1, 68},
	{-12, -54, 0, 1, 71},
	{-11, -51, 0, 1, 76},
	{-10, -48, 0, 1, 80},
	{-9, -45, 0, 1, 86},
	{-8, -43, 0, 1, 90},
	{-7, -40, 0, 1, 97},
	{-6, -37, 0, 1, 105},
	{-5, -35, 0, 1, 111},
	{-4, -33, 0, 1, 117},
	{-3, -30, 0, 0, 6},
	{-2, -28, 0, 0, 6},
	{-1, -26, 0, 0, 7},
	{0, -24, 0, 0, 7},
	{1, -22, 0, 0, 8},
	{2, -20, 0, 0, 9},
	{3, -18, 0, 0, 10},
	{4, -17, 0, 0, 10},
	{5, -15, 0, 0, 12},
	{6, -13, 0, 0, 14},
	{7, -12, 0, 0, 15},
	{8, -11, 0, 0, 17},
	{9, -9, 0, 0, 21},
	{10, -8, 0, 0, 23},
	{11, -7, 0, 0, 27},
	{12, -6, 0, 0, 32},
	{13, -5, 0, 0, 38},
	{14, -4, 0, 0, 48},
	{15, -3, 0, 0, 64},
	{16, -2, 0, 0, 97},
	{17, -2, 0, 0, 97},
	{18, -1, 0, 0, 127},
	{19, 0, 1, 0, 0},
	{20, 0, 1, 0, 0},
	{21, 0, 1, 0, 0},
	{22, 1, 1, 0, 127},
	{23, 1, 1, 0, 127},
	{24, 1, 1, 0, 127},
	{25, 1, 1, 0, 127},
	{26, 1, 1, 0, 127},
	{27, 1, 1, 0, 127},
	{28, 1, 1, 0, 127},
	{29, 0, 1, 0, 0},
	{30, 0, 1, 0, 0},
	{31, 0, 1, 0, 0},
	{32, -1, 0, 0, 127},
	{33, -2, 0, 0, 97},
	{34, -2, 0, 0, 97},
	{35, -3, 0, 0, 64},
	{36, -4, 0, 0, 48},
	{37, -5, 0, 0, 38},
	{38, -6, 0, 0, 32},
	{39, -7, 0, 0, 27},
	{40, -8, 0, 0, 23},
	{41, -9, 0, 0, 21},
	{42, -11, 0, 0, 17},
	{43, -12, 0, 0, 15},
	{44, -13, 0, 0, 14},
	{45, -15, 0, 0, 12},
	{46, -17, 0, 0, 10},
	{47, -18, 0, 0, 10},
	{48, -20, 0, 0, 9},
	{49, -22, 0, 0, 8},
	{50, -24, 0, 0, 7},
	{51, -26, 0, 0, 7},
	{52, -28, 0, 0, 6},
	{53, -30, 0, 0, 6},
	{54, -33, 0, 1, 117},
	{55, -35, 0, 1, 111},
	{56, -37, 0, 1, 105},
	{57, -40, 0, 1, 97},
	{58, -43, 0, 1, 90},
	{59, -45, 0, 1, 86},
	{60, -48, 0, 1, 80},
	{61, -51, 0, 1, 76},
	{62, -54, 0, 1, 71},
	{63, -57, 0, 1, 68},
	{64, -60, 0, 1, 64},
	{65, -63, 0, 1, 61},
	{66, -66, 0, 1, 58},
	{67, -70, 0, 1, 55},
	{68, -73, 0, 1, 53},
	{69, -76, 0, 1, 50},
	{70, -80, 0, 1, 48},
	{71, -84, 0, 1, 45},
	{72, -87, 0, 1, 44},
	{73, -91, 0, 1, 42},
	{74, -95, 0, 1, 40},
	{75, -99, 0, 1, 38},
	{76, -103, 0, 1, 37},
	{77, -107, 0, 1, 36},
	{78, -111, 0, 1, 34},
	{79, -116, 0, 1, 33},
	{80, -120, 0, 1, 32},
	{81, -124, 0, 1, 31},
	{82, -129, 0, 1, 29},
	{83, -134, 0, 1, 28},
	{84, -138, 0, 1, 27},
	{85, -143, 0, 1, 26}
};

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Sets the RTC in either 12 or 24 hour mode.
 *
 * \param dwMode  Hour mode.
 */
void rtc_set_hour_mode(uint32_t mode)
{
	assert((mode & 0xFFFFFFFE) == 0);
	RTC->RTC_MR = mode;
}

extern uint32_t rtc_get_hour_mode(void)
{
	uint32_t mode;
	mode = RTC->RTC_MR;
	mode &= 0xFFFFFFFE;
	return mode;
}

void rtc_enable_it(uint32_t sources)
{
	assert((sources & (uint32_t) (~0x1F)) == 0);
	RTC->RTC_IER = sources;
}

void rtc_disable_it(uint32_t sources)
{
	assert((sources & (uint32_t) (~0x1F)) == 0);
	RTC->RTC_IDR = sources;
}

uint32_t rtc_set_time(struct _time *time)
{
	uint32_t ltime = 0;
	uint8_t hour_bcd , min_bcd, sec_bcd;

	/* if 12-hour mode, set AMPM bit */
	if ((RTC->RTC_MR & RTC_MR_HRMOD) == RTC_MR_HRMOD) {
		if (time->hour > 12) {
			time->hour -= 12;
			ltime |= RTC_TIMR_AMPM;
		}
	}
	hour_bcd = (time->hour % 10) | ((time->hour / 10) << 4);
	min_bcd = (time->min % 10) | ((time->min / 10) << 4);
	sec_bcd = (time->sec % 10) | ((time->sec / 10) << 4);
	/* value overflow */
	if ((hour_bcd & (uint8_t) (~RTC_HOUR_BIT_LEN_MASK)) |
	    (min_bcd & (uint8_t) (~RTC_MIN_BIT_LEN_MASK)) |
	    (sec_bcd & (uint8_t) (~RTC_SEC_BIT_LEN_MASK))) {
		return 1;
	}
	ltime = sec_bcd | (min_bcd << 8) | (hour_bcd << 16);
	RTC->RTC_CR |= RTC_CR_UPDTIM;
	while ((RTC->RTC_SR & RTC_SR_ACKUPD) != RTC_SR_ACKUPD) ;
	RTC->RTC_SCCR = RTC_SCCR_ACKCLR;
	RTC->RTC_TIMR = ltime;
	RTC->RTC_CR &= (uint32_t) (~RTC_CR_UPDTIM);
	RTC->RTC_SCCR |= RTC_SCCR_SECCLR;
	return (uint32_t) (RTC->RTC_VER & RTC_VER_NVTIM);
}

void rtc_get_time(struct _time *time)
{
	uint32_t ltime;

	/* Get current RTC time */
	ltime = RTC->RTC_TIMR;
	while (ltime != RTC->RTC_TIMR) {
		ltime = RTC->RTC_TIMR;
	}
	/* Hour */
	time->hour = ((ltime & 0x00300000) >> 20) * 10 + ((ltime & 0x000F0000) >> 16);
	if ((ltime & RTC_TIMR_AMPM) == RTC_TIMR_AMPM) {
		time->hour += 12;
	}
	/* Minute */
	time->min = ((ltime & 0x00007000) >> 12) * 10 + ((ltime & 0x00000F00) >> 8);
	/* Second */
	time->sec = ((ltime & 0x00000070) >> 4) * 10 + (ltime & 0x0000000F);
}

uint32_t rtc_set_time_alarm(struct _time *time)
{
	uint32_t alarm = 0;

	/* Hour */
	if (time->hour) {
		alarm |= RTC_TIMALR_HOUREN | ((time->hour / 10) << 20) | ((time->hour % 10) << 16);
	}
	/* Minute */
	if (time->min) {
		alarm |= RTC_TIMALR_MINEN | ((time->min / 10) << 12) | ((time->min % 10) << 8);
	}
	/* Second */
	if (time->sec) {
		alarm |= RTC_TIMALR_SECEN | ((time->sec / 10) << 4) | (time->sec % 10);
	}
	RTC->RTC_TIMALR = alarm;
	return (uint32_t) (RTC->RTC_VER & RTC_VER_NVTIMALR);
}

void rtc_get_date(struct _date *date)
{
	uint32_t ldate;

	/* Get current date (multiple reads are necessary to insure a stable value) */
	do {
		ldate = RTC->RTC_CALR;
	} while (ldate != RTC->RTC_CALR);

	/* Retrieve values */
	date->year = (((ldate >> 4) & 0x7) * 1000) + ((ldate & 0xF) * 100)
		+ (((ldate >> 12) & 0xF) * 10) + ((ldate >> 8) & 0xF);
	date->month = (((ldate >> 20) & 1) * 10) + ((ldate >> 16) & 0xF);
	date->day = (((ldate >> 28) & 0x3) * 10) + ((ldate >> 24) & 0xF);
	date->week = ((ldate >> 21) & 0x7);
}

uint32_t rtc_set_date(struct _date *date)
{
	uint32_t ldate;
	uint8_t cent_bcd, year_bcd, month_bcd, day_bcd, week_bcd;

	cent_bcd = ((date->year / 100) % 10) | ((date->year / 1000) << 4);
	year_bcd = (date->year % 10) | (((date->year / 10) % 10) << 4);
	month_bcd = ((date->month % 10) | (date->month / 10) << 4);
	day_bcd = ((date->day % 10) | (date->day / 10) << 4);
	week_bcd = ((date->week % 10) | (date->week / 10) << 4);
	/* value over flow */
	if ((cent_bcd & (uint8_t) (~RTC_CENT_BIT_LEN_MASK)) |
	    (year_bcd & (uint8_t) (~RTC_YEAR_BIT_LEN_MASK)) |
	    (month_bcd & (uint8_t) (~RTC_MONTH_BIT_LEN_MASK)) |
	    (week_bcd & (uint8_t) (~RTC_WEEK_BIT_LEN_MASK)) |
	    (day_bcd & (uint8_t) (~RTC_DATE_BIT_LEN_MASK))
	    ) {
		return 1;
	}
	/* Convert values to date register value */
	ldate = cent_bcd | (year_bcd << 8) | (month_bcd << 16) | (week_bcd << 21) | (day_bcd << 24);
	/* Update calendar register  */
	RTC->RTC_CR |= RTC_CR_UPDCAL;
	while ((RTC->RTC_SR & RTC_SR_ACKUPD) != RTC_SR_ACKUPD) ;
	RTC->RTC_SCCR = RTC_SCCR_ACKCLR;
	RTC->RTC_CALR = ldate;
	RTC->RTC_CR &= (uint32_t) (~RTC_CR_UPDCAL);
	RTC->RTC_SCCR |= RTC_SCCR_SECCLR;	/* clear SECENV in SCCR */
	return (uint32_t) (RTC->RTC_VER & RTC_VER_NVCAL);
}

uint32_t rtc_set_date_alarm(struct _date *date)
{
	uint32_t alarm;

	alarm = ((date->month) || (date->day)) ? (0) : (0x01010000);
	/* Compute alarm field value */
	if (date->month) {
		alarm |= RTC_CALALR_MTHEN | ((date->month / 10) << 20) | ((date->month % 10) << 16);
	}
	if (date->day) {
		alarm |= RTC_CALALR_DATEEN | ((date->day / 10) << 28) | ((date->day % 10) << 24);
	}
	/* Set alarm */
	RTC->RTC_CALALR = alarm;
	return (uint32_t) (RTC->RTC_VER & RTC_VER_NVCALALR);
}

void rtc_clear_sccr(uint32_t mask)
{
	/* Clear all flag bits in status clear command register */
	mask &= RTC_SCCR_ACKCLR | RTC_SCCR_ALRCLR | RTC_SCCR_SECCLR |
		RTC_SCCR_TIMCLR | RTC_SCCR_CALCLR;
	RTC->RTC_SCCR = mask;
}

uint32_t rtc_get_sr(uint32_t mask)
{
	return (RTC->RTC_SR) & mask;
}

void rtc_get_tamper_time(struct _time *time,  uint8_t reg_num)
{
	uint32_t ltime, temp;

	/* Get current RTC time */
	ltime = RTC->RTC_TS[reg_num].RTC_TSTR;
	while (ltime != RTC->RTC_TS[reg_num].RTC_TSTR) {
		ltime = RTC->RTC_TS[reg_num].RTC_TSTR;
	}
	/* Hour */
	if (time->hour) {
		temp = (ltime & RTC_TSTR_HOUR_Msk) >> RTC_TSTR_HOUR_Pos;
		time->hour = (temp >> BCD_SHIFT) * BCD_FACTOR + (temp & BCD_MASK);
		if ((ltime & RTC_TSTR_AMPM) == RTC_TSTR_AMPM) {
			time->hour += 12;
		}
	}
	/* Minute */
	if (time->min) {
		temp = (ltime & RTC_TSTR_MIN_Msk) >> RTC_TSTR_MIN_Pos;
		time->min = (temp >> BCD_SHIFT) * BCD_FACTOR + (temp & BCD_MASK);
	}
	/* Second */
	if (time->sec) {
		temp = (ltime & RTC_TSTR_SEC_Msk) >> RTC_TSTR_SEC_Pos;
		time->sec = (temp >> BCD_SHIFT) * BCD_FACTOR + (temp & BCD_MASK);
	}
}

void rtc_get_tamper_date(struct _date *date, uint8_t reg_num)
{
	uint32_t ldate, cent, temp;

	/* Get the current date (multiple reads are to insure a stable value). */
	ldate = RTC->RTC_TS[reg_num].RTC_TSDR;
	while (ldate != RTC->RTC_TS[reg_num].RTC_TSDR) {
		ldate = RTC->RTC_TS[reg_num].RTC_TSDR;
	}
	/* Retrieve year */
	temp = (ldate & RTC_TSDR_CENT_Msk) >> RTC_TSDR_CENT_Pos;
	cent = (temp >> BCD_SHIFT) * BCD_FACTOR + (temp & BCD_MASK);
	temp = (ldate & RTC_TSDR_YEAR_Msk) >> RTC_TSDR_YEAR_Pos;
	date->year = (cent * BCD_FACTOR * BCD_FACTOR) + (temp >> BCD_SHIFT) * BCD_FACTOR + (temp & BCD_MASK);

	/* Retrieve month */
	temp = (ldate & RTC_TSDR_MONTH_Msk) >> RTC_TSDR_MONTH_Pos;
	date->month = (temp >> BCD_SHIFT) * BCD_FACTOR + (temp & BCD_MASK);

	/* Retrieve day */
	temp = (ldate & RTC_TSDR_DATE_Msk) >> RTC_TSDR_DATE_Pos;
	date->day = (temp >> BCD_SHIFT) * BCD_FACTOR + (temp & BCD_MASK);

	/* Retrieve week */
	date->week= ((ldate & RTC_TSDR_DAY_Msk) >> RTC_TSDR_DAY_Pos);
}

uint32_t rtc_get_tamper_source(uint8_t reg_num)
{
	return RTC->RTC_TS[reg_num].RTC_TSSR;
}

uint32_t rtc_get_tamper_event_counter(void)
{
	return (RTC->RTC_TS[0].RTC_TSTR & RTC_TSTR_TEVCNT_Msk) >> RTC_TSTR_TEVCNT_Pos;
}

uint8_t rtc_is_tamper_occur_in_backup_mode(uint8_t reg_num)
{
	if (RTC->RTC_TS[reg_num].RTC_TSTR & RTC_TSTR_BACKUP) {
		return 1;
	} else {
		return 0;
	}
}

void rtc_convert_time_to_hms(struct _time *time, uint32_t count)
{
	count = count % 86400;
	time->hour = count / 3600;
	count -= time->hour * 3600;
	time->min = count / 60;
	time->sec = count % 60;
}

void rtc_calibration(int32_t current_tempr)
{
	uint32_t i, mr;
	for (i = 0; i < ARRAY_SIZE(ppm_lookup); i++) {
		if (ppm_lookup[i].tempr == current_tempr) {
			mr = RTC_MR_CORRECTION(ppm_lookup[i].correction);
			mr |= (ppm_lookup[i].highppm << 15);
			mr |= (ppm_lookup[i].negppm << 4);
			RTC->RTC_MR = mr; // update the calibration value
			break;
		}
	}
}

uint32_t rtc_set_time_event (uint32_t mask)
{
   uint32_t reg;
   reg = RTC->RTC_CR;
   reg &= ~RTC_CR_TIMEVSEL_Msk;
   reg |= mask;
   RTC->RTC_CR = reg;
   return RTC->RTC_CR;
}

uint32_t rtc_set_calendar_event (uint32_t mask)
{
   uint32_t reg;
   reg = RTC->RTC_CR;
   reg &= ~RTC_CR_CALEVSEL_Msk;
   reg |= mask;
   RTC->RTC_CR = reg;
   return RTC->RTC_CR;
}
