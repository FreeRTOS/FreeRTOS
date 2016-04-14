/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/**
 * \file
 *
 * Interface for Real Time Clock (RTC) controller.
 *
 */

#ifndef _RTC_H_
#define _RTC_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

#define RTC_HOUR_BIT_LEN_MASK   0x3F
#define RTC_MIN_BIT_LEN_MASK    0x7F
#define RTC_SEC_BIT_LEN_MASK    0x7F
#define RTC_CENT_BIT_LEN_MASK   0x7F
#define RTC_YEAR_BIT_LEN_MASK   0xFF
#define RTC_MONTH_BIT_LEN_MASK  0x1F
#define RTC_DATE_BIT_LEN_MASK   0x3F
#define RTC_WEEK_BIT_LEN_MASK   0x07

struct _time
{
  uint8_t hour;
  uint8_t min;
  uint8_t sec;
} ;

struct _date
{
  uint16_t year;
  uint8_t  month;
  uint8_t  day;
  uint8_t  week;
} ;

#ifdef CONFIG_SOC_SAMA5D2
	/* -------- RTC_TSTR : (RTC Offset: N/A) TimeStamp Time Register 0 -------- */
	#define RTC_TSTR_SEC_Pos 0
	#define RTC_TSTR_SEC_Msk (0x7fu << RTC_TSTR_SEC_Pos) /**< \brief (RTC_TSTR) SEConds of the tamper */
	#define RTC_TSTR_MIN_Pos 8
	#define RTC_TSTR_MIN_Msk (0x7fu << RTC_TSTR_MIN_Pos) /**< \brief (RTC_TSTR) MINutes of the tamper */
	#define RTC_TSTR_HOUR_Pos 16
	#define RTC_TSTR_HOUR_Msk (0x3fu << RTC_TSTR_HOUR_Pos) /**< \brief (RTC_TSTR) HOURs of the tamper */
	#define RTC_TSTR_AMPM (0x1u << 22) /**< \brief (RTC_TSTR) AMPM indicator of the tamper */
	#define RTC_TSTR_TEVCNT_Pos 24
	#define RTC_TSTR_TEVCNT_Msk (0xfu << RTC_TSTR_TEVCNT_Pos) /**< \brief (RTC_TSTR) Tamper events counter */
	#define RTC_TSTR_BACKUP (0x1u << 31) /**< \brief (RTC_TSTR) system mode of the tamper */
	/* -------- RTC_TSDR : (RTC Offset: N/A) TimeStamp Date Register 0 -------- */
	#define RTC_TSDR_CENT_Pos 0
	#define RTC_TSDR_CENT_Msk (0x7fu << RTC_TSDR_CENT_Pos) /**< \brief (RTC_TSDR) Century of the tamper */
	#define RTC_TSDR_YEAR_Pos 8
	#define RTC_TSDR_YEAR_Msk (0xffu << RTC_TSDR_YEAR_Pos) /**< \brief (RTC_TSDR) Year of the tamper */
	#define RTC_TSDR_MONTH_Pos 16
	#define RTC_TSDR_MONTH_Msk (0x1fu << RTC_TSDR_MONTH_Pos) /**< \brief (RTC_TSDR) Month of the tamper */
	#define RTC_TSDR_DAY_Pos 21
	#define RTC_TSDR_DAY_Msk (0x7u << RTC_TSDR_DAY_Pos) /**< \brief (RTC_TSDR) Day of the tamper */
	#define RTC_TSDR_DATE_Pos 24
	#define RTC_TSDR_DATE_Msk (0x3fu << RTC_TSDR_DATE_Pos) /**< \brief (RTC_TSDR) Date of the tamper */
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \brief Sets the RTC in either 12 or 24 hour mode.
 *
 * \param mode  Hour mode.
 */
extern void rtc_set_hour_mode(uint32_t mode);

/**
 * \brief Gets the RTC mode.
 *
 * \return Hour mode.
 */
extern uint32_t rtc_get_hour_mode(void);

/**
 * \brief Enables the selected interrupt sources of the RTC.
 *
 * \param sources  Interrupt sources to enable.
 */
extern void rtc_enable_it(uint32_t sources);

/**
* \brief Disables the selected interrupt sources of the RTC.
*
* \param sources  Interrupt sources to disable.
*/
extern void rtc_disable_it(uint32_t sources);

/**
 * \brief Sets the current time in the RTC.
 *
 * \note In successive update operations, the user must wait at least one second
 * after resetting the UPDTIM/UPDCAL bit in the RTC_CR before setting these
 * bits again. Please look at the RTC section of the datasheet for detail.
 *
 * \param time Pointer to structure time
 *
 * \return 0 sucess, 1 fail to set
 */
extern uint32_t rtc_set_time(struct _time *time);

/**
 * \brief Retrieves the current time as stored in the RTC in several variables.
 *
 * \param time Pointer to structure time
 */
extern void rtc_get_time(struct _time *time);

/**
 * \brief Sets a time alarm on the RTC.
 * The match is performed only on the provided variables;
 * Setting all pointers to 0 disables the time alarm.
 *
 * \note In AM/PM mode, the hour value must have bit #7 set for PM, cleared for
 * AM (as expected in the time registers).
 *
 * \param time Pointer to structure time.
 *
 * \return 0 success, 1 fail to set
 */
extern uint32_t rtc_set_time_alarm(struct _time *time);

/**
 * \brief Retrieves the current year, month and day from the RTC.
 * Month, day and week values are numbered starting at 1.
 *
 * \param date	Pointer to structure Date.
 */
extern void rtc_get_date(struct _date *date);

/**
 * \brief Sets the current year, month and day in the RTC.
 * Month, day and week values must be numbered starting from 1.
 *
 * \note In successive update operations, the user must wait at least one second
 * after resetting the UPDTIM/UPDCAL bit in the RTC_CR before setting these
 * bits again. Please look at the RTC section of the datasheet for detail.
 *
 * \param date	Pointer to structure Date
 *
 * \return 0 success, 1 fail to set
 */
extern uint32_t rtc_set_date(struct _date *date);

/**
 * \brief Sets a date alarm in the RTC.
 * The alarm will match only the provided values;
 * Passing a null-pointer disables the corresponding field match.
 *
 * \param pucMonth If not null, the RTC alarm will month-match this value.
 * \param pucDay   If not null, the RTC alarm will day-match this value.
 *
 * \return 0 success, 1 fail to set
 */
extern uint32_t rtc_set_date_alarm(struct _date *date);

/**
 * \brief Clear flag bits of status clear command register in the RTC.
 *
 * \param mask Bits mask of cleared events
 */
extern void rtc_clear_sccr(uint32_t mask);

/**
 * \brief Get flag bits of status register in the RTC.
 *
 * \param mask Bits mask of Status Register
 *
 * \return Status register & mask
 */
extern uint32_t rtc_get_sr(uint32_t mask);

/**
 * \brief Get the RTC tamper time value.
 *
 * \note This function should be called before rtc_get_tamper_source()
 *       function call, Otherwise the tamper time will be cleared.
 *
 * \param time Pointer to structure Time.
 * \param reg_num    Tamper register set number.
 */
extern void rtc_get_tamper_time(struct _time *time, uint8_t reg_num);

/**
 * \brief Get the RTC tamper date.
 *
 * \note This function should be called before rtc_get_tamper_source()
 *       function call, Otherwise the tamper date will be cleared.
 *
 * \param date     Pointer to structure Date
 * \param reg_num   Tamper register set number.
 */
extern void rtc_get_tamper_date(struct _date *date, uint8_t reg_num);

/**
 * \brief Get the RTC tamper source.
 *
 * \param reg_num  Current tamper register set number.
 *
 * \return Tamper source.
 */
extern uint32_t rtc_get_tamper_source(uint8_t reg_num);

/**
 * \brief Get the RTC tamper event counter.
 *
 * \note This function should be called before rtc_get_tamper_source()
 *       function call, Otherwise the tamper event counter will be cleared.
 *
 * \return Tamper event counter
 */
extern uint32_t rtc_get_tamper_event_counter(void);

/**
 * \brief Check the system is in backup mode when RTC tamper event happen.
 *
 * \note This function should be called before rtc_get_tamper_source()
 *       function call, Otherwise the flag indicates tamper occur in backup
 *       mode will be cleared.
 *
 * \param reg_num  Current tamper register set number.
 *
 * \return 1 - The system is in backup mode when the tamper event occurs.
 *         0 - The system is different from backup mode.
 */
extern uint8_t rtc_is_tamper_occur_in_backup_mode(uint8_t reg_num);

/**
 * \brief Convert number of second (count) to HMS format.
 *
 */
extern void rtc_convert_time_to_hms (struct _time *time, uint32_t count);

/**
 * \brief RTC calibration for Temperature or PPM drift
 */
extern void rtc_calibration(int32_t current_tempr);

/**
 * \brief Set calendar event selection.
 *
 * \param mask Bits CALEVSEL of Control Register
 * \return Status register & mask
 */
extern uint32_t rtc_set_calendar_event (uint32_t mask);

/**
 * \brief Set time event selection.
 *
 * \param mask Bits TIMEVSEL of Control Register
 * \return Status register & mask
 */
extern uint32_t rtc_set_time_event (uint32_t maskask);

#ifdef __cplusplus
}
#endif
#endif /* _RTC_H_ */
