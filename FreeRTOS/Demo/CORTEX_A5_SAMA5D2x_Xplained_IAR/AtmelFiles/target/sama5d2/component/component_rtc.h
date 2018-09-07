/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2015, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMA5D2_RTC_COMPONENT_
#define _SAMA5D2_RTC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Real-time Clock */
/* ============================================================================= */
/** \addtogroup SAMA5D2_RTC Real-time Clock */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief RtcTs hardware registers */
typedef struct {
  __I uint32_t RTC_TSTR; /**< \brief (RtcTs Offset: 0x0) TimeStamp Time Register 0 */
  __I uint32_t RTC_TSDR; /**< \brief (RtcTs Offset: 0x4) TimeStamp Date Register 0 */
  __I uint32_t RTC_TSSR; /**< \brief (RtcTs Offset: 0x8) TimeStamp Source Register 0 */
} RtcTs;
/** \brief Rtc hardware registers */
#define RTCTS_NUMBER 2
typedef struct {
  __IO uint32_t RTC_CR;               /**< \brief (Rtc Offset: 0x00) Control Register */
  __IO uint32_t RTC_MR;               /**< \brief (Rtc Offset: 0x04) Mode Register */
  __IO uint32_t RTC_TIMR;             /**< \brief (Rtc Offset: 0x08) Time Register */
  __IO uint32_t RTC_CALR;             /**< \brief (Rtc Offset: 0x0C) Calendar Register */
  __IO uint32_t RTC_TIMALR;           /**< \brief (Rtc Offset: 0x10) Time Alarm Register */
  __IO uint32_t RTC_CALALR;           /**< \brief (Rtc Offset: 0x14) Calendar Alarm Register */
  __I  uint32_t RTC_SR;               /**< \brief (Rtc Offset: 0x18) Status Register */
  __O  uint32_t RTC_SCCR;             /**< \brief (Rtc Offset: 0x1C) Status Clear Command Register */
  __O  uint32_t RTC_IER;              /**< \brief (Rtc Offset: 0x20) Interrupt Enable Register */
  __O  uint32_t RTC_IDR;              /**< \brief (Rtc Offset: 0x24) Interrupt Disable Register */
  __I  uint32_t RTC_IMR;              /**< \brief (Rtc Offset: 0x28) Interrupt Mask Register */
  __I  uint32_t RTC_VER;              /**< \brief (Rtc Offset: 0x2C) Valid Entry Register */
  __I  uint32_t Reserved1[32];
       RtcTs    RTC_TS[RTCTS_NUMBER]; /**< \brief (Rtc Offset: 0xB0) 0 .. 1 */
  __I  uint32_t Reserved2[2];
  __I  uint32_t RTC_MSR;              /**< \brief (Rtc Offset: 0xD0) Milliseconds Register */
  __I  uint32_t Reserved3[4];
  __IO uint32_t RTC_WPMR;             /**< \brief (Rtc Offset: 0xE4) Write Protection Mode Register */
  __I  uint32_t Reserved4[5];
  __I  uint32_t RTC_VERSION;          /**< \brief (Rtc Offset: 0xFC) Version Register */
} Rtc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- RTC_CR : (RTC Offset: 0x00) Control Register -------- */
#define RTC_CR_UPDTIM (0x1u << 0) /**< \brief (RTC_CR) Update Request Time Register */
#define RTC_CR_UPDCAL (0x1u << 1) /**< \brief (RTC_CR) Update Request Calendar Register */
#define RTC_CR_TIMEVSEL_Pos 8
#define RTC_CR_TIMEVSEL_Msk (0x3u << RTC_CR_TIMEVSEL_Pos) /**< \brief (RTC_CR) Time Event Selection */
#define RTC_CR_TIMEVSEL(value) ((RTC_CR_TIMEVSEL_Msk & ((value) << RTC_CR_TIMEVSEL_Pos)))
#define   RTC_CR_TIMEVSEL_MINUTE (0x0u << 8) /**< \brief (RTC_CR) Minute change */
#define   RTC_CR_TIMEVSEL_HOUR (0x1u << 8) /**< \brief (RTC_CR) Hour change */
#define   RTC_CR_TIMEVSEL_MIDNIGHT (0x2u << 8) /**< \brief (RTC_CR) Every day at midnight */
#define   RTC_CR_TIMEVSEL_NOON (0x3u << 8) /**< \brief (RTC_CR) Every day at noon */
#define RTC_CR_CALEVSEL_Pos 16
#define RTC_CR_CALEVSEL_Msk (0x3u << RTC_CR_CALEVSEL_Pos) /**< \brief (RTC_CR) Calendar Event Selection */
#define RTC_CR_CALEVSEL(value) ((RTC_CR_CALEVSEL_Msk & ((value) << RTC_CR_CALEVSEL_Pos)))
#define   RTC_CR_CALEVSEL_WEEK (0x0u << 16) /**< \brief (RTC_CR) Week change (every Monday at time 00:00:00) */
#define   RTC_CR_CALEVSEL_MONTH (0x1u << 16) /**< \brief (RTC_CR) Month change (every 01 of each month at time 00:00:00) */
#define   RTC_CR_CALEVSEL_YEAR (0x2u << 16) /**< \brief (RTC_CR) Year change (every January 1 at time 00:00:00) */
/* -------- RTC_MR : (RTC Offset: 0x04) Mode Register -------- */
#define RTC_MR_HRMOD (0x1u << 0) /**< \brief (RTC_MR) 12-/24-hour Mode */
#define RTC_MR_PERSIAN (0x1u << 1) /**< \brief (RTC_MR) PERSIAN Calendar */
#define RTC_MR_UTC (0x1u << 2) /**< \brief (RTC_MR) UTC Time Format */
#define RTC_MR_NEGPPM (0x1u << 4) /**< \brief (RTC_MR) NEGative PPM Correction */
#define RTC_MR_CORRECTION_Pos 8
#define RTC_MR_CORRECTION_Msk (0x7fu << RTC_MR_CORRECTION_Pos) /**< \brief (RTC_MR) Slow Clock Correction */
#define RTC_MR_CORRECTION(value) ((RTC_MR_CORRECTION_Msk & ((value) << RTC_MR_CORRECTION_Pos)))
#define RTC_MR_HIGHPPM (0x1u << 15) /**< \brief (RTC_MR) HIGH PPM Correction */
#define RTC_MR_OUT0_Pos 16
#define RTC_MR_OUT0_Msk (0x7u << RTC_MR_OUT0_Pos) /**< \brief (RTC_MR) All ADC Channel Trigger Event Source Selection */
#define RTC_MR_OUT0(value) ((RTC_MR_OUT0_Msk & ((value) << RTC_MR_OUT0_Pos)))
#define   RTC_MR_OUT0_NO_WAVE (0x0u << 16) /**< \brief (RTC_MR) No waveform, stuck at '0' */
#define   RTC_MR_OUT0_FREQ1HZ (0x1u << 16) /**< \brief (RTC_MR) 1 Hz square wave */
#define   RTC_MR_OUT0_FREQ32HZ (0x2u << 16) /**< \brief (RTC_MR) 32 Hz square wave */
#define   RTC_MR_OUT0_FREQ64HZ (0x3u << 16) /**< \brief (RTC_MR) 64 Hz square wave */
#define   RTC_MR_OUT0_FREQ512HZ (0x4u << 16) /**< \brief (RTC_MR) 512 Hz square wave */
#define   RTC_MR_OUT0_ALARM_FLAG (0x6u << 16) /**< \brief (RTC_MR) Output is a copy of the alarm flag */
#define RTC_MR_OUT1_Pos 20
#define RTC_MR_OUT1_Msk (0x7u << RTC_MR_OUT1_Pos) /**< \brief (RTC_MR) ADC Last Channel Trigger Event Source Selection */
#define RTC_MR_OUT1(value) ((RTC_MR_OUT1_Msk & ((value) << RTC_MR_OUT1_Pos)))
#define   RTC_MR_OUT1_NO_WAVE (0x0u << 20) /**< \brief (RTC_MR) No waveform, stuck at '0' */
#define   RTC_MR_OUT1_FREQ1HZ (0x1u << 20) /**< \brief (RTC_MR) 1 Hz square wave */
#define   RTC_MR_OUT1_FREQ32HZ (0x2u << 20) /**< \brief (RTC_MR) 32 Hz square wave */
#define   RTC_MR_OUT1_FREQ64HZ (0x3u << 20) /**< \brief (RTC_MR) 64 Hz square wave */
#define   RTC_MR_OUT1_FREQ512HZ (0x4u << 20) /**< \brief (RTC_MR) 512 Hz square wave */
#define   RTC_MR_OUT1_ALARM_FLAG (0x6u << 20) /**< \brief (RTC_MR) Output is a copy of the alarm flag */
/* -------- RTC_TIMR : (RTC Offset: 0x08) Time Register -------- */
#define RTC_TIMR_SEC_Pos 0
#define RTC_TIMR_SEC_Msk (0x7fu << RTC_TIMR_SEC_Pos) /**< \brief (RTC_TIMR) Current Second */
#define RTC_TIMR_SEC(value) ((RTC_TIMR_SEC_Msk & ((value) << RTC_TIMR_SEC_Pos)))
#define RTC_TIMR_MIN_Pos 8
#define RTC_TIMR_MIN_Msk (0x7fu << RTC_TIMR_MIN_Pos) /**< \brief (RTC_TIMR) Current Minute */
#define RTC_TIMR_MIN(value) ((RTC_TIMR_MIN_Msk & ((value) << RTC_TIMR_MIN_Pos)))
#define RTC_TIMR_HOUR_Pos 16
#define RTC_TIMR_HOUR_Msk (0x3fu << RTC_TIMR_HOUR_Pos) /**< \brief (RTC_TIMR) Current Hour */
#define RTC_TIMR_HOUR(value) ((RTC_TIMR_HOUR_Msk & ((value) << RTC_TIMR_HOUR_Pos)))
#define RTC_TIMR_AMPM (0x1u << 22) /**< \brief (RTC_TIMR) Ante Meridiem Post Meridiem Indicator */
#define RTC_TIMR_UTC_TIME_Pos 0
#define RTC_TIMR_UTC_TIME_Msk (0xffffffffu << RTC_TIMR_UTC_TIME_Pos) /**< \brief (RTC_TIMR) Current UTC Time */
#define RTC_TIMR_UTC_TIME(value) ((RTC_TIMR_UTC_TIME_Msk & ((value) << RTC_TIMR_UTC_TIME_Pos)))
/* -------- RTC_CALR : (RTC Offset: 0x0C) Calendar Register -------- */
#define RTC_CALR_CENT_Pos 0
#define RTC_CALR_CENT_Msk (0x7fu << RTC_CALR_CENT_Pos) /**< \brief (RTC_CALR) Current Century */
#define RTC_CALR_CENT(value) ((RTC_CALR_CENT_Msk & ((value) << RTC_CALR_CENT_Pos)))
#define RTC_CALR_YEAR_Pos 8
#define RTC_CALR_YEAR_Msk (0xffu << RTC_CALR_YEAR_Pos) /**< \brief (RTC_CALR) Current Year */
#define RTC_CALR_YEAR(value) ((RTC_CALR_YEAR_Msk & ((value) << RTC_CALR_YEAR_Pos)))
#define RTC_CALR_MONTH_Pos 16
#define RTC_CALR_MONTH_Msk (0x1fu << RTC_CALR_MONTH_Pos) /**< \brief (RTC_CALR) Current Month */
#define RTC_CALR_MONTH(value) ((RTC_CALR_MONTH_Msk & ((value) << RTC_CALR_MONTH_Pos)))
#define RTC_CALR_DAY_Pos 21
#define RTC_CALR_DAY_Msk (0x7u << RTC_CALR_DAY_Pos) /**< \brief (RTC_CALR) Current Day in Current Week */
#define RTC_CALR_DAY(value) ((RTC_CALR_DAY_Msk & ((value) << RTC_CALR_DAY_Pos)))
#define RTC_CALR_DATE_Pos 24
#define RTC_CALR_DATE_Msk (0x3fu << RTC_CALR_DATE_Pos) /**< \brief (RTC_CALR) Current Day in Current Month */
#define RTC_CALR_DATE(value) ((RTC_CALR_DATE_Msk & ((value) << RTC_CALR_DATE_Pos)))
/* -------- RTC_TIMALR : (RTC Offset: 0x10) Time Alarm Register -------- */
#define RTC_TIMALR_SEC_Pos 0
#define RTC_TIMALR_SEC_Msk (0x7fu << RTC_TIMALR_SEC_Pos) /**< \brief (RTC_TIMALR) Second Alarm */
#define RTC_TIMALR_SEC(value) ((RTC_TIMALR_SEC_Msk & ((value) << RTC_TIMALR_SEC_Pos)))
#define RTC_TIMALR_SECEN (0x1u << 7) /**< \brief (RTC_TIMALR) Second Alarm Enable */
#define RTC_TIMALR_MIN_Pos 8
#define RTC_TIMALR_MIN_Msk (0x7fu << RTC_TIMALR_MIN_Pos) /**< \brief (RTC_TIMALR) Minute Alarm */
#define RTC_TIMALR_MIN(value) ((RTC_TIMALR_MIN_Msk & ((value) << RTC_TIMALR_MIN_Pos)))
#define RTC_TIMALR_MINEN (0x1u << 15) /**< \brief (RTC_TIMALR) Minute Alarm Enable */
#define RTC_TIMALR_HOUR_Pos 16
#define RTC_TIMALR_HOUR_Msk (0x3fu << RTC_TIMALR_HOUR_Pos) /**< \brief (RTC_TIMALR) Hour Alarm */
#define RTC_TIMALR_HOUR(value) ((RTC_TIMALR_HOUR_Msk & ((value) << RTC_TIMALR_HOUR_Pos)))
#define RTC_TIMALR_AMPM (0x1u << 22) /**< \brief (RTC_TIMALR) AM/PM Indicator */
#define RTC_TIMALR_HOUREN (0x1u << 23) /**< \brief (RTC_TIMALR) Hour Alarm Enable */
#define RTC_TIMALR_UTC_TIME_Pos 0
#define RTC_TIMALR_UTC_TIME_Msk (0xffffffffu << RTC_TIMALR_UTC_TIME_Pos) /**< \brief (RTC_TIMALR) UTC_TIME Alarm */
#define RTC_TIMALR_UTC_TIME(value) ((RTC_TIMALR_UTC_TIME_Msk & ((value) << RTC_TIMALR_UTC_TIME_Pos)))
/* -------- RTC_CALALR : (RTC Offset: 0x14) Calendar Alarm Register -------- */
#define RTC_CALALR_MONTH_Pos 16
#define RTC_CALALR_MONTH_Msk (0x1fu << RTC_CALALR_MONTH_Pos) /**< \brief (RTC_CALALR) Month Alarm */
#define RTC_CALALR_MONTH(value) ((RTC_CALALR_MONTH_Msk & ((value) << RTC_CALALR_MONTH_Pos)))
#define RTC_CALALR_MTHEN (0x1u << 23) /**< \brief (RTC_CALALR) Month Alarm Enable */
#define RTC_CALALR_DATE_Pos 24
#define RTC_CALALR_DATE_Msk (0x3fu << RTC_CALALR_DATE_Pos) /**< \brief (RTC_CALALR) Date Alarm */
#define RTC_CALALR_DATE(value) ((RTC_CALALR_DATE_Msk & ((value) << RTC_CALALR_DATE_Pos)))
#define RTC_CALALR_DATEEN (0x1u << 31) /**< \brief (RTC_CALALR) Date Alarm Enable */
#define RTC_CALALR_UTCEN (0x1u << 0) /**< \brief (RTC_CALALR) UTC Alarm Enable */
/* -------- RTC_SR : (RTC Offset: 0x18) Status Register -------- */
#define RTC_SR_ACKUPD (0x1u << 0) /**< \brief (RTC_SR) Acknowledge for Update */
#define   RTC_SR_ACKUPD_FREERUN (0x0u << 0) /**< \brief (RTC_SR) Time and calendar registers cannot be updated. */
#define   RTC_SR_ACKUPD_UPDATE (0x1u << 0) /**< \brief (RTC_SR) Time and calendar registers can be updated. */
#define RTC_SR_ALARM (0x1u << 1) /**< \brief (RTC_SR) Alarm Flag */
#define   RTC_SR_ALARM_NO_ALARMEVENT (0x0u << 1) /**< \brief (RTC_SR) No alarm matching condition occurred. */
#define   RTC_SR_ALARM_ALARMEVENT (0x1u << 1) /**< \brief (RTC_SR) An alarm matching condition has occurred. */
#define RTC_SR_SEC (0x1u << 2) /**< \brief (RTC_SR) Second Event */
#define   RTC_SR_SEC_NO_SECEVENT (0x0u << 2) /**< \brief (RTC_SR) No second event has occurred since the last clear. */
#define   RTC_SR_SEC_SECEVENT (0x1u << 2) /**< \brief (RTC_SR) At least one second event has occurred since the last clear. */
#define RTC_SR_TIMEV (0x1u << 3) /**< \brief (RTC_SR) Time Event */
#define   RTC_SR_TIMEV_NO_TIMEVENT (0x0u << 3) /**< \brief (RTC_SR) No time event has occurred since the last clear. */
#define   RTC_SR_TIMEV_TIMEVENT (0x1u << 3) /**< \brief (RTC_SR) At least one time event has occurred since the last clear. */
#define RTC_SR_CALEV (0x1u << 4) /**< \brief (RTC_SR) Calendar Event */
#define   RTC_SR_CALEV_NO_CALEVENT (0x0u << 4) /**< \brief (RTC_SR) No calendar event has occurred since the last clear. */
#define   RTC_SR_CALEV_CALEVENT (0x1u << 4) /**< \brief (RTC_SR) At least one calendar event has occurred since the last clear. */
#define RTC_SR_TDERR (0x1u << 5) /**< \brief (RTC_SR) Time and/or Date Free Running Error */
#define   RTC_SR_TDERR_CORRECT (0x0u << 5) /**< \brief (RTC_SR) The internal free running counters are carrying valid values since the last read of the Status Register (RTC_SR). */
#define   RTC_SR_TDERR_ERR_TIMEDATE (0x1u << 5) /**< \brief (RTC_SR) The internal free running counters have been corrupted (invalid date or time, non-BCD values) since the last read and/or they are still invalid. */
/* -------- RTC_SCCR : (RTC Offset: 0x1C) Status Clear Command Register -------- */
#define RTC_SCCR_ACKCLR (0x1u << 0) /**< \brief (RTC_SCCR) Acknowledge Clear */
#define RTC_SCCR_ALRCLR (0x1u << 1) /**< \brief (RTC_SCCR) Alarm Clear */
#define RTC_SCCR_SECCLR (0x1u << 2) /**< \brief (RTC_SCCR) Second Clear */
#define RTC_SCCR_TIMCLR (0x1u << 3) /**< \brief (RTC_SCCR) Time Clear */
#define RTC_SCCR_CALCLR (0x1u << 4) /**< \brief (RTC_SCCR) Calendar Clear */
#define RTC_SCCR_TDERRCLR (0x1u << 5) /**< \brief (RTC_SCCR) Time and/or Date Free Running Error Clear */
/* -------- RTC_IER : (RTC Offset: 0x20) Interrupt Enable Register -------- */
#define RTC_IER_ACKEN (0x1u << 0) /**< \brief (RTC_IER) Acknowledge Update Interrupt Enable */
#define RTC_IER_ALREN (0x1u << 1) /**< \brief (RTC_IER) Alarm Interrupt Enable */
#define RTC_IER_SECEN (0x1u << 2) /**< \brief (RTC_IER) Second Event Interrupt Enable */
#define RTC_IER_TIMEN (0x1u << 3) /**< \brief (RTC_IER) Time Event Interrupt Enable */
#define RTC_IER_CALEN (0x1u << 4) /**< \brief (RTC_IER) Calendar Event Interrupt Enable */
#define RTC_IER_TDERREN (0x1u << 5) /**< \brief (RTC_IER) Time and/or Date Error Interrupt Enable */
/* -------- RTC_IDR : (RTC Offset: 0x24) Interrupt Disable Register -------- */
#define RTC_IDR_ACKDIS (0x1u << 0) /**< \brief (RTC_IDR) Acknowledge Update Interrupt Disable */
#define RTC_IDR_ALRDIS (0x1u << 1) /**< \brief (RTC_IDR) Alarm Interrupt Disable */
#define RTC_IDR_SECDIS (0x1u << 2) /**< \brief (RTC_IDR) Second Event Interrupt Disable */
#define RTC_IDR_TIMDIS (0x1u << 3) /**< \brief (RTC_IDR) Time Event Interrupt Disable */
#define RTC_IDR_CALDIS (0x1u << 4) /**< \brief (RTC_IDR) Calendar Event Interrupt Disable */
#define RTC_IDR_TDERRDIS (0x1u << 5) /**< \brief (RTC_IDR) Time and/or Date Error Interrupt Disable */
/* -------- RTC_IMR : (RTC Offset: 0x28) Interrupt Mask Register -------- */
#define RTC_IMR_ACK (0x1u << 0) /**< \brief (RTC_IMR) Acknowledge Update Interrupt Mask */
#define RTC_IMR_ALR (0x1u << 1) /**< \brief (RTC_IMR) Alarm Interrupt Mask */
#define RTC_IMR_SEC (0x1u << 2) /**< \brief (RTC_IMR) Second Event Interrupt Mask */
#define RTC_IMR_TIM (0x1u << 3) /**< \brief (RTC_IMR) Time Event Interrupt Mask */
#define RTC_IMR_CAL (0x1u << 4) /**< \brief (RTC_IMR) Calendar Event Interrupt Mask */
#define RTC_IMR_TDERR (0x1u << 5) /**< \brief (RTC_IMR) Time and/or Date Error Mask */
/* -------- RTC_VER : (RTC Offset: 0x2C) Valid Entry Register -------- */
#define RTC_VER_NVTIM (0x1u << 0) /**< \brief (RTC_VER) Non-valid Time */
#define RTC_VER_NVCAL (0x1u << 1) /**< \brief (RTC_VER) Non-valid Calendar */
#define RTC_VER_NVTIMALR (0x1u << 2) /**< \brief (RTC_VER) Non-valid Time Alarm */
#define RTC_VER_NVCALALR (0x1u << 3) /**< \brief (RTC_VER) Non-valid Calendar Alarm */
/* -------- RTC_TSTR : (RTC Offset: N/A) TimeStamp Time Register 0 -------- */
#define RTC_TSTR_SEC_Pos 0
#define RTC_TSTR_SEC_Msk (0x7fu << RTC_TSTR_SEC_Pos) /**< \brief (RTC_TSTR) Seconds of the Tamper */
#define RTC_TSTR_MIN_Pos 8
#define RTC_TSTR_MIN_Msk (0x7fu << RTC_TSTR_MIN_Pos) /**< \brief (RTC_TSTR) Minutes of the Tamper */
#define RTC_TSTR_HOUR_Pos 16
#define RTC_TSTR_HOUR_Msk (0x3fu << RTC_TSTR_HOUR_Pos) /**< \brief (RTC_TSTR) Hours of the Tamper */
#define RTC_TSTR_AMPM (0x1u << 22) /**< \brief (RTC_TSTR) AM/PM Indicator of the Tamper */
#define RTC_TSTR_TEVCNT_Pos 24
#define RTC_TSTR_TEVCNT_Msk (0xfu << RTC_TSTR_TEVCNT_Pos) /**< \brief (RTC_TSTR) Tamper Events Counter */
#define RTC_TSTR_BACKUP (0x1u << 31) /**< \brief (RTC_TSTR) System Mode of the Tamper */
/* -------- RTC_TSDR : (RTC Offset: N/A) TimeStamp Date Register 0 -------- */
#define RTC_TSDR_CENT_Pos 0
#define RTC_TSDR_CENT_Msk (0x7fu << RTC_TSDR_CENT_Pos) /**< \brief (RTC_TSDR) Century of the Tamper */
#define RTC_TSDR_YEAR_Pos 8
#define RTC_TSDR_YEAR_Msk (0xffu << RTC_TSDR_YEAR_Pos) /**< \brief (RTC_TSDR) Year of the Tamper */
#define RTC_TSDR_MONTH_Pos 16
#define RTC_TSDR_MONTH_Msk (0x1fu << RTC_TSDR_MONTH_Pos) /**< \brief (RTC_TSDR) Month of the Tamper */
#define RTC_TSDR_DAY_Pos 21
#define RTC_TSDR_DAY_Msk (0x7u << RTC_TSDR_DAY_Pos) /**< \brief (RTC_TSDR) Day of the Tamper */
#define RTC_TSDR_DATE_Pos 24
#define RTC_TSDR_DATE_Msk (0x3fu << RTC_TSDR_DATE_Pos) /**< \brief (RTC_TSDR) Date of the Tamper */
#define RTC_TSDR_UTC_TIME_Pos 0
#define RTC_TSDR_UTC_TIME_Msk (0xffffffffu << RTC_TSDR_UTC_TIME_Pos) /**< \brief (RTC_TSDR) Time of the Tamper (UTC format) */
/* -------- RTC_TSSR : (RTC Offset: N/A) TimeStamp Source Register 0 -------- */
#define RTC_TSSR_SHLDM (0x1u << 0) /**< \brief (RTC_TSSR) Shield Monitor */
#define RTC_TSSR_DBLFM (0x1u << 1) /**< \brief (RTC_TSSR) Double Frequency Monitor */
#define RTC_TSSR_TST (0x1u << 2) /**< \brief (RTC_TSSR) Test Pin Monitor */
#define RTC_TSSR_JTAG (0x1u << 3) /**< \brief (RTC_TSSR) JTAG Pins Monitor */
#define RTC_TSSR_REGUL (0x1u << 4) /**< \brief (RTC_TSSR) Core Regulator Disconnection Monitor */
#define RTC_TSSR_MCKM (0x1u << 5) /**< \brief (RTC_TSSR) Master Clock Monitor */
#define RTC_TSSR_TPML (0x1u << 6) /**< \brief (RTC_TSSR) Low Temperature Monitor */
#define RTC_TSSR_TPMH (0x1u << 7) /**< \brief (RTC_TSSR) High Temperature Monitor */
#define RTC_TSSR_VDDRL (0x1u << 8) /**< \brief (RTC_TSSR) Low VDDDDR Voltage Monitor */
#define RTC_TSSR_VDDRH (0x1u << 9) /**< \brief (RTC_TSSR) High VDDDDR Voltage Monitor */
#define RTC_TSSR_VDDBUL (0x1u << 10) /**< \brief (RTC_TSSR) Low VDDBU Voltage Monitor */
#define RTC_TSSR_VDDBUH (0x1u << 11) /**< \brief (RTC_TSSR) High VDDBU Voltage Monitor */
#define RTC_TSSR_VDDCOREL (0x1u << 12) /**< \brief (RTC_TSSR) Low VDDCORE Voltage Monitor */
#define RTC_TSSR_VDDCOREH (0x1u << 13) /**< \brief (RTC_TSSR) High VDDCORE Voltage Monitor */
#define RTC_TSSR_VDDIOL (0x1u << 14) /**< \brief (RTC_TSSR) Low VDDIO Voltage Monitor */
#define RTC_TSSR_VDDIOH (0x1u << 15) /**< \brief (RTC_TSSR) High VDDIO Voltage Monitor */
#define RTC_TSSR_DET0 (0x1u << 16) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
#define RTC_TSSR_DET1 (0x1u << 17) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
#define RTC_TSSR_DET2 (0x1u << 18) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
#define RTC_TSSR_DET3 (0x1u << 19) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
#define RTC_TSSR_DET4 (0x1u << 20) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
#define RTC_TSSR_DET5 (0x1u << 21) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
#define RTC_TSSR_DET6 (0x1u << 22) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
#define RTC_TSSR_DET7 (0x1u << 23) /**< \brief (RTC_TSSR) PIOBU Intrusion Detector */
/* -------- RTC_MSR : (RTC Offset: 0xD0) Milliseconds Register -------- */
#define RTC_MSR_MS_Pos 0
#define RTC_MSR_MS_Msk (0x3ffu << RTC_MSR_MS_Pos) /**< \brief (RTC_MSR) Number of 1/1024 seconds elapsed within 1 second */
/* -------- RTC_WPMR : (RTC Offset: 0xE4) Write Protection Mode Register -------- */
#define RTC_WPMR_WPEN (0x1u << 0) /**< \brief (RTC_WPMR) Write Protection Enable */
#define RTC_WPMR_WPKEY_Pos 8
#define RTC_WPMR_WPKEY_Msk (0xffffffu << RTC_WPMR_WPKEY_Pos) /**< \brief (RTC_WPMR) Write Protection Key */
#define RTC_WPMR_WPKEY(value) ((RTC_WPMR_WPKEY_Msk & ((value) << RTC_WPMR_WPKEY_Pos)))
#define   RTC_WPMR_WPKEY_PASSWD (0x525443u << 8) /**< \brief (RTC_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0. */
/* -------- RTC_VERSION : (RTC Offset: 0xFC) Version Register -------- */
#define RTC_VERSION_VERSION_Pos 0
#define RTC_VERSION_VERSION_Msk (0xfffu << RTC_VERSION_VERSION_Pos) /**< \brief (RTC_VERSION) Version of the Hardware Module */
#define RTC_VERSION_MFN_Pos 16
#define RTC_VERSION_MFN_Msk (0x7u << RTC_VERSION_MFN_Pos) /**< \brief (RTC_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_RTC_COMPONENT_ */
