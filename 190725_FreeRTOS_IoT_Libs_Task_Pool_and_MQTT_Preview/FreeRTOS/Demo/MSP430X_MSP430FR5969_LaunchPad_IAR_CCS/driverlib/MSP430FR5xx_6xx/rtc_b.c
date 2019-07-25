/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// rtc_b.c - Driver for the rtc_b Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup rtc_b_api rtc_b
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_RTC_B__
#include "rtc_b.h"

#include <assert.h>

void RTC_B_startClock(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_RTCCTL01_H) &= ~(RTCHOLD_H);
}

void RTC_B_holdClock(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_RTCCTL01_H) |= RTCHOLD_H;
}

void RTC_B_setCalibrationFrequency(uint16_t baseAddress,
                                   uint16_t frequencySelect)
{
    HWREG16(baseAddress + OFS_RTCCTL23) &= ~(RTCCALF_3);
    HWREG16(baseAddress + OFS_RTCCTL23) |= frequencySelect;
}

void RTC_B_setCalibrationData(uint16_t baseAddress,
                              uint8_t offsetDirection,
                              uint8_t offsetValue)
{
    HWREG8(baseAddress + OFS_RTCCTL23_L) = offsetValue + offsetDirection;
}

void RTC_B_initCalendar(uint16_t baseAddress,
                        Calendar *CalendarTime,
                        uint16_t formatSelect)
{
    HWREG8(baseAddress + OFS_RTCCTL01_H) |= RTCHOLD_H;

    HWREG16(baseAddress + OFS_RTCCTL01) &= ~(RTCBCD);
    HWREG16(baseAddress + OFS_RTCCTL01) |= formatSelect;

    HWREG8(baseAddress + OFS_RTCTIM0_L) = CalendarTime->Seconds;
    HWREG8(baseAddress + OFS_RTCTIM0_H) = CalendarTime->Minutes;
    HWREG8(baseAddress + OFS_RTCTIM1_L) = CalendarTime->Hours;
    HWREG8(baseAddress + OFS_RTCTIM1_H) = CalendarTime->DayOfWeek;
    HWREG8(baseAddress + OFS_RTCDATE_L) = CalendarTime->DayOfMonth;
    HWREG8(baseAddress + OFS_RTCDATE_H) = CalendarTime->Month;
    HWREG16(baseAddress + OFS_RTCYEAR) = CalendarTime->Year;
}

Calendar RTC_B_getCalendarTime(uint16_t baseAddress)
{
    Calendar tempCal;

    while(!(HWREG16(baseAddress + OFS_RTCCTL01) & RTCRDY))
    {
        ;
    }

    tempCal.Seconds = HWREG8(baseAddress + OFS_RTCTIM0_L);
    tempCal.Minutes = HWREG8(baseAddress + OFS_RTCTIM0_H);
    tempCal.Hours = HWREG8(baseAddress + OFS_RTCTIM1_L);
    tempCal.DayOfWeek = HWREG8(baseAddress + OFS_RTCTIM1_H);
    tempCal.DayOfMonth = HWREG8(baseAddress + OFS_RTCDATE_L);
    tempCal.Month = HWREG8(baseAddress + OFS_RTCDATE_H);
    tempCal.Year = HWREG16(baseAddress + OFS_RTCYEAR);

    return (tempCal);
}

void RTC_B_configureCalendarAlarm(uint16_t baseAddress,
                                  RTC_B_configureCalendarAlarmParam *param)
{
    //Each of these is XORed with 0x80 to turn on if an integer is passed,
    //or turn OFF if RTC_B_ALARM_OFF (0x80) is passed.
    HWREG8(baseAddress + OFS_RTCAMINHR_L) = (param->minutesAlarm ^ 0x80);
    HWREG8(baseAddress + OFS_RTCAMINHR_H) = (param->hoursAlarm ^ 0x80);
    HWREG8(baseAddress + OFS_RTCADOWDAY_L) = (param->dayOfWeekAlarm ^ 0x80);
    HWREG8(baseAddress + OFS_RTCADOWDAY_H) = (param->dayOfMonthAlarm ^ 0x80);
}

void RTC_B_setCalendarEvent(uint16_t baseAddress,
                            uint16_t eventSelect)
{
    HWREG16(baseAddress + OFS_RTCCTL01) &= ~(RTCTEV_3); //Reset bits
    HWREG16(baseAddress + OFS_RTCCTL01) |= eventSelect;
}

void RTC_B_definePrescaleEvent(uint16_t baseAddress,
                               uint8_t prescaleSelect,
                               uint8_t prescaleEventDivider)
{
    HWREG8(baseAddress + OFS_RTCPS0CTL_L + prescaleSelect) &= ~(RT0IP_7);
    HWREG8(baseAddress + OFS_RTCPS0CTL_L +
           prescaleSelect) |= prescaleEventDivider;
}

uint8_t RTC_B_getPrescaleValue(uint16_t baseAddress,
                               uint8_t prescaleSelect)
{
    if(RTC_B_PRESCALE_0 == prescaleSelect)
    {
        return (HWREG8(baseAddress + OFS_RTCPS_L));
    }
    else if(RTC_B_PRESCALE_1 == prescaleSelect)
    {
        return (HWREG8(baseAddress + OFS_RTCPS_H));
    }
    else
    {
        return (0);
    }
}

void RTC_B_setPrescaleValue(uint16_t baseAddress,
                            uint8_t prescaleSelect,
                            uint8_t prescaleCounterValue)
{
    if(RTC_B_PRESCALE_0 == prescaleSelect)
    {
        HWREG8(baseAddress + OFS_RTCPS_L) = prescaleCounterValue;
    }
    else if(RTC_B_PRESCALE_1 == prescaleSelect)
    {
        HWREG8(baseAddress + OFS_RTCPS_H) = prescaleCounterValue;
    }
}

void RTC_B_enableInterrupt(uint16_t baseAddress,
                           uint8_t interruptMask)
{
    if(interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE))
    {
        HWREG8(baseAddress + OFS_RTCCTL01_L) |=
            (interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE));
    }

    if(interruptMask & RTC_B_PRESCALE_TIMER0_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS0CTL) |= RT0PSIE;
    }

    if(interruptMask & RTC_B_PRESCALE_TIMER1_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS1CTL) |= RT1PSIE;
    }
}

void RTC_B_disableInterrupt(uint16_t baseAddress,
                            uint8_t interruptMask)
{
    if(interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE))
    {
        HWREG8(baseAddress + OFS_RTCCTL01_L) &=
            ~(interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE));
    }

    if(interruptMask & RTC_B_PRESCALE_TIMER0_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS0CTL) &= ~(RT0PSIE);
    }

    if(interruptMask & RTC_B_PRESCALE_TIMER1_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS1CTL) &= ~(RT1PSIE);
    }
}

uint8_t RTC_B_getInterruptStatus(uint16_t baseAddress,
                                 uint8_t interruptFlagMask)
{
    uint8_t tempInterruptFlagMask = 0x0000;

    tempInterruptFlagMask |= (HWREG8(baseAddress + OFS_RTCCTL01_L)
                              & ((interruptFlagMask >> 4)
                                 & (RTCOFIFG +
                                    RTCTEVIFG +
                                    RTCAIFG +
                                    RTCRDYIFG)));

    tempInterruptFlagMask = tempInterruptFlagMask << 4;

    if(interruptFlagMask & RTC_B_PRESCALE_TIMER0_INTERRUPT)
    {
        if(HWREG8(baseAddress + OFS_RTCPS0CTL) & RT0PSIFG)
        {
            tempInterruptFlagMask |= RTC_B_PRESCALE_TIMER0_INTERRUPT;
        }
    }

    if(interruptFlagMask & RTC_B_PRESCALE_TIMER1_INTERRUPT)
    {
        if(HWREG8(baseAddress + OFS_RTCPS1CTL) & RT1PSIFG)
        {
            tempInterruptFlagMask |= RTC_B_PRESCALE_TIMER1_INTERRUPT;
        }
    }

    return (tempInterruptFlagMask);
}

void RTC_B_clearInterrupt(uint16_t baseAddress,
                          uint8_t interruptFlagMask)
{
    if(interruptFlagMask & (RTC_B_TIME_EVENT_INTERRUPT +
                            RTC_B_CLOCK_ALARM_INTERRUPT +
                            RTC_B_CLOCK_READ_READY_INTERRUPT +
                            RTC_B_OSCILLATOR_FAULT_INTERRUPT))
    {
        HWREG8(baseAddress + OFS_RTCCTL01_L) &=
            ~((interruptFlagMask >> 4) & (RTCOFIFG +
                                          RTCTEVIFG +
                                          RTCAIFG +
                                          RTCRDYIFG));
    }

    if(interruptFlagMask & RTC_B_PRESCALE_TIMER0_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS0CTL) &= ~(RT0PSIFG);
    }

    if(interruptFlagMask & RTC_B_PRESCALE_TIMER1_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS1CTL) &= ~(RT1PSIFG);
    }
}

uint16_t RTC_B_convertBCDToBinary(uint16_t baseAddress,
                                  uint16_t valueToConvert)
{
    HWREG16(baseAddress + OFS_BCD2BIN) = valueToConvert;
    return (HWREG16(baseAddress + OFS_BCD2BIN));
}

uint16_t RTC_B_convertBinaryToBCD(uint16_t baseAddress,
                                  uint16_t valueToConvert)
{
    HWREG16(baseAddress + OFS_BIN2BCD) = valueToConvert;
    return (HWREG16(baseAddress + OFS_BIN2BCD));
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for rtc_b_api
//! @}
//
//*****************************************************************************
