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
// rtc_c.c - Driver for the rtc_c Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup rtc_c_api rtc_c
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_RTC_C__
#include "rtc_c.h"

#include <assert.h>

void RTC_C_startClock(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
    HWREG8(baseAddress + OFS_RTCCTL13_L) &= ~(RTCHOLD);
    HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
}

void RTC_C_holdClock(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
    HWREG8(baseAddress + OFS_RTCCTL13_L) |= RTCHOLD;
    HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
}

void RTC_C_setCalibrationFrequency(uint16_t baseAddress,
                                   uint16_t frequencySelect)
{
    HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
    HWREG16(baseAddress + OFS_RTCCTL13) &= ~(RTCCALF_3);
    HWREG16(baseAddress + OFS_RTCCTL13) |= frequencySelect;
    HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
}

void RTC_C_setCalibrationData(uint16_t baseAddress,
                              uint8_t offsetDirection,
                              uint8_t offsetValue)
{
    HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
    HWREG16(baseAddress + OFS_RTCOCAL) = offsetValue + offsetDirection;
    HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
}

void RTC_C_initCounter(uint16_t baseAddress,
                       uint16_t clockSelect,
                       uint16_t counterSizeSelect)
{
    HWREG8(baseAddress + OFS_RTCCTL13) |= RTCHOLD;
    HWREG8(baseAddress + OFS_RTCCTL13) &= ~(RTCMODE);

    HWREG16(baseAddress + OFS_RTCCTL13) &= ~(RTCSSEL_3 | RTCTEV_3);
    HWREG16(baseAddress + OFS_RTCCTL13) |= clockSelect + counterSizeSelect;
}

bool RTC_C_setTemperatureCompensation(uint16_t baseAddress,
                                      uint16_t offsetDirection,
                                      uint8_t offsetValue)
{
    while(!(HWREG8(baseAddress + OFS_RTCTCMP_H) & RTCTCRDY_H))
    {
        ;
    }

    HWREG16(baseAddress + OFS_RTCTCMP) = offsetValue + offsetDirection;

    if(HWREG8(baseAddress + OFS_RTCTCMP_H) & RTCTCOK_H)
    {
        return(STATUS_SUCCESS);
    }
    else
    {
        return(STATUS_FAIL);
    }
}

void RTC_C_initCalendar(uint16_t baseAddress,
                        Calendar *CalendarTime,
                        uint16_t formatSelect)
{
    HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;

    HWREG8(baseAddress + OFS_RTCCTL13_L) |= RTCHOLD;

    HWREG16(baseAddress + OFS_RTCCTL13_L) &= ~(RTCBCD);
    HWREG16(baseAddress + OFS_RTCCTL13_L) |= formatSelect;

    HWREG8(baseAddress + OFS_RTCTIM0_L) = CalendarTime->Seconds;
    HWREG8(baseAddress + OFS_RTCTIM0_H) = CalendarTime->Minutes;
    HWREG8(baseAddress + OFS_RTCTIM1_L) = CalendarTime->Hours;
    HWREG8(baseAddress + OFS_RTCTIM1_H) = CalendarTime->DayOfWeek;
    HWREG8(baseAddress + OFS_RTCDATE_L) = CalendarTime->DayOfMonth;
    HWREG8(baseAddress + OFS_RTCDATE_H) = CalendarTime->Month;
    HWREG16(baseAddress + OFS_RTCYEAR) = CalendarTime->Year;

    HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
}

Calendar RTC_C_getCalendarTime(uint16_t baseAddress)
{
    Calendar tempCal;

    while(!(HWREG8(baseAddress + OFS_RTCCTL13_L) & RTCRDY))
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

void RTC_C_configureCalendarAlarm(uint16_t baseAddress,
                                  RTC_C_configureCalendarAlarmParam *param)
{
    //Each of these is XORed with 0x80 to turn on if an integer is passed,
    //or turn OFF if RTC_C_ALARM_OFF (0x80) is passed.
    HWREG8(baseAddress + OFS_RTCAMINHR_L) = (param->minutesAlarm ^ 0x80);
    HWREG8(baseAddress + OFS_RTCAMINHR_H) = (param->hoursAlarm ^ 0x80);
    HWREG8(baseAddress + OFS_RTCADOWDAY_L) = (param->dayOfWeekAlarm ^ 0x80);
    HWREG8(baseAddress + OFS_RTCADOWDAY_H) = (param->dayOfMonthAlarm ^ 0x80);
}

void RTC_C_setCalendarEvent(uint16_t baseAddress,
                            uint16_t eventSelect)
{
    HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
    HWREG8(baseAddress + OFS_RTCCTL13_L) &= ~(RTCTEV_3); //Reset bits
    HWREG8(baseAddress + OFS_RTCCTL13_L) |= eventSelect;
    HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
}

uint32_t RTC_C_getCounterValue(uint16_t baseAddress)
{
    if((HWREG8(baseAddress + OFS_RTCCTL13) & RTCHOLD)
       || (HWREG8(baseAddress + OFS_RTCPS1CTL) & RT1PSHOLD))
    {
        return (0);
    }

    uint32_t counterValue_L = HWREG16(baseAddress + OFS_RTCTIM0);
    uint32_t counterValue_H = HWREG16(baseAddress + OFS_RTCTIM1);
    return ((counterValue_H << 16) + counterValue_L);
}

void RTC_C_setCounterValue(uint16_t baseAddress,
                           uint32_t counterValue)
{
    uint16_t mode = HWREG16(baseAddress + OFS_RTCCTL13) & RTCTEV_3;

    if(mode == RTC_C_COUNTERSIZE_8BIT && counterValue > 0xF)
    {
        counterValue = 0xF;
    }
    else if(mode == RTC_C_COUNTERSIZE_16BIT && counterValue > 0xFF)
    {
        counterValue = 0xFF;
    }
    else if(mode == RTC_C_COUNTERSIZE_24BIT && counterValue > 0xFFFFFF)
    {
        counterValue = 0xFFFFFF;
    }

    HWREG16(baseAddress + OFS_RTCTIM0) = counterValue;
    HWREG16(baseAddress + OFS_RTCTIM1) = (counterValue >> 16);
}

void RTC_C_initCounterPrescale(uint16_t baseAddress,
                               uint8_t prescaleSelect,
                               uint16_t prescaleClockSelect,
                               uint16_t prescaleDivider)
{
    //Reset bits and set clock select
    HWREG16(baseAddress + OFS_RTCPS0CTL + prescaleSelect) =
        prescaleClockSelect + prescaleDivider;
}

void RTC_C_holdCounterPrescale(uint16_t baseAddress,
                               uint8_t prescaleSelect)
{
    HWREG8(baseAddress + OFS_RTCPS0CTL_H + prescaleSelect) |= RT0PSHOLD_H;
}

void RTC_C_startCounterPrescale(uint16_t baseAddress,
                                uint8_t prescaleSelect)
{
    HWREG8(baseAddress + OFS_RTCPS0CTL_H + prescaleSelect) &= ~(RT0PSHOLD_H);
}

void RTC_C_definePrescaleEvent(uint16_t baseAddress,
                               uint8_t prescaleSelect,
                               uint8_t prescaleEventDivider)
{
    HWREG8(baseAddress + OFS_RTCPS0CTL_L + prescaleSelect) &= ~(RT0IP_7);
    HWREG8(baseAddress + OFS_RTCPS0CTL_L +
           prescaleSelect) |= prescaleEventDivider;
}

uint8_t RTC_C_getPrescaleValue(uint16_t baseAddress,
                               uint8_t prescaleSelect)
{
    if(RTC_C_PRESCALE_0 == prescaleSelect)
    {
        return (HWREG8(baseAddress + OFS_RTCPS_L));
    }
    else if(RTC_C_PRESCALE_1 == prescaleSelect)
    {
        return (HWREG8(baseAddress + OFS_RTCPS_H));
    }
    else
    {
        return (0);
    }
}

void RTC_C_setPrescaleValue(uint16_t baseAddress,
                            uint8_t prescaleSelect,
                            uint8_t prescaleCounterValue)
{
    HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
    if(RTC_C_PRESCALE_0 == prescaleSelect)
    {
        HWREG8(baseAddress + OFS_RTCPS_L) = prescaleCounterValue;
    }
    else if(RTC_C_PRESCALE_1 == prescaleSelect)
    {
        HWREG8(baseAddress + OFS_RTCPS_H) = prescaleCounterValue;
    }
    HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
}

void RTC_C_enableInterrupt(uint16_t baseAddress,
                           uint8_t interruptMask)
{
    if(interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE))
    {
        HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
        HWREG8(baseAddress + OFS_RTCCTL0_L) |=
            (interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE));
        HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
    }

    if(interruptMask & RTC_C_PRESCALE_TIMER0_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS0CTL_L) |= RT0PSIE;
    }

    if(interruptMask & RTC_C_PRESCALE_TIMER1_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS1CTL_L) |= RT1PSIE;
    }
}

void RTC_C_disableInterrupt(uint16_t baseAddress,
                            uint8_t interruptMask)
{
    if(interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE))
    {
        HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
        HWREG8(baseAddress + OFS_RTCCTL0_L) &=
            ~(interruptMask & (RTCOFIE + RTCTEVIE + RTCAIE + RTCRDYIE));
        HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
    }

    if(interruptMask & RTC_C_PRESCALE_TIMER0_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS0CTL_L) &= ~(RT0PSIE);
    }

    if(interruptMask & RTC_C_PRESCALE_TIMER1_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS1CTL_L) &= ~(RT1PSIE);
    }
}

uint8_t RTC_C_getInterruptStatus(uint16_t baseAddress,
                                 uint8_t interruptFlagMask)
{
    uint8_t tempInterruptFlagMask = 0x0000;

    tempInterruptFlagMask |= (HWREG8(baseAddress + OFS_RTCCTL0_L)
                              & ((interruptFlagMask >> 4)
                                 & (RTCOFIFG +
                                    RTCTEVIFG +
                                    RTCAIFG +
                                    RTCRDYIFG)));

    tempInterruptFlagMask = tempInterruptFlagMask << 4;

    if(interruptFlagMask & RTC_C_PRESCALE_TIMER0_INTERRUPT)
    {
        if(HWREG8(baseAddress + OFS_RTCPS0CTL_L) & RT0PSIFG)
        {
            tempInterruptFlagMask |= RTC_C_PRESCALE_TIMER0_INTERRUPT;
        }
    }

    if(interruptFlagMask & RTC_C_PRESCALE_TIMER1_INTERRUPT)
    {
        if(HWREG8(baseAddress + OFS_RTCPS1CTL_L) & RT1PSIFG)
        {
            tempInterruptFlagMask |= RTC_C_PRESCALE_TIMER1_INTERRUPT;
        }
    }

    return (tempInterruptFlagMask);
}

void RTC_C_clearInterrupt(uint16_t baseAddress,
                          uint8_t interruptFlagMask)
{
    if(interruptFlagMask & (RTC_C_TIME_EVENT_INTERRUPT +
                            RTC_C_CLOCK_ALARM_INTERRUPT +
                            RTC_C_CLOCK_READ_READY_INTERRUPT +
                            RTC_C_OSCILLATOR_FAULT_INTERRUPT))
    {
        HWREG8(baseAddress + OFS_RTCCTL0_H) = RTCKEY_H;
        HWREG8(baseAddress + OFS_RTCCTL0_L) &=
            ~((interruptFlagMask >> 4) & (RTCOFIFG +
                                          RTCTEVIFG +
                                          RTCAIFG +
                                          RTCRDYIFG));
        HWREG8(baseAddress + OFS_RTCCTL0_H) = 0x00;
    }

    if(interruptFlagMask & RTC_C_PRESCALE_TIMER0_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS0CTL_L) &= ~(RT0PSIFG);
    }

    if(interruptFlagMask & RTC_C_PRESCALE_TIMER1_INTERRUPT)
    {
        HWREG8(baseAddress + OFS_RTCPS1CTL_L) &= ~(RT1PSIFG);
    }
}

uint16_t RTC_C_convertBCDToBinary(uint16_t baseAddress,
                                  uint16_t valueToConvert)
{
    HWREG16(baseAddress + OFS_BCD2BIN) = valueToConvert;
    return (HWREG16(baseAddress + OFS_BCD2BIN));
}

uint16_t RTC_C_convertBinaryToBCD(uint16_t baseAddress,
                                  uint16_t valueToConvert)
{
    HWREG16(baseAddress + OFS_BIN2BCD) = valueToConvert;
    return (HWREG16(baseAddress + OFS_BIN2BCD));
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for rtc_c_api
//! @}
//
//*****************************************************************************
