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
// rtc_b.h - Driver for the RTC_B Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_RTC_B_H__
#define __MSP430WARE_RTC_B_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_RTC_B__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

#include "inc/hw_regaccess.h"
//*****************************************************************************
//
//! \brief Used in the RTC_B_initCalendar() function as the CalendarTime
//! parameter.
//
//*****************************************************************************
typedef struct Calendar
{
    //! Seconds of minute between 0-59
    uint8_t Seconds;
    //! Minutes of hour between 0-59
    uint8_t Minutes;
    //! Hour of day between 0-23
    uint8_t Hours;
    //! Day of week between 0-6
    uint8_t DayOfWeek;
    //! Day of month between 1-31
    uint8_t DayOfMonth;
    //! Month between 0-11
    uint8_t Month;
    //! Year between 0-4095
    uint16_t Year;
} Calendar;

//*****************************************************************************
//
//! \brief Used in the RTC_B_configureCalendarAlarm() function as the param
//! parameter.
//
//*****************************************************************************
typedef struct RTC_B_configureCalendarAlarmParam
{
    //! Is the alarm condition for the minutes.
    //! \n Valid values are:
    //! - \b RTC_B_ALARMCONDITION_OFF [Default]
    uint8_t minutesAlarm;
    //! Is the alarm condition for the hours.
    //! \n Valid values are:
    //! - \b RTC_B_ALARMCONDITION_OFF [Default]
    uint8_t hoursAlarm;
    //! Is the alarm condition for the day of week.
    //! \n Valid values are:
    //! - \b RTC_B_ALARMCONDITION_OFF [Default]
    uint8_t dayOfWeekAlarm;
    //! Is the alarm condition for the day of the month.
    //! \n Valid values are:
    //! - \b RTC_B_ALARMCONDITION_OFF [Default]
    uint8_t dayOfMonthAlarm;
} RTC_B_configureCalendarAlarmParam;

//*****************************************************************************
//
// The following are values that can be passed to the frequencySelect parameter
// for functions: RTC_B_setCalibrationFrequency().
//
//*****************************************************************************
#define RTC_B_CALIBRATIONFREQ_OFF                                   (RTCCALF_0)
#define RTC_B_CALIBRATIONFREQ_512HZ                                 (RTCCALF_1)
#define RTC_B_CALIBRATIONFREQ_256HZ                                 (RTCCALF_2)
#define RTC_B_CALIBRATIONFREQ_1HZ                                   (RTCCALF_3)

//*****************************************************************************
//
// The following are values that can be passed to the offsetDirection parameter
// for functions: RTC_B_setCalibrationData().
//
//*****************************************************************************
#define RTC_B_CALIBRATION_DOWN2PPM                                 (!(RTCCALS))
#define RTC_B_CALIBRATION_UP4PPM                                      (RTCCALS)

//*****************************************************************************
//
// The following are values that can be passed to the formatSelect parameter
// for functions: RTC_B_initCalendar().
//
//*****************************************************************************
#define RTC_B_FORMAT_BINARY                                         (!(RTCBCD))
#define RTC_B_FORMAT_BCD                                               (RTCBCD)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: RTC_B_configureCalendarAlarm(), RTC_B_configureCalendarAlarm(),
// RTC_B_configureCalendarAlarm(), and RTC_B_configureCalendarAlarm().
//
//*****************************************************************************
#define RTC_B_ALARMCONDITION_OFF                                         (0x80)

//*****************************************************************************
//
// The following are values that can be passed to the eventSelect parameter for
// functions: RTC_B_setCalendarEvent().
//
//*****************************************************************************
#define RTC_B_CALENDAREVENT_MINUTECHANGE                             (RTCTEV_0)
#define RTC_B_CALENDAREVENT_HOURCHANGE                               (RTCTEV_1)
#define RTC_B_CALENDAREVENT_NOON                                     (RTCTEV_2)
#define RTC_B_CALENDAREVENT_MIDNIGHT                                 (RTCTEV_3)

//*****************************************************************************
//
// The following are values that can be passed to the prescaleEventDivider
// parameter for functions: RTC_B_definePrescaleEvent().
//
//*****************************************************************************
#define RTC_B_PSEVENTDIVIDER_2                                        (RT0IP_0)
#define RTC_B_PSEVENTDIVIDER_4                                        (RT0IP_1)
#define RTC_B_PSEVENTDIVIDER_8                                        (RT0IP_2)
#define RTC_B_PSEVENTDIVIDER_16                                       (RT0IP_3)
#define RTC_B_PSEVENTDIVIDER_32                                       (RT0IP_4)
#define RTC_B_PSEVENTDIVIDER_64                                       (RT0IP_5)
#define RTC_B_PSEVENTDIVIDER_128                                      (RT0IP_6)
#define RTC_B_PSEVENTDIVIDER_256                                      (RT0IP_7)

//*****************************************************************************
//
// The following are values that can be passed to the prescaleSelect parameter
// for functions: RTC_B_definePrescaleEvent(), RTC_B_getPrescaleValue(), and
// RTC_B_setPrescaleValue().
//
//*****************************************************************************
#define RTC_B_PRESCALE_0                                                  (0x0)
#define RTC_B_PRESCALE_1                                                  (0x2)

//*****************************************************************************
//
// The following are values that can be passed to the interruptMask parameter
// for functions: RTC_B_enableInterrupt(), and RTC_B_disableInterrupt(); the
// interruptFlagMask parameter for functions: RTC_B_getInterruptStatus(), and
// RTC_B_clearInterrupt() as well as returned by the RTC_B_getInterruptStatus()
// function.
//
//*****************************************************************************
#define RTC_B_TIME_EVENT_INTERRUPT                                     RTCTEVIE
#define RTC_B_CLOCK_ALARM_INTERRUPT                                      RTCAIE
#define RTC_B_CLOCK_READ_READY_INTERRUPT                               RTCRDYIE
#define RTC_B_PRESCALE_TIMER0_INTERRUPT                                    0x02
#define RTC_B_PRESCALE_TIMER1_INTERRUPT                                    0x01
#define RTC_B_OSCILLATOR_FAULT_INTERRUPT                                RTCOFIE

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Starts the RTC.
//!
//! This function clears the RTC main hold bit to allow the RTC to function.
//!
//! \param baseAddress is the base address of the RTC_B module.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_startClock(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Holds the RTC.
//!
//! This function sets the RTC main hold bit to disable RTC functionality.
//!
//! \param baseAddress is the base address of the RTC_B module.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_holdClock(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Allows and Sets the frequency output to RTCCLK pin for calibration
//! measurement.
//!
//! This function sets a frequency to measure at the RTCCLK output pin. After
//! testing the set frequency, the calibration could be set accordingly.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param frequencySelect is the frequency output to RTCCLK.
//!        Valid values are:
//!        - \b RTC_B_CALIBRATIONFREQ_OFF [Default] - turn off calibration
//!           output
//!        - \b RTC_B_CALIBRATIONFREQ_512HZ - output signal at 512Hz for
//!           calibration
//!        - \b RTC_B_CALIBRATIONFREQ_256HZ - output signal at 256Hz for
//!           calibration
//!        - \b RTC_B_CALIBRATIONFREQ_1HZ - output signal at 1Hz for
//!           calibration
//!        \n Modified bits are \b RTCCALF of \b RTCCTL3 register.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_setCalibrationFrequency(uint16_t baseAddress,
                                          uint16_t frequencySelect);

//*****************************************************************************
//
//! \brief Sets the specified calibration for the RTC.
//!
//! This function sets the calibration offset to make the RTC as accurate as
//! possible. The offsetDirection can be either +4-ppm or -2-ppm, and the
//! offsetValue should be from 1-63 and is multiplied by the direction setting
//! (i.e. +4-ppm * 8 (offsetValue) = +32-ppm). Please note, when measuring the
//! frequency after setting the calibration, you will only see a change on the
//! 1Hz frequency.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param offsetDirection is the direction that the calibration offset will
//!        go.
//!        Valid values are:
//!        - \b RTC_B_CALIBRATION_DOWN2PPM - calibrate at steps of -2
//!        - \b RTC_B_CALIBRATION_UP4PPM - calibrate at steps of +4
//!        \n Modified bits are \b RTCCALS of \b RTCCTL2 register.
//! \param offsetValue is the value that the offset will be a factor of; a
//!        valid value is any integer from 1-63.
//!        \n Modified bits are \b RTCCAL of \b RTCCTL2 register.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_setCalibrationData(uint16_t baseAddress,
                                     uint8_t offsetDirection,
                                     uint8_t offsetValue);

//*****************************************************************************
//
//! \brief Initializes the settings to operate the RTC in calendar mode
//!
//! This function initializes the Calendar mode of the RTC module. To prevent
//! potential erroneous alarm conditions from occurring, the alarm should be
//! disabled by clearing the RTCAIE, RTCAIFG and AE bits with APIs:
//! RTC_B_disableInterrupt(), RTC_B_clearInterrupt() and
//! RTC_B_configureCalendarAlarm() before calendar initialization.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param CalendarTime is the pointer to the structure containing the values
//!        for the Calendar to be initialized to. Valid values should be of
//!        type pointer to Calendar and should contain the following members
//!        and corresponding values: \b Seconds between 0-59 \b Minutes between
//!        0-59 \b Hours between 0-23 \b DayOfWeek between 0-6 \b DayOfMonth
//!        between 1-31 \b Year between 0-4095 NOTE: Values beyond the ones
//!        specified may result in erratic behavior.
//! \param formatSelect is the format for the Calendar registers to use.
//!        Valid values are:
//!        - \b RTC_B_FORMAT_BINARY [Default]
//!        - \b RTC_B_FORMAT_BCD
//!        \n Modified bits are \b RTCBCD of \b RTCCTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_initCalendar(uint16_t baseAddress,
                               Calendar *CalendarTime,
                               uint16_t formatSelect);

//*****************************************************************************
//
//! \brief Returns the Calendar Time stored in the Calendar registers of the
//! RTC.
//!
//! This function returns the current Calendar time in the form of a Calendar
//! structure. The RTCRDY polling is used in this function to prevent reading
//! invalid time.
//!
//! \param baseAddress is the base address of the RTC_B module.
//!
//! \return A Calendar structure containing the current time.
//
//*****************************************************************************
extern Calendar RTC_B_getCalendarTime(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Sets and Enables the desired Calendar Alarm settings.
//!
//! This function sets a Calendar interrupt condition to assert the RTCAIFG
//! interrupt flag. The condition is a logical and of all of the parameters.
//! For example if the minutes and hours alarm is set, then the interrupt will
//! only assert when the minutes AND the hours change to the specified setting.
//! Use the RTC_B_ALARM_OFF for any alarm settings that should not be apart of
//! the alarm condition.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param param is the pointer to struct for calendar alarm configuration.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_configureCalendarAlarm(uint16_t baseAddress,
                                         RTC_B_configureCalendarAlarmParam *param);

//*****************************************************************************
//
//! \brief Sets a single specified Calendar interrupt condition
//!
//! This function sets a specified event to assert the RTCTEVIFG interrupt.
//! This interrupt is independent from the Calendar alarm interrupt.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param eventSelect is the condition selected.
//!        Valid values are:
//!        - \b RTC_B_CALENDAREVENT_MINUTECHANGE - assert interrupt on every
//!           minute
//!        - \b RTC_B_CALENDAREVENT_HOURCHANGE - assert interrupt on every hour
//!        - \b RTC_B_CALENDAREVENT_NOON - assert interrupt when hour is 12
//!        - \b RTC_B_CALENDAREVENT_MIDNIGHT - assert interrupt when hour is 0
//!        \n Modified bits are \b RTCTEV of \b RTCCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_setCalendarEvent(uint16_t baseAddress,
                                   uint16_t eventSelect);

//*****************************************************************************
//
//! \brief Sets up an interrupt condition for the selected Prescaler.
//!
//! This function sets the condition for an interrupt to assert based on the
//! individual prescalers.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param prescaleSelect is the prescaler to define an interrupt for.
//!        Valid values are:
//!        - \b RTC_B_PRESCALE_0
//!        - \b RTC_B_PRESCALE_1
//! \param prescaleEventDivider is a divider to specify when an interrupt can
//!        occur based on the clock source of the selected prescaler. (Does not
//!        affect timer of the selected prescaler).
//!        Valid values are:
//!        - \b RTC_B_PSEVENTDIVIDER_2 [Default]
//!        - \b RTC_B_PSEVENTDIVIDER_4
//!        - \b RTC_B_PSEVENTDIVIDER_8
//!        - \b RTC_B_PSEVENTDIVIDER_16
//!        - \b RTC_B_PSEVENTDIVIDER_32
//!        - \b RTC_B_PSEVENTDIVIDER_64
//!        - \b RTC_B_PSEVENTDIVIDER_128
//!        - \b RTC_B_PSEVENTDIVIDER_256
//!        \n Modified bits are \b RTxIP of \b RTCPSxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_definePrescaleEvent(uint16_t baseAddress,
                                      uint8_t prescaleSelect,
                                      uint8_t prescaleEventDivider);

//*****************************************************************************
//
//! \brief Returns the selected prescaler value.
//!
//! This function returns the value of the selected prescale counter register.
//! Note that the counter value should be held by calling RTC_B_holdClock()
//! before calling this API.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param prescaleSelect is the prescaler to obtain the value of.
//!        Valid values are:
//!        - \b RTC_B_PRESCALE_0
//!        - \b RTC_B_PRESCALE_1
//!
//! \return The value of the specified prescaler count register
//
//*****************************************************************************
extern uint8_t RTC_B_getPrescaleValue(uint16_t baseAddress,
                                      uint8_t prescaleSelect);

//*****************************************************************************
//
//! \brief Sets the selected prescaler value.
//!
//! This function sets the prescale counter value. Before setting the prescale
//! counter, it should be held by calling RTC_B_holdClock().
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param prescaleSelect is the prescaler to set the value for.
//!        Valid values are:
//!        - \b RTC_B_PRESCALE_0
//!        - \b RTC_B_PRESCALE_1
//! \param prescaleCounterValue is the specified value to set the prescaler to.
//!        Valid values are any integer between 0-255
//!        \n Modified bits are \b RTxPS of \b RTxPS register.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_setPrescaleValue(uint16_t baseAddress,
                                   uint8_t prescaleSelect,
                                   uint8_t prescaleCounterValue);

//*****************************************************************************
//
//! \brief Enables selected RTC interrupt sources.
//!
//! This function enables the selected RTC interrupt source.  Only the sources
//! that are enabled can be reflected to the processor interrupt; disabled
//! sources have no effect on the processor. Does not clear interrupt flags.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param interruptMask is a bit mask of the interrupts to enable.
//!        Mask value is the logical OR of any of the following:
//!        - \b RTC_B_TIME_EVENT_INTERRUPT - asserts when counter overflows in
//!           counter mode or when Calendar event condition defined by
//!           defineCalendarEvent() is met.
//!        - \b RTC_B_CLOCK_ALARM_INTERRUPT - asserts when alarm condition in
//!           Calendar mode is met.
//!        - \b RTC_B_CLOCK_READ_READY_INTERRUPT - asserts when Calendar
//!           registers are settled.
//!        - \b RTC_B_PRESCALE_TIMER0_INTERRUPT - asserts when Prescaler 0
//!           event condition is met.
//!        - \b RTC_B_PRESCALE_TIMER1_INTERRUPT - asserts when Prescaler 1
//!           event condition is met.
//!        - \b RTC_B_OSCILLATOR_FAULT_INTERRUPT - asserts if there is a
//!           problem with the 32kHz oscillator, while the RTC is running.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_enableInterrupt(uint16_t baseAddress,
                                  uint8_t interruptMask);

//*****************************************************************************
//
//! \brief Disables selected RTC interrupt sources.
//!
//! This function disables the selected RTC interrupt source. Only the sources
//! that are enabled can be reflected to the processor interrupt; disabled
//! sources have no effect on the processor.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param interruptMask is a bit mask of the interrupts to disable.
//!        Mask value is the logical OR of any of the following:
//!        - \b RTC_B_TIME_EVENT_INTERRUPT - asserts when counter overflows in
//!           counter mode or when Calendar event condition defined by
//!           defineCalendarEvent() is met.
//!        - \b RTC_B_CLOCK_ALARM_INTERRUPT - asserts when alarm condition in
//!           Calendar mode is met.
//!        - \b RTC_B_CLOCK_READ_READY_INTERRUPT - asserts when Calendar
//!           registers are settled.
//!        - \b RTC_B_PRESCALE_TIMER0_INTERRUPT - asserts when Prescaler 0
//!           event condition is met.
//!        - \b RTC_B_PRESCALE_TIMER1_INTERRUPT - asserts when Prescaler 1
//!           event condition is met.
//!        - \b RTC_B_OSCILLATOR_FAULT_INTERRUPT - asserts if there is a
//!           problem with the 32kHz oscillator, while the RTC is running.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_disableInterrupt(uint16_t baseAddress,
                                   uint8_t interruptMask);

//*****************************************************************************
//
//! \brief Returns the status of the selected interrupts flags.
//!
//! This function returns the status of the interrupt flag for the selected
//! channel.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param interruptFlagMask is a bit mask of the interrupt flags to return the
//!        status of.
//!        Mask value is the logical OR of any of the following:
//!        - \b RTC_B_TIME_EVENT_INTERRUPT - asserts when counter overflows in
//!           counter mode or when Calendar event condition defined by
//!           defineCalendarEvent() is met.
//!        - \b RTC_B_CLOCK_ALARM_INTERRUPT - asserts when alarm condition in
//!           Calendar mode is met.
//!        - \b RTC_B_CLOCK_READ_READY_INTERRUPT - asserts when Calendar
//!           registers are settled.
//!        - \b RTC_B_PRESCALE_TIMER0_INTERRUPT - asserts when Prescaler 0
//!           event condition is met.
//!        - \b RTC_B_PRESCALE_TIMER1_INTERRUPT - asserts when Prescaler 1
//!           event condition is met.
//!        - \b RTC_B_OSCILLATOR_FAULT_INTERRUPT - asserts if there is a
//!           problem with the 32kHz oscillator, while the RTC is running.
//!
//! \return Logical OR of any of the following:
//!         - \b RTC_B_TIME_EVENT_INTERRUPT asserts when counter overflows in
//!         counter mode or when Calendar event condition defined by
//!         defineCalendarEvent() is met.
//!         - \b RTC_B_CLOCK_ALARM_INTERRUPT asserts when alarm condition in
//!         Calendar mode is met.
//!         - \b RTC_B_CLOCK_READ_READY_INTERRUPT asserts when Calendar
//!         registers are settled.
//!         - \b RTC_B_PRESCALE_TIMER0_INTERRUPT asserts when Prescaler 0 event
//!         condition is met.
//!         - \b RTC_B_PRESCALE_TIMER1_INTERRUPT asserts when Prescaler 1 event
//!         condition is met.
//!         - \b RTC_B_OSCILLATOR_FAULT_INTERRUPT asserts if there is a problem
//!         with the 32kHz oscillator, while the RTC is running.
//!         \n indicating the status of the masked interrupts
//
//*****************************************************************************
extern uint8_t RTC_B_getInterruptStatus(uint16_t baseAddress,
                                        uint8_t interruptFlagMask);

//*****************************************************************************
//
//! \brief Clears selected RTC interrupt flags.
//!
//! This function clears the RTC interrupt flag is cleared, so that it no
//! longer asserts.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param interruptFlagMask is a bit mask of the interrupt flags to be
//!        cleared.
//!        Mask value is the logical OR of any of the following:
//!        - \b RTC_B_TIME_EVENT_INTERRUPT - asserts when counter overflows in
//!           counter mode or when Calendar event condition defined by
//!           defineCalendarEvent() is met.
//!        - \b RTC_B_CLOCK_ALARM_INTERRUPT - asserts when alarm condition in
//!           Calendar mode is met.
//!        - \b RTC_B_CLOCK_READ_READY_INTERRUPT - asserts when Calendar
//!           registers are settled.
//!        - \b RTC_B_PRESCALE_TIMER0_INTERRUPT - asserts when Prescaler 0
//!           event condition is met.
//!        - \b RTC_B_PRESCALE_TIMER1_INTERRUPT - asserts when Prescaler 1
//!           event condition is met.
//!        - \b RTC_B_OSCILLATOR_FAULT_INTERRUPT - asserts if there is a
//!           problem with the 32kHz oscillator, while the RTC is running.
//!
//! \return None
//
//*****************************************************************************
extern void RTC_B_clearInterrupt(uint16_t baseAddress,
                                 uint8_t interruptFlagMask);

//*****************************************************************************
//
//! \brief Convert the given BCD value to binary format
//!
//! This function converts BCD values to binary format. This API uses the
//! hardware registers to perform the conversion rather than a software method.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param valueToConvert is the raw value in BCD format to convert to Binary.
//!        \n Modified bits are \b BCD2BIN of \b BCD2BIN register.
//!
//! \return The binary version of the input parameter
//
//*****************************************************************************
extern uint16_t RTC_B_convertBCDToBinary(uint16_t baseAddress,
                                         uint16_t valueToConvert);

//*****************************************************************************
//
//! \brief Convert the given binary value to BCD format
//!
//! This function converts binary values to BCD format. This API uses the
//! hardware registers to perform the conversion rather than a software method.
//!
//! \param baseAddress is the base address of the RTC_B module.
//! \param valueToConvert is the raw value in Binary format to convert to BCD.
//!        \n Modified bits are \b BIN2BCD of \b BIN2BCD register.
//!
//! \return The BCD version of the valueToConvert parameter
//
//*****************************************************************************
extern uint16_t RTC_B_convertBinaryToBCD(uint16_t baseAddress,
                                         uint16_t valueToConvert);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_RTC_B_H__
