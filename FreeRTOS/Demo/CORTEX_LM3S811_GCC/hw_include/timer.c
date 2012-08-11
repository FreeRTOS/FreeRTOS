//*****************************************************************************
//
// timer.c - Driver for the timer module.
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
//
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
//
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
//
// This is part of revision 991 of the Stellaris Driver Library.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup timer_api
//! @{
//
//*****************************************************************************

#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_timer.h"
#include "../hw_types.h"
#include "debug.h"
#include "interrupt.h"
#include "timer.h"

//*****************************************************************************
//
//! Enables the timer(s).
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to enable; must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.
//!
//! This will enable operation of the timer module.  The timer must be
//! configured before it is enabled.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_enable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerEnable(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Enable the timer(s) module.
    //
    HWREG(ulBase + TIMER_O_CTL) |= ulTimer & (TIMER_CTL_TAEN | TIMER_CTL_TBEN);
}
#endif

//*****************************************************************************
//
//! Disables the timer(s).
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to disable; must be one of
//! \b TIMER_A, \b TIMER_B, or \b TIMER_BOTH.
//!
//! This will disable operation of the timer module.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_disable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerDisable(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Disable the timer module.
    //
    HWREG(ulBase + TIMER_O_CTL) &= ~(ulTimer &
                                     (TIMER_CTL_TAEN | TIMER_CTL_TBEN));
}
#endif

//*****************************************************************************
//
//! Configures the timer(s).
//!
//! \param ulBase is the base address of the timer module.
//! \param ulConfig is the configuration for the timer.
//!
//! This function configures the operating mode of the timer(s).  The timer
//! module is disabled before being configured, and is left in the disabled
//! state.  The configuration is specified in \e ulConfig as one of the
//! following values:
//!
//! - \b TIMER_CFG_32_BIT_OS - 32-bit one shot timer
//! - \b TIMER_CFG_32_BIT_PER - 32-bit periodic timer
//! - \b TIMER_CFG_32_RTC - 32-bit real time clock timer
//! - \b TIMER_CFG_16_BIT_PAIR - Two 16-bit timers
//!
//! When configured for a pair of 16-bit timers, each timer is separately
//! configured.  The first timer is configured by setting \e ulConfig to
//! the result of a logical OR operation between one of the following values
//! and \e ulConfig:
//!
//! - \b TIMER_CFG_A_ONE_SHOT - 16-bit one shot timer
//! - \b TIMER_CFG_A_PERIODIC - 16-bit periodic timer
//! - \b TIMER_CFG_A_CAP_COUNT - 16-bit edge count capture
//! - \b TIMER_CFG_A_CAP_TIME - 16-bit edge time capture
//! - \b TIMER_CFG_A_PWM - 16-bit PWM output
//!
//! Similarly, the second timer is configured by setting \e ulConfig to
//! the result of a logical OR operation between one of the corresponding
//! \b TIMER_CFG_B_* values and \e ulConfig.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_configure) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerConfigure(unsigned long ulBase, unsigned long ulConfig)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulConfig == TIMER_CFG_32_BIT_OS) ||
           (ulConfig == TIMER_CFG_32_BIT_PER) ||
           (ulConfig == TIMER_CFG_32_RTC) ||
           ((ulConfig & 0xff000000) == TIMER_CFG_16_BIT_PAIR));
    ASSERT(((ulConfig & 0xff000000) != TIMER_CFG_16_BIT_PAIR) ||
           ((((ulConfig & 0x000000ff) == TIMER_CFG_A_ONE_SHOT) ||
             ((ulConfig & 0x000000ff) == TIMER_CFG_A_PERIODIC) ||
             ((ulConfig & 0x000000ff) == TIMER_CFG_A_CAP_COUNT) ||
             ((ulConfig & 0x000000ff) == TIMER_CFG_A_CAP_TIME) ||
             ((ulConfig & 0x000000ff) == TIMER_CFG_A_PWM)) &&
            (((ulConfig & 0x0000ff00) == TIMER_CFG_B_ONE_SHOT) ||
             ((ulConfig & 0x0000ff00) == TIMER_CFG_B_PERIODIC) ||
             ((ulConfig & 0x0000ff00) == TIMER_CFG_B_CAP_COUNT) ||
             ((ulConfig & 0x0000ff00) == TIMER_CFG_B_CAP_TIME) ||
             ((ulConfig & 0x0000ff00) == TIMER_CFG_B_PWM))));

    //
    // Disable the timers.
    //
    HWREG(ulBase + TIMER_O_CTL) &= ~(TIMER_CTL_TAEN | TIMER_CTL_TBEN);

    //
    // Set the global timer configuration.
    //
    HWREG(ulBase + TIMER_O_CFG) = ulConfig >> 24;

    //
    // Set the configuration of the A and B timers.  Note that the B timer
    // configuration is ignored by the hardware in 32-bit modes.
    //
    HWREG(ulBase + TIMER_O_TAMR) = ulConfig & 255;
    HWREG(ulBase + TIMER_O_TBMR) = (ulConfig >> 8) & 255;
}
#endif

//*****************************************************************************
//
//! Controls the output level.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to adjust; must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.
//! \param bInvert specifies the output level.
//!
//! This function sets the PWM output level for the specified timer.  If the
//! parameter \e bInvert is \b true, then the timer's output will be made
//! active low; otherwise, it will be made active high.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_controllevel) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerControlLevel(unsigned long ulBase, unsigned long ulTimer,
                  tBoolean bInvert)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Set the output levels as requested.
    //
    ulTimer &= TIMER_CTL_TAPWML | TIMER_CTL_TBPWML;
    HWREG(ulBase + TIMER_O_CTL) = (bInvert ?
                                   (HWREG(ulBase + TIMER_O_CTL) | ulTimer) :
                                   (HWREG(ulBase + TIMER_O_CTL) & ~(ulTimer)));
}
#endif

//*****************************************************************************
//
//! Enables or disables the trigger output.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer to adjust; must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.
//! \param bEnable specifies the desired trigger state.
//!
//! This function controls the trigger output for the specified timer.  If the
//! parameter \e bEnable is \b true, then the timer's output trigger is
//! enabled; otherwise it is disabled.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_controltrigger) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerControlTrigger(unsigned long ulBase, unsigned long ulTimer,
                    tBoolean bEnable)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Set the trigger output as requested.
    //
    ulTimer &= TIMER_CTL_TAOTE | TIMER_CTL_TBOTE;
    HWREG(ulBase + TIMER_O_CTL) = (bEnable ?
                                   (HWREG(ulBase + TIMER_O_CTL) | ulTimer) :
                                   (HWREG(ulBase + TIMER_O_CTL) & ~(ulTimer)));
}
#endif

//*****************************************************************************
//
//! Controls the event type.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to be adjusted; must be one of
//! \b TIMER_A, \b TIMER_B, or \b TIMER_BOTH.
//! \param ulEvent specifies the type of event; must be one of
//! \b TIMER_EVENT_POS_EDGE, \b TIMER_EVENT_NEG_EDGE, or
//! \b TIMER_EVENT_BOTH_EDGES.
//!
//! This function sets the signal edge(s) that will trigger the timer when in
//! capture mode.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_controlevent) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerControlEvent(unsigned long ulBase, unsigned long ulTimer,
                  unsigned long ulEvent)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Set the event type.
    //
    ulEvent &= ulTimer & (TIMER_CTL_TAEVENT_MSK | TIMER_CTL_TBEVENT_MSK);
    HWREG(ulBase + TIMER_O_CTL) = ((HWREG(ulBase + TIMER_O_CTL) &
                                    ~(TIMER_CTL_TAEVENT_MSK |
                                      TIMER_CTL_TBEVENT_MSK)) | ulEvent);
}
#endif

//*****************************************************************************
//
//! Controls the stall handling.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to be adjusted; must be one of
//! \b TIMER_A, \b TIMER_B, or \b TIMER_BOTH.
//! \param bStall specifies the response to a stall signal.
//!
//! This function controls the stall response for the specified timer.  If the
//! parameter \e bStall is \b true, then the timer will stop counting if the
//! processor enters debug mode; otherwise the timer will keep running while in
//! debug mode.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_controlstall) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerControlStall(unsigned long ulBase, unsigned long ulTimer,
                  tBoolean  bStall)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Set the stall mode.
    //
    ulTimer &= TIMER_CTL_TASTALL | TIMER_CTL_TBSTALL;
    HWREG(ulBase + TIMER_O_CTL) = (bStall ?
                                   (HWREG(ulBase + TIMER_O_CTL) | ulTimer) :
                                   (HWREG(ulBase + TIMER_O_CTL) & ~(ulTimer)));
}
#endif

//*****************************************************************************
//
//! Enable RTC counting.
//!
//! \param ulBase is the base address of the timer module.
//!
//! This function causes the timer to start counting when in RTC mode.  If not
//! configured for RTC mode, this will do nothing.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_rtcenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerRTCEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));

    //
    // Enable RTC counting.
    //
    HWREG(ulBase + TIMER_O_CTL) |= TIMER_CTL_RTCEN;
}
#endif

//*****************************************************************************
//
//! Disable RTC counting.
//!
//! \param ulBase is the base address of the timer module.
//!
//! This function causes the timer to stop counting when in RTC mode.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_rtcdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerRTCDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));

    //
    // Disable RTC counting.
    //
    HWREG(ulBase + TIMER_O_CTL) &= ~(TIMER_CTL_RTCEN);
}
#endif

//*****************************************************************************
//
//! Set the timer prescale value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to adjust; must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.
//! \param ulValue is the timer prescale value; must be between 0 and 255,
//! inclusive.
//!
//! This function sets the value of the input clock prescaler.  The prescaler
//! is only operational when in 16-bit mode and is used to extend the range of
//! the 16-bit timer modes.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_prescaleset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerPrescaleSet(unsigned long ulBase, unsigned long ulTimer,
                 unsigned long ulValue)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));
    ASSERT(ulValue < 256);

    //
    // Set the timer A prescaler if requested.
    //
    if(ulTimer & TIMER_A)
    {
        HWREG(ulBase + TIMER_O_TAPR) = ulValue;
    }

    //
    // Set the timer B prescaler if requested.
    //
    if(ulTimer & TIMER_B)
    {
        HWREG(ulBase + TIMER_O_TBPR) = ulValue;
    }
}
#endif

//*****************************************************************************
//
//! Get the timer prescale value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer; must be one of \b TIMER_A or
//! \b TIMER_B.
//!
//! This function gets the value of the input clock prescaler.  The prescaler
//! is only operational when in 16-bit mode and is used to extend the range of
//! the 16-bit timer modes.
//!
//! \return The value of the timer prescaler.
//
//*****************************************************************************
#if defined(GROUP_prescaleget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
TimerPrescaleGet(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Return the appropriate prescale value.
    //
    return((ulTimer == TIMER_A) ? HWREG(ulBase + TIMER_O_TAPR) :
           HWREG(ulBase + TIMER_O_TBPR));
}
#endif

//*****************************************************************************
//
//! Set the timer prescale match value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to adjust; must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.
//! \param ulValue is the timer prescale match value; must be between 0 and
//! 255, inclusive.
//!
//! This function sets the value of the input clock prescaler match value.
//! When in a 16-bit mode that uses the counter match (edge count or PWM), the
//! prescale match effectively extends the range of the counter to 24-bits.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_prescalematchset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerPrescaleMatchSet(unsigned long ulBase, unsigned long ulTimer,
                      unsigned long ulValue)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));
    ASSERT(ulValue < 256);

    //
    // Set the timer A prescale match if requested.
    //
    if(ulTimer & TIMER_A)
    {
        HWREG(ulBase + TIMER_O_TAPMR) = ulValue;
    }

    //
    // Set the timer B prescale match if requested.
    //
    if(ulTimer & TIMER_B)
    {
        HWREG(ulBase + TIMER_O_TBPMR) = ulValue;
    }
}
#endif

//*****************************************************************************
//
//! Get the timer prescale match value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer; must be one of \b TIMER_A or
//! \b TIMER_B.
//!
//! This function gets the value of the input clock prescaler match value.
//! When in a 16-bit mode that uses the counter match (edge count or PWM), the
//! prescale match effectively extends the range of the counter to 24-bits.
//!
//! \return The value of the timer prescale match.
//
//*****************************************************************************
#if defined(GROUP_prescalematchget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
TimerPrescaleMatchGet(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Return the appropriate prescale match value.
    //
    return((ulTimer == TIMER_A) ? HWREG(ulBase + TIMER_O_TAPMR) :
           HWREG(ulBase + TIMER_O_TBPMR));
}
#endif

//*****************************************************************************
//
//! Sets the timer load value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to adjust; must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.  Only \b TIMER_A should be used when the
//! timer is configured for 32-bit operation.
//! \param ulValue is the load value.
//!
//! This function sets the timer load value; if the timer is running then the
//! value will be immediately loaded into the timer.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_loadset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerLoadSet(unsigned long ulBase, unsigned long ulTimer,
             unsigned long ulValue)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Set the timer A load value if requested.
    //
    if(ulTimer & TIMER_A)
    {
        HWREG(ulBase + TIMER_O_TAILR) = ulValue;
    }

    //
    // Set the timer B load value if requested.
    //
    if(ulTimer & TIMER_B)
    {
        HWREG(ulBase + TIMER_O_TBILR) = ulValue;
    }
}
#endif

//*****************************************************************************
//
//! Gets the timer load value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer; must be one of \b TIMER_A or
//! \b TIMER_B.  Only \b TIMER_A should be used when the timer is configured
//! for 32-bit operation.
//!
//! This function gets the currently programmed interval load value for the
//! specified timer.
//!
//! \return Returns the load value for the timer.
//
//*****************************************************************************
#if defined(GROUP_loadget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
TimerLoadGet(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B));

    //
    // Return the appropriate load value.
    //
    return((ulTimer == TIMER_A) ? HWREG(ulBase + TIMER_O_TAILR) :
           HWREG(ulBase + TIMER_O_TBILR));
}
#endif

//*****************************************************************************
//
//! Gets the current timer value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer; must be one of \b TIMER_A or
//! \b TIMER_B.  Only \b TIMER_A should be used when the timer is configured
//! for 32-bit operation.
//!
//! This function reads the current value of the specified timer.
//!
//! \return Returns the current value of the timer.
//
//*****************************************************************************
#if defined(GROUP_valueget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
TimerValueGet(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B));

    //
    // Return the appropriate timer value.
    //
    return((ulTimer == TIMER_A) ? HWREG(ulBase + TIMER_O_TAR) :
           HWREG(ulBase + TIMER_O_TBR));
}
#endif

//*****************************************************************************
//
//! Sets the timer match value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s) to adjust; must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.  Only \b TIMER_A should be used when the
//! timer is configured for 32-bit operation.
//! \param ulValue is the match value.
//!
//! This function sets the match value for a timer.  This is used in capture
//! count mode to determine when to interrupt the processor and in PWM mode to
//! determine the duty cycle of the output signal.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_matchset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerMatchSet(unsigned long ulBase, unsigned long ulTimer,
              unsigned long ulValue)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Set the timer A match value if requested.
    //
    if(ulTimer & TIMER_A)
    {
        HWREG(ulBase + TIMER_O_TAMATCHR) = ulValue;
    }

    //
    // Set the timer B match value if requested.
    //
    if(ulTimer & TIMER_B)
    {
        HWREG(ulBase + TIMER_O_TBMATCHR) = ulValue;
    }
}
#endif

//*****************************************************************************
//
//! Gets the timer match value.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer; must be one of \b TIMER_A or
//! \b TIMER_B.  Only \b TIMER_A should be used when the timer is configured
//! for 32-bit operation.
//!
//! This function gets the match value for the specified timer.
//!
//! \return Returns the match value for the timer.
//
//*****************************************************************************
#if defined(GROUP_matchget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
TimerMatchGet(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B));

    //
    // Return the appropriate match value.
    //
    return((ulTimer == TIMER_A) ? HWREG(ulBase + TIMER_O_TAMATCHR) :
           HWREG(ulBase + TIMER_O_TBMATCHR));
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for the timer interrupt.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s); must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.
//! \param pfnHandler is a pointer to the function to be called when the timer
//! interrupt occurs.
//!
//! This sets the handler to be called when a timer interrupt occurs.  This
//! will enable the global interrupt in the interrupt controller; specific
//! timer interrupts must be enabled via TimerIntEnable().  It is the interrupt
//! handler's responsibility to clear the interrupt source via TimerIntClear().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerIntRegister(unsigned long ulBase, unsigned long ulTimer,
                 void (*pfnHandler)(void))
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Get the interrupt number for this timer module.
    //
    ulBase = ((ulBase == TIMER0_BASE) ? INT_TIMER0A :
              ((ulBase == TIMER1_BASE) ? INT_TIMER1A : INT_TIMER2A));

    //
    // Register an interrupt handler for timer A if requested.
    //
    if(ulTimer & TIMER_A)
    {
        //
        // Register the interrupt handler.
        //
        IntRegister(ulBase, pfnHandler);

        //
        // Enable the interrupt.
        //
        IntEnable(ulBase);
    }

    //
    // Register an interrupt handler for timer B if requested.
    //
    if(ulTimer & TIMER_B)
    {
        //
        // Register the interrupt handler.
        //
        IntRegister(ulBase + 1, pfnHandler);

        //
        // Enable the interrupt.
        //
        IntEnable(ulBase + 1);
    }
}
#endif

//*****************************************************************************
//
//! Unregisters an interrupt handler for the timer interrupt.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulTimer specifies the timer(s); must be one of \b TIMER_A,
//! \b TIMER_B, or \b TIMER_BOTH.
//!
//! This function will clear the handler to be called when a timer interrupt
//! occurs.  This will also mask off the interrupt in the interrupt controller
//! so that the interrupt handler no longer is called.
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intunregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerIntUnregister(unsigned long ulBase, unsigned long ulTimer)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));
    ASSERT((ulTimer == TIMER_A) || (ulTimer == TIMER_B) ||
           (ulTimer == TIMER_BOTH));

    //
    // Get the interrupt number for this timer module.
    //
    ulBase = ((ulBase == TIMER0_BASE) ? INT_TIMER0A :
              ((ulBase == TIMER1_BASE) ? INT_TIMER1A : INT_TIMER2A));

    //
    // Unregister the interrupt handler for timer A if requested.
    //
    if(ulTimer & TIMER_A)
    {
        //
        // Disable the interrupt.
        //
        IntDisable(ulBase);

        //
        // Unregister the interrupt handler.
        //
        IntUnregister(ulBase);
    }

    //
    // Unregister the interrupt handler for timer B if requested.
    //
    if(ulTimer & TIMER_B)
    {
        //
        // Disable the interrupt.
        //
        IntDisable(ulBase + 1);

        //
        // Unregister the interrupt handler.
        //
        IntUnregister(ulBase + 1);
    }
}
#endif

//*****************************************************************************
//
//! Enables individual timer interrupt sources.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulIntFlags is the bit mask of the interrupt sources to be enabled.
//!
//! Enables the indicated timer interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! The parameter \e ulIntFlags must be the logical OR of any combination of
//! the following:
//!
//! - TIMER_CAPB_EVENT  - Capture B event interrupt
//! - TIMER_CAPB_MATCH  - Capture B match interrupt
//! - TIMER_TIMB_TIMEOUT  - Timer B timeout interrupt
//! - TIMER_RTC_MATCH  - RTC interrupt mask
//! - TIMER_CAPA_EVENT  - Capture A event interrupt
//! - TIMER_CAPA_MATCH  - Capture A match interrupt
//! - TIMER_TIMA_TIMEOUT  - Timer A timeout interrupt
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerIntEnable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));

    //
    // Enable the specified interrupts.
    //
    HWREG(ulBase + TIMER_O_IMR) |= ulIntFlags;
}
#endif

//*****************************************************************************
//
//! Disables individual timer interrupt sources.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulIntFlags is the bit mask of the interrupt sources to be disabled.
//!
//! Disables the indicated timer interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! The parameter \e ulIntFlags has the same definition as the \e ulIntFlags
//! parameter to TimerIntEnable().
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerIntDisable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));

    //
    // Disable the specified interrupts.
    //
    HWREG(ulBase + TIMER_O_IMR) &= ~(ulIntFlags);
}
#endif

//*****************************************************************************
//
//! Gets the current interrupt status.
//!
//! \param ulBase is the base address of the timer module.
//! \param bMasked is false if the raw interrupt status is required and true if
//! the masked interrupt status is required.
//!
//! This returns the interrupt status for the timer module.  Either the raw
//! interrupt status or the status of interrupts that are allowed to reflect to
//! the processor can be returned.
//!
//! \return The current interrupt status, enumerated as a bit field of
//! values described in TimerIntEnable().
//
//*****************************************************************************
#if defined(GROUP_intstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
TimerIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    return(bMasked ? HWREG(ulBase + TIMER_O_MIS) :
           HWREG(ulBase + TIMER_O_RIS));
}
#endif

//*****************************************************************************
//
//! Clears timer interrupt sources.
//!
//! \param ulBase is the base address of the timer module.
//! \param ulIntFlags is a bit mask of the interrupt sources to be cleared.
//!
//! The specified timer interrupt sources are cleared, so that they no longer
//! assert.  This must be done in the interrupt handler to keep it from being
//! called again immediately upon exit.
//!
//! The parameter \e ulIntFlags has the same definition as the \e ulIntFlags
//! parameter to TimerIntEnable().
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerIntClear(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));

    //
    // Clear the requested interrupt sources.
    //
    HWREG(ulBase + TIMER_O_ICR) = ulIntFlags;
}
#endif

//*****************************************************************************
//
//! Puts the timer into its reset state.
//!
//! \param ulBase is the base address of the timer module.
//!
//! The specified timer is disabled, and all its interrupts are disabled,
//! cleared, and unregistered. Then the timer registers are set to their reset
//! value.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_quiesce) || defined(BUILD_ALL) || defined(DOXYGEN)
void
TimerQuiesce(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == TIMER0_BASE) || (ulBase == TIMER1_BASE) ||
           (ulBase == TIMER2_BASE));

    //
    // Disable the timer.
    //
    HWREG(ulBase + TIMER_O_CTL) = TIMER_RV_CTL;

    //
    // Disable all the timer interrupts.
    //
    HWREG(ulBase + TIMER_O_IMR) = TIMER_RV_IMR;

    //
    // Clear all the timer interrupts.
    //
    HWREG(ulBase + TIMER_O_ICR) = 0xFFFFFFFF;

    //
    // Unregister the interrupt handler.  This also disables interrupts to the
    // core.
    //
    TimerIntUnregister(ulBase, TIMER_BOTH);

    //
    // Set all the registers to their reset value.
    //
    HWREG(ulBase + TIMER_O_CFG) = TIMER_RV_CFG;
    HWREG(ulBase + TIMER_O_TAMR) = TIMER_RV_TAMR;
    HWREG(ulBase + TIMER_O_TBMR) = TIMER_RV_TBMR;
    HWREG(ulBase + TIMER_O_RIS) = TIMER_RV_RIS;
    HWREG(ulBase + TIMER_O_MIS) = TIMER_RV_MIS;
    HWREG(ulBase + TIMER_O_TAILR) = TIMER_RV_TAILR;
    HWREG(ulBase + TIMER_O_TBILR) = TIMER_RV_TBILR;
    HWREG(ulBase + TIMER_O_TAMATCHR) = TIMER_RV_TAMATCHR;
    HWREG(ulBase + TIMER_O_TBMATCHR) = TIMER_RV_TBMATCHR;
    HWREG(ulBase + TIMER_O_TAPR) = TIMER_RV_TAPR;
    HWREG(ulBase + TIMER_O_TBPR) = TIMER_RV_TBPR;
    HWREG(ulBase + TIMER_O_TAPMR) = TIMER_RV_TAPMR;
    HWREG(ulBase + TIMER_O_TBPMR) = TIMER_RV_TBPMR;
    HWREG(ulBase + TIMER_O_TAR) = TIMER_RV_TAR;
    HWREG(ulBase + TIMER_O_TBR) = TIMER_RV_TBR;
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
