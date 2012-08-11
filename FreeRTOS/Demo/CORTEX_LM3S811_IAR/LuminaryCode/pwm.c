//*****************************************************************************
//
// pwm.c - API for the PWM modules
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
//! \addtogroup pwm_api
//! @{
//
//*****************************************************************************

#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_pwm.h"
#include "../hw_types.h"
#include "debug.h"
#include "interrupt.h"
#include "pwm.h"

//*****************************************************************************
//
// Misc macros for manipulating the encoded generator and output defines used
// by the API.
//
//*****************************************************************************
#define PWM_GEN_BADDR(_mod_, _gen_)                                           \
                                ((_mod_) + (_gen_))
#define PWM_OUT_BADDR(_mod_, _out_)                                           \
                                ((_mod_) + ((_out_) & 0xFFFFFFC0))
#define PWM_IS_OUTPUT_ODD(_out_)                                              \
                                ((_out_) & 0x00000001)

//*****************************************************************************
//
//! Configures a PWM generator.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to configure.  Must be one of
//! \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//! \param ulConfig is the configuration for the PWM generator.
//!
//! This function is used to set the mode of operation for a PWM generator.
//! The counting mode, synchronization mode, and debug behavior are all
//! configured.  After configuration, the generator is left in the disabled
//! state.
//!
//! A PWM generator can count in two different modes:  count down mode or count
//! up/down mode.  In count down mode, it will count from a value down to zero,
//! and then reset to the preset value.  This will produce left-aligned PWM
//! signals (i.e. the rising edge of the two PWM signals produced by the
//! generator will occur at the same time).  In count up/down mode, it will
//! count up from zero to the preset value, count back down to zero, and then
//! repeat the process.  This will produce center-aligned PWM signals (i.e. the
//! middle of the high/low period of the PWM signals produced by the generator
//! will occur at the same time).
//!
//! When the PWM generator parameters (period and pulse width) are modified,
//! their affect on the output PWM signals can be delayed.  In synchronous
//! mode, the parameter updates are not applied until a synchronization event
//! occurs.  This allows multiple parameters to be modified and take affect
//! simultaneously, instead of one at a time.  Additionally, parameters to
//! multiple PWM generators in synchronous mode can be updated simultaneously,
//! allowing them to be treated as if they were a unified generator.  In
//! non-synchronous mode, the parameter updates are not delayed until a
//! synchronization event.  In either mode, the parameter updates only occur
//! when the counter is at zero to help prevent oddly formed PWM signals during
//! the update (i.e. a PWM pulse that is too short or too long).
//!
//! The PWM generator can either pause or continue running when the processor
//! is stopped via the debugger.  If configured to pause, it will continue to
//! count until it reaches zero, at which point it will pause until the
//! processor is restarted.  If configured to continue running, it will keep
//! counting as if nothing had happened.
//!
//! The \b ulConfig parameter contains the desired configuration.  It is the
//! logical OR of the following: \b PWM_GEN_MODE_DOWN or
//! \b PWM_GEN_MODE_UP_DOWN to specify the counting mode, \b PWM_GEN_MODE_SYNC
//! or \b PWM_GEN_MODE_NO_SYNC to specify the synchronization mode, and
//! \b PWM_GEN_MODE_DBG_RUN or \b PWM_GEN_MODE_DBG_STOP to specify the debug
//! behavior.
//!
//! \note Changes to the counter mode will affect the period of the PWM signals
//! produced.  PWMGenPeriodSet() and PWMPulseWidthSet() should be called after
//! any changes to the counter mode of a generator.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_genconfigure) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenConfigure(unsigned long ulBase, unsigned long ulGen,
                unsigned long ulConfig)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Compute the generator's base address.
    //
    ulGen = PWM_GEN_BADDR(ulBase, ulGen);

    //
    // Change the global configuration of the generator.
    //
    HWREG(ulGen + PWM_O_X_CTL) = ((HWREG(ulGen + PWM_O_X_CTL) &
                                   ~(PWM_X_CTL_MODE | PWM_X_CTL_DEBUG |
                                     PWM_X_CTL_LOADUPD | PWM_X_CTL_CMPAUPD |
                                     PWM_X_CTL_CMPBUPD)) | ulConfig);

    //
    // Set the individual PWM generator controls.
    //
    if(ulConfig & PWM_X_CTL_MODE)
    {
        //
        // In up/down count mode, set the signal high on up count comparison
        // and low on down count comparison (i.e. center align the signals).
        //
        HWREG(ulGen + PWM_O_X_GENA) = ((PWM_GEN_ACT_ONE <<
                                        PWM_GEN_ACT_A_UP_SHIFT) |
                                       (PWM_GEN_ACT_ZERO <<
                                        PWM_GEN_ACT_A_DN_SHIFT));
        HWREG(ulGen + PWM_O_X_GENB) = ((PWM_GEN_ACT_ONE <<
                                        PWM_GEN_ACT_B_UP_SHIFT) |
                                       (PWM_GEN_ACT_ZERO <<
                                        PWM_GEN_ACT_B_DN_SHIFT));
    }
    else
    {
        //
        // In down count mode, set the signal high on load and low on count
        // comparison (i.e. left align the signals).
        //
        HWREG(ulGen + PWM_O_X_GENA) = ((PWM_GEN_ACT_ONE <<
                                        PWM_GEN_ACT_LOAD_SHIFT) |
                                       (PWM_GEN_ACT_ZERO <<
                                        PWM_GEN_ACT_A_DN_SHIFT));
        HWREG(ulGen + PWM_O_X_GENB) = ((PWM_GEN_ACT_ONE <<
                                        PWM_GEN_ACT_LOAD_SHIFT) |
                                       (PWM_GEN_ACT_ZERO <<
                                        PWM_GEN_ACT_B_DN_SHIFT));
    }
}
#endif

//*****************************************************************************
//
//! Set the period of a PWM generator.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to be modified.  Must be one of
//! \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//! \param ulPeriod specifies the period of PWM generator output, measured
//! in clock ticks.
//!
//! This function sets the period of the specified PWM generator block, where
//! the period of the generator block is defined as the number of \b PWM 
//! clock ticks between pulses on the generator block \b zero signal.
//!
//! \note Any subsequent calls made to this function before an update occurs
//! will cause the previous values to be overwritten.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_genperiodset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenPeriodSet(unsigned long ulBase, unsigned long ulGen,
                unsigned long ulPeriod)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Compute the generator's base address.
    //
    ulGen = PWM_GEN_BADDR(ulBase, ulGen);

    //
    // Set the reload register based on the mode.
    //
    if(HWREG(ulGen + PWM_O_X_CTL) & PWM_X_CTL_MODE)
    {
        //
        // In up/down count mode, set the reload register to half the requested
        // period.
        //
        ASSERT((ulPeriod / 2) < 65536);
        HWREG(ulGen + PWM_O_X_LOAD) = ulPeriod / 2;
    }
    else
    {
        //
        // In down count mode, set the reload register to the requested period
        // minus one.
        //
        ASSERT((ulPeriod <= 65536) && (ulPeriod != 0));
        HWREG(ulGen + PWM_O_X_LOAD) = ulPeriod - 1;
    }
}
#endif

//*****************************************************************************
//
//! Gets the period of a PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to query.  Must be one of
//! \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//!
//! This function gets the period of the specified PWM generator block.  The
//! period of the generator block is defined as the number of \b PWM clock
//! ticks between pulses on the generator block \b zero signal.
//!
//! If the update of the counter for the specified PWM generator has yet
//! to be completed, the value returned may not be the active period.  The
//! value returned is the programmed period, measured in \b PWM clock ticks.
//!
//! \return Returns the programmed period of the specified generator block
//! in \b PWM clock ticks.
//
//*****************************************************************************
#if defined(GROUP_genperiodget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
PWMGenPeriodGet(unsigned long ulBase, unsigned long ulGen)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Compute the generator's base address.
    //
    ulGen = PWM_GEN_BADDR(ulBase, ulGen);

    //
    // Figure out the counter mode.
    //
    if(HWREG(ulGen + PWM_O_X_CTL) & PWM_X_CTL_MODE)
    {
        //
        // The period is twice the reload register value.
        //
        return(HWREG(ulGen + PWM_O_X_LOAD) * 2);
    }
    else
    {
        //
        // The period is the reload register value plus one.
        //
        return(HWREG(ulGen + PWM_O_X_LOAD) + 1);
    }
}
#endif

//*****************************************************************************
//
//! Enables the timer/counter for a PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to be enabled.  Must be one of
//! \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//!
//! This function allows the \b PWM clock to drive the timer/counter for the
//! specified generator block.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_genenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenEnable(unsigned long ulBase, unsigned long ulGen)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Enable the PWM generator.
    //
    HWREG(PWM_GEN_BADDR(ulBase, ulGen) + PWM_O_X_CTL) |= PWM_X_CTL_ENABLE;
}
#endif

//*****************************************************************************
//
//! Disables the timer/counter for a PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to be disabled.  Must be one of
//! \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//!
//! This function blocks the \b PWM clock from driving the timer/counter for 
//! the specified generator block.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_gendisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenDisable(unsigned long ulBase, unsigned long ulGen)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Disable the PWM generator.
    //
    HWREG(PWM_GEN_BADDR(ulBase, + ulGen) + PWM_O_X_CTL) &= ~(PWM_X_CTL_ENABLE);
}
#endif

//*****************************************************************************
//
//! Sets the pulse width for the specified PWM output.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulPWMOut is the PWM output to modify.  Must be one of \b PWM_OUT_0,
//! \b PWM_OUT_1, \b PWM_OUT_2, \b PWM_OUT_3, \b PWM_OUT_4, or \b PWM_OUT_5.
//! \param ulWidth specifies the width of the positive portion of the pulse.
//!
//! This function sets the pulse width for the specified PWM output, where the
//! pulse width is defined as the number of \b PWM clock ticks.
//!
//! \note Any subsequent calls made to this function before an update occurs
//! will cause the previous values to be overwritten.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_pulsewidthset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMPulseWidthSet(unsigned long ulBase, unsigned long ulPWMOut,
                 unsigned long ulWidth)
{
    unsigned long ulGenBase, ulReg;

    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulPWMOut == PWM_OUT_0) || (ulPWMOut == PWM_OUT_1) ||
           (ulPWMOut == PWM_OUT_2) || (ulPWMOut == PWM_OUT_3) ||
           (ulPWMOut == PWM_OUT_4) || (ulPWMOut == PWM_OUT_5));

    //
    // Compute the generator's base address.
    //
    ulGenBase = PWM_OUT_BADDR(ulBase, ulPWMOut);

    //
    // If the counter is in up/down count mode, divide the width by two.
    //
    if(HWREG(ulGenBase + PWM_O_X_CTL) & PWM_X_CTL_MODE)
    {
        ulWidth /= 2;
    }

    //
    // Get the period.
    //
    ulReg = HWREG(ulGenBase + PWM_O_X_LOAD);

    //
    // Make sure the width is not too large.
    //
    ASSERT(ulWidth < ulReg);

    //
    // Compute the compare value.
    //
    ulReg = ulReg - ulWidth;

    //
    // Write to the appropriate registers.
    //
    if(PWM_IS_OUTPUT_ODD(ulPWMOut))
    {
        HWREG(ulGenBase + PWM_O_X_CMPB) = ulReg;
    }
    else
    {
        HWREG(ulGenBase + PWM_O_X_CMPA) = ulReg;
    }
}
#endif

//*****************************************************************************
//
//! Gets the pulse width of a PWM output.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulPWMOut is the PWM output to query.  Must be one of \b PWM_OUT_0,
//! \b PWM_OUT_1, \b PWM_OUT_2, \b PWM_OUT_3, \b PWM_OUT_4, or \b PWM_OUT_5.
//!
//! This function gets the currently programmed pulse width for the
//! specified PWM output.  If the update of the comparator for the specified
//! output has yet to be completed, the value returned may not be the active
//! pulse width.  The value returned is the programmed pulse width, measured
//! in \b PWM clock ticks.
//!
//! \return Returns the width of the pulse in \b PWM clock ticks.
//
//*****************************************************************************
#if defined(GROUP_pulsewidthget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
PWMPulseWidthGet(unsigned long ulBase, unsigned long ulPWMOut)
{
    unsigned long ulGenBase, ulReg, ulLoad;

    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulPWMOut == PWM_OUT_0) || (ulPWMOut == PWM_OUT_1) ||
           (ulPWMOut == PWM_OUT_2) || (ulPWMOut == PWM_OUT_3) ||
           (ulPWMOut == PWM_OUT_4) || (ulPWMOut == PWM_OUT_5));

    //
    // Compute the generator's base address.
    //
    ulGenBase = PWM_OUT_BADDR(ulBase, ulPWMOut);

    //
    // Then compute the pulse width.  If mode is UpDown, set
    // width = (load-compare)*2.  Otherwise, set width = load - compare
    //
    ulLoad = HWREG(ulGenBase + PWM_O_X_LOAD);
    if(PWM_IS_OUTPUT_ODD(ulPWMOut))
    {
        ulReg = HWREG(ulGenBase + PWM_O_X_CMPB);
    }
    else
    {
        ulReg = HWREG(ulGenBase + PWM_O_X_CMPA);
    }
    ulReg = ulLoad - ulReg;

    //
    // If in up/down count mode, double the pulse width.
    //
    if(HWREG(ulGenBase + PWM_O_X_CTL) & PWM_X_CTL_MODE)
    {
        ulReg = ulReg * 2;
    }

    //
    // Return the pulse width.
    //
    return(ulReg);
}
#endif

//*****************************************************************************
//
//! Enables the PWM dead band output, and sets the dead band delays.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to modify.  Must be one of
//! \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//! \param usRise specifies the width of delay from the rising edge.
//! \param usFall specifies the width of delay from the falling edge.
//!
//! This function sets the dead bands for the specified PWM generator,
//! where the dead bands are defined as the number of \b PWM clock ticks
//! from the rising or falling edge of the generator's \b OutA signal.
//! Note that this function causes the coupling of \b OutB to \b OutA.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_deadbandenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMDeadBandEnable(unsigned long ulBase, unsigned long ulGen,
                  unsigned short usRise, unsigned short usFall)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));
    ASSERT(usRise < 4096);
    ASSERT(usFall < 4096);

    //
    // Compute the generator's base address.
    //
    ulGen = PWM_GEN_BADDR(ulBase, ulGen);

    //
    // Write the dead band delay values.
    //
    HWREG(ulGen + PWM_O_X_DBRISE) = usRise;
    HWREG(ulGen + PWM_O_X_DBFALL) = usFall;

    //
    // Enable the deadband functionality.
    //
    HWREG(ulGen + PWM_O_X_DBCTL) |= PWM_DBCTL_ENABLE;
}
#endif

//*****************************************************************************
//
//! Disables the PWM dead band output.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to modify.  Must be one of
//! \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//!
//! This function disables the dead band mode for the specified PWM generator.
//! Doing so decouples the \b OutA and \b OutB signals.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_deadbanddisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMDeadBandDisable(unsigned long ulBase, unsigned long ulGen)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Disable the deadband functionality.
    //
    HWREG(PWM_GEN_BADDR(ulBase, ulGen) + PWM_O_X_DBCTL) &= ~(PWM_DBCTL_ENABLE);
}
#endif

//*****************************************************************************
//
//! Synchronizes all pending updates.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGenBits are the PWM generator blocks to be updated.  Must be the
//! logical OR of any of \b PWM_GEN_0_BIT, \b PWM_GEN_1_BIT, or
//! \b PWM_GEN_2_BIT.
//!
//! For the selected PWM generators, this function causes all queued updates to
//! the period or pulse width to be applied the next time the corresponding
//! counter becomes zero.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_syncupdate) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMSyncUpdate(unsigned long ulBase, unsigned long ulGenBits)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT(!(ulGenBits & ~(PWM_GEN_0_BIT | PWM_GEN_1_BIT | PWM_GEN_2_BIT)));

    //
    // Update the PWM timing registers.
    //
    HWREG(ulBase + PWM_O_CTL) = ulGenBits;
}
#endif

//*****************************************************************************
//
//! Synchronizes the counters in one or multiple PWM generator blocks.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGenBits are the PWM generator blocks to be synchronized.  Must be
//! the logical OR of any of \b PWM_GEN_0_BIT, \b PWM_GEN_1_BIT, or
//! \b PWM_GEN_2_BIT.
//!
//! For the selected PWM module, this function synchronizes the time base
//! of the generator blocks by causing the specified generator counters to be
//! reset to zero.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_synctimebase) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMSyncTimeBase(unsigned long ulBase, unsigned long ulGenBits)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT(!(ulGenBits & ~(PWM_GEN_0_BIT | PWM_GEN_1_BIT | PWM_GEN_2_BIT)));

    //
    // Synchronize the counters in the specified generators by writing to
    // the module's synchronization register.
    //
    HWREG(ulBase + PWM_O_SYNC) = ulGenBits;
}
#endif

//*****************************************************************************
//
//! Enables or disables PWM outputs.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulPWMOutBits are the PWM outputs to be modified.  Must be the
//! logical OR of any of \b PWM_OUT_0_BIT, \b PWM_OUT_1_BIT, \b PWM_OUT_2_BIT,
//! \b PWM_OUT_3_BIT, \b PWM_OUT_4_BIT, or \b PWM_OUT_5_BIT.
//! \param bEnable determines if the signal is enabled or disabled.
//!
//! This function is used to enable or disable the selected PWM outputs.  The
//! outputs are selected using the parameter \e ulPWMOutBits.  The parameter
//! \e bEnable determines the state of the selected outputs.  If \e bEnable is
//! \b true, then the selected PWM outputs are enabled, or placed in the active
//! state.  If \e bEnable is \b false, then the selected outputs are disabled,
//! or placed in the inactive state.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_outputstate) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMOutputState(unsigned long ulBase, unsigned long ulPWMOutBits,
               tBoolean bEnable)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT(!(ulPWMOutBits & ~(PWM_OUT_0_BIT | PWM_OUT_1_BIT | PWM_OUT_2_BIT |
                              PWM_OUT_3_BIT | PWM_OUT_4_BIT | PWM_OUT_5_BIT)));

    //
    // Read the module's ENABLE output control register, and set or clear
    // the requested bits.
    //
    if(bEnable == true)
    {
        HWREG(ulBase + PWM_O_ENABLE) |= ulPWMOutBits;
    }
    else
    {
        HWREG(ulBase + PWM_O_ENABLE) &= ~(ulPWMOutBits);
    }
}
#endif

//*****************************************************************************
//
//! Selects the inversion mode for PWM outputs.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulPWMOutBits are the PWM outputs to be modified.  Must be the
//! logical OR of any of \b PWM_OUT_0_BIT, \b PWM_OUT_1_BIT, \b PWM_OUT_2_BIT,
//! \b PWM_OUT_3_BIT, \b PWM_OUT_4_BIT, or \b PWM_OUT_5_BIT.
//! \param bInvert determines if the signal is inverted or passed through.
//!
//! This function is used to select the inversion mode for the selected PWM
//! outputs.  The outputs are selected using the parameter \e ulPWMOutBits.
//! The parameter \e bInvert determines the inversion mode for the selected
//! outputs.  If \e bInvert is \b true, this function will cause the specified
//! PWM output signals to be inverted, or made active low.  If \e bInvert is
//! \b false, the specified output will be passed through as is, or be made
//! active high.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_outputinvert) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMOutputInvert(unsigned long ulBase, unsigned long ulPWMOutBits,
                tBoolean bInvert)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT(!(ulPWMOutBits & ~(PWM_OUT_0_BIT | PWM_OUT_1_BIT | PWM_OUT_2_BIT |
                              PWM_OUT_3_BIT | PWM_OUT_4_BIT | PWM_OUT_5_BIT)));

    //
    // Read the module's INVERT output control register, and set or clear
    // the requested bits.
    //
    if(bInvert == true)
    {
        HWREG(ulBase + PWM_O_INVERT) |= ulPWMOutBits;
    }
    else
    {
        HWREG(ulBase + PWM_O_INVERT) &= ~(ulPWMOutBits);
    }
}
#endif

//*****************************************************************************
//
//! Specifies the state of PWM outputs in response to a fault condition.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulPWMOutBits are the PWM outputs to be modified.  Must be the
//! logical OR of any of \b PWM_OUT_0_BIT, \b PWM_OUT_1_BIT, \b PWM_OUT_2_BIT,
//! \b PWM_OUT_3_BIT, \b PWM_OUT_4_BIT, or \b PWM_OUT_5_BIT.
//! \param bFaultKill determines if the signal is killed or passed through
//! during an active fault condition.
//!
//! This function sets the fault handling characteristics of the selected PWM
//! outputs.  The outputs are selected using the parameter \e ulPWMOutBits.
//! The parameter \e bFaultKill determines the fault handling characteristics
//! for the selected outputs.  If \e bFaultKill is \b true, then the selected
//! outputs will be made inactive.  If \e bFaultKill is \b false, then the
//! selected outputs are unaffected by the detected fault.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_outputfault) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMOutputFault(unsigned long ulBase, unsigned long ulPWMOutBits,
               tBoolean bFaultKill)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT(!(ulPWMOutBits & ~(PWM_OUT_0_BIT | PWM_OUT_1_BIT | PWM_OUT_2_BIT |
                              PWM_OUT_3_BIT | PWM_OUT_4_BIT | PWM_OUT_5_BIT)));

    //
    // Read the module's FAULT output control register, and set or clear
    // the requested bits.
    //
    if(bFaultKill == true)
    {
        HWREG(ulBase + PWM_O_FAULT) |= ulPWMOutBits;
    }
    else
    {
        HWREG(ulBase + PWM_O_FAULT) &= ~(ulPWMOutBits);
    }
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for the specified PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator in question.
//! \param pfnIntHandler is a pointer to the function to be called when the PWM
//! generator interrupt occurs.
//!
//! This function will ensure that the interrupt handler specified by
//! \e pfnIntHandler is called when an interrupt is detected for the specified
//! PWM generator block.  This function will also enable the corresponding
//! PWM generator interrupt in the interrupt controller; individual generator
//! interrupts and interrupt sources must be enabled with PWMIntEnable() and
//! PWMGenIntTrigEnable().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_genintregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenIntRegister(unsigned long ulBase, unsigned long ulGen,
                  void (*pfnIntHandler)(void))
{
    unsigned long ulInt;

    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Get the interrupt number associated with the specified generator.
    //
    ulInt = INT_PWM0 + (ulGen >> 6) - 1;

    //
    // Register the interrupt handler.
    //
    IntRegister(ulInt, pfnIntHandler);

    //
    // Enable the PWMx interrupt.
    //
    IntEnable(ulInt);
}
#endif

//*****************************************************************************
//
//! Removes an interrupt handler for the specified PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator in question.
//!
//! This function will unregister the interrupt handler for the specified
//! PWM generator block.  This function will also disable the corresponding
//! PWM generator interrupt in the interrupt controller; individual generator
//! interrupts and interrupt sources must be disabled with PWMIntDisable() and
//! PWMGenIntTrigDisable().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_genintunregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenIntUnregister(unsigned long ulBase, unsigned long ulGen)
{
    unsigned long ulInt;

    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Get the interrupt number associated with the specified generator.
    //
    ulInt = INT_PWM0 + (ulGen >> 6) - 1;

    //
    // Disable the PWMx interrupt.
    //
    IntDisable(ulInt);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(ulInt);
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for a fault condition detected in a PWM
//! module.
//!
//! \param ulBase is the base address of the PWM module.
//! \param pfnIntHandler is a pointer to the function to be called when the PWM
//! fault interrupt occurs.
//!
//! This function will ensure that the interrupt handler specified by
//! \e pfnIntHandler is called when a fault interrupt is detected for the
//! selected PWM module.  This function will also enable the PWM fault
//! interrupt in the NVIC; the PWM fault interrupt must also be enabled at the
//! module level using PWMIntEnable().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_faultintregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMFaultIntRegister(unsigned long ulBase, void (*pfnIntHandler)(void))
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);

    //
    // Register the interrupt handler, returning an error if one occurs.
    //
    IntRegister(INT_PWM_FAULT, pfnIntHandler);

    //
    // Enable the PWM fault interrupt.
    //
    IntEnable(INT_PWM_FAULT);
}
#endif

//*****************************************************************************
//
//! Removes the PWM fault condition interrupt handler.
//!
//! \param ulBase is the base address of the PWM module.
//!
//! This function will remove the interrupt handler for a PWM fault interrupt
//! from the selected PWM module.  This function will also disable the PWM
//! fault interrupt in the NVIC; the PWM fault interrupt must also be disabled
//! at the module level using PWMIntDisable().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_faultintunregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMFaultIntUnregister(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);

    //
    // Disable the PWM fault interrupt.
    //
    IntDisable(INT_PWM_FAULT);

    //
    // Unregister the interrupt handler, returning an error if one occurs.
    //
    IntUnregister(INT_PWM_FAULT);
}
#endif

//*****************************************************************************
//
//! Enables interrupts and triggers for the specified PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to have interrupts and triggers enabled.
//! Must be one of \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//! \param ulIntTrig specifies the interrupts and triggers to be enabled.
//!
//! Unmasks the specified interrupt(s) and trigger(s) by setting the
//! specified bits of the interrupt/trigger enable register for the specified
//! PWM generator.  The defined values for the bits are as follows:
//!
//! - PWM_INT_CNT_ZERO
//! - PWM_INT_CNT_LOAD
//! - PWM_INT_CMP_AU
//! - PWM_INT_CMP_AD
//! - PWM_INT_CMP_BU
//! - PWM_INT_CMP_BD
//! - PWM_TR_CNT_ZERO
//! - PWM_TR_CNT_LOAD
//! - PWM_TR_CMP_AU
//! - PWM_TR_CMP_AD
//! - PWM_TR_CMP_BU
//! - PWM_TR_CMP_BD
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_geninttrigenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenIntTrigEnable(unsigned long ulBase, unsigned long ulGen,
                    unsigned long ulIntTrig)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Enable the specified interrupts/triggers.
    //
    HWREG(PWM_GEN_BADDR(ulBase, ulGen) + PWM_O_X_INTEN) |= ulIntTrig;
}
#endif

//*****************************************************************************
//
//! Disables interrupts for the specified PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to have interrupts and triggers disabled.
//! Must be one of \b PWM_GEN_0, \b PWM_GEN_1, or \b PWM_GEN_2.
//! \param ulIntTrig specifies the interrupts and triggers to be disabled.
//!
//! Masks the specified interrupt(s) and trigger(s) by clearing the
//! specified bits of the interrupt/trigger enable register for the specified
//! PWM generator.  The defined values for the bits are as follows:
//!
//! - PWM_INT_CNT_ZERO
//! - PWM_INT_CNT_LOAD
//! - PWM_INT_CMP_AU
//! - PWM_INT_CMP_AD
//! - PWM_INT_CMP_BU
//! - PWM_INT_CMP_BD
//! - PWM_TR_CNT_ZERO
//! - PWM_TR_CNT_LOAD
//! - PWM_TR_CMP_AU
//! - PWM_TR_CMP_AD
//! - PWM_TR_CMP_BU
//! - PWM_TR_CMP_BD
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_geninttrigdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenIntTrigDisable(unsigned long ulBase, unsigned long ulGen,
                     unsigned long ulIntTrig)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Disable the specified interrupts/triggers.
    //
    HWREG(PWM_GEN_BADDR(ulBase, ulGen) + PWM_O_X_INTEN) &= ~(ulIntTrig);
}
#endif

//*****************************************************************************
//
//! Gets interrupt status for the specified PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to query.  Must be one of \b PWM_GEN_0,
//! \b PWM_GEN_1, or \b PWM_GEN_2.
//! \param bMasked specifies whether masked or raw interrupt status is
//! returned.
//!
//! If \e bMasked is set as \b true, then the masked interrupt status is
//! returned; otherwise, the raw interrupt status will be returned.
//!
//! \return Returns the contents of the interrupt status register, or the
//! contents of the raw interrupt status register, for the specified
//! PWM generator.
//
//*****************************************************************************
#if defined(GROUP_genintstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
PWMGenIntStatus(unsigned long ulBase, unsigned long ulGen, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Compute the generator's base address.
    //
    ulGen = PWM_GEN_BADDR(ulBase, ulGen);

    //
    // Read and return the specified generator's raw or enabled interrupt
    // status.
    //
    if(bMasked == true)
    {
        return(HWREG(ulGen + PWM_O_X_ISC));
    }
    else
    {
        return(HWREG(ulGen + PWM_O_X_RIS));
    }
}
#endif

//*****************************************************************************
//
//! Clears the specified interrupt(s) for the specified PWM generator block.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGen is the PWM generator to query.  Must be one of \b PWM_GEN_0,
//! \b PWM_GEN_1, or \b PWM_GEN_2.
//! \param ulInts specifies the interrupts to be cleared.
//!
//! Clears the specified interrupt(s) by writing a 1 to the specified bits
//! of the interrupt status register for the specified PWM generator.  The
//! defined values for the bits are as follows:
//!
//! - PWM_INT_CNT_ZERO
//! - PWM_INT_CNT_LOAD
//! - PWM_INT_CMP_AU
//! - PWM_INT_CMP_AD
//! - PWM_INT_CMP_BU
//! - PWM_INT_CMP_BD
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_genintclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMGenIntClear(unsigned long ulBase, unsigned long ulGen, unsigned long ulInts)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);
    ASSERT((ulGen == PWM_GEN_0) || (ulGen == PWM_GEN_1) ||
           (ulGen == PWM_GEN_2));

    //
    // Clear the requested interrupts by writing ones to the specified bit
    // of the module's interrupt enable register.
    //
    HWREG(PWM_GEN_BADDR(ulBase, ulGen) + PWM_O_X_ISC) = ulInts;
}
#endif

//*****************************************************************************
//
//! Enables generator and fault interrupts for a PWM module.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGenFault contains the interrupts to be enabled.  Must be a logical
//! OR of any of \b PWM_INT_GEN_0, \b PWM_INT_GEN_1, \b PWM_INT_GEN_2, or
//! \b PWM_INT_FAULT.
//!
//! Unmasks the specified interrupt(s) by setting the specified bits of
//! the interrupt enable register for the selected PWM module.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMIntEnable(unsigned long ulBase, unsigned long ulGenFault)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);

    //
    // Read the module's interrupt enable register, and enable interrupts
    // for the specified PWM generators.
    //
    HWREG(ulBase + PWM_O_INTEN) |= ulGenFault;
}
#endif

//*****************************************************************************
//
//! Disables generator and fault interrupts for a PWM module.
//!
//! \param ulBase is the base address of the PWM module.
//! \param ulGenFault contains the interrupts to be disabled.  Must be a
//! logical OR of any of \b PWM_INT_GEN_0, \b PWM_INT_GEN_1, \b PWM_INT_GEN_2,
//! or \b PWM_INT_FAULT.
//!
//! Masks the specified interrupt(s) by clearing the specified bits of
//! the interrupt enable register for the selected PWM module.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMIntDisable(unsigned long ulBase, unsigned long ulGenFault)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);

    //
    // Read the module's interrupt enable register, and disable interrupts
    // for the specified PWM generators.
    //
    HWREG(ulBase + PWM_O_INTEN) &= ~(ulGenFault);
}
#endif

//*****************************************************************************
//
//! Clears the fault interrupt for a PWM module.
//!
//! \param ulBase is the base address of the PWM module.
//!
//! Clears the fault interrupt by writing to the appropriate bit of the
//! interrupt status register for the selected PWM module.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_faultintclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
PWMFaultIntClear(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);

    //
    // Write the only writeable bit in the module's interrupt register.
    //
    HWREG(ulBase + PWM_O_ISC) = PWM_INT_INTFAULT;
}
#endif

//*****************************************************************************
//
//! Gets the interrupt status for a PWM module.
//!
//! \param ulBase is the base address of the PWM module.
//! \param bMasked specifies whether masked or raw interrupt status is
//! returned.
//!
//! If \e bMasked is set as \b true, then the masked interrupt status is
//! returned; otherwise, the raw interrupt status will be returned.
//!
//! \return The current interrupt status, enumerated as a bit field of
//! \b PWM_INT_GEN_0, \b PWM_INT_GEN_1, \b PWM_INT_GEN_2, and \b PWM_INT_FAULT.
//!
//*****************************************************************************
#if defined(GROUP_intstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
PWMIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == PWM_BASE);

    //
    // Read and return either the module's raw or enabled interrupt status.
    //
    if(bMasked == true)
    {
        return(HWREG(ulBase + PWM_O_ISC));
    }
    else
    {
        return(HWREG(ulBase + PWM_O_RIS));
    }
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
