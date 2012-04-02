//*****************************************************************************
//
// watchdog.c - Driver for the Watchdog Timer Module.
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
//! \addtogroup watchdog_api
//! @{
//
//*****************************************************************************

#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_types.h"
#include "../hw_watchdog.h"
#include "debug.h"
#include "interrupt.h"
#include "watchdog.h"

//*****************************************************************************
//
//! Determines if the watchdog timer is enabled.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! This will check to see if the watchdog timer is enabled.
//!
//! \return Returns \b true if the watchdog timer is enabled, and \b false
//! if it is not.
//
//*****************************************************************************
#if defined(GROUP_running) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
WatchdogRunning(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // See if the watchdog timer module is enabled, and return.
    //
    return(HWREG(ulBase + WDT_O_CTL) & WDT_CTL_INTEN);
}
#endif

//*****************************************************************************
//
//! Enables the watchdog timer.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! This will enable the watchdog timer counter and interrupt.
//!
//! \note This function will have no effect if the watchdog timer has
//! been locked.
//!
//! \sa WatchdogLock(), WatchdogUnlock()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_enable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Enable the watchdog timer module.
    //
    HWREG(ulBase + WDT_O_CTL) |= WDT_CTL_INTEN;
}
#endif

//*****************************************************************************
//
//! Enables the watchdog timer reset.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! Enables the capability of the watchdog timer to issue a reset to the
//! processor upon a second timeout condition.
//!
//! \note This function will have no effect if the watchdog timer has
//! been locked.
//!
//! \sa WatchdogLock(), WatchdogUnlock()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_resetenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogResetEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Enable the watchdog reset.
    //
    HWREG(ulBase + WDT_O_CTL) |= WDT_CTL_RESEN;
}
#endif

//*****************************************************************************
//
//! Disables the watchdog timer reset.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! Disables the capability of the watchdog timer to issue a reset to the
//! processor upon a second timeout condition.
//!
//! \note This function will have no effect if the watchdog timer has
//! been locked.
//!
//! \sa WatchdogLock(), WatchdogUnlock()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_resetdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogResetDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Disable the watchdog reset.
    //
    HWREG(ulBase + WDT_O_CTL) &= ~(WDT_CTL_RESEN);
}
#endif

//*****************************************************************************
//
//! Enables the watchdog timer lock mechanism.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! Locks out write access to the watchdog timer configuration registers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_lock) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogLock(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Lock out watchdog register writes.  Writing anything to the WDT_O_LOCK
    // register causes the lock to go into effect.
    //
    HWREG(ulBase + WDT_O_LOCK) = WDT_LOCK_LOCKED;
}
#endif

//*****************************************************************************
//
//! Disables the watchdog timer lock mechanism.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! Enables write access to the watchdog timer configuration registers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_unlock) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogUnlock(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Unlock watchdog register writes.
    //
    HWREG(ulBase + WDT_O_LOCK) = WDT_LOCK_UNLOCK;
}
#endif

//*****************************************************************************
//
//! Gets the state of the watchdog timer lock mechanism.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! Returns the lock state of the watchdog timer registers.
//!
//! \return Returns \b true if the watchdog timer registers are locked, and
//! \b false if they are not locked.
//
//*****************************************************************************
#if defined(GROUP_lockstate) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
WatchdogLockState(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Get the lock state.
    //
    return((HWREG(ulBase + WDT_O_LOCK) == WDT_LOCK_LOCKED) ? true : false);
}
#endif

//*****************************************************************************
//
//! Sets the watchdog timer reload value.
//!
//! \param ulBase is the base address of the watchdog timer module.
//! \param ulLoadVal is the load value for the watchdog timer.
//!
//! This function sets the value to load into the watchdog timer when the count
//! reaches zero for the first time; if the watchdog timer is running when this
//! function is called, then the value will be immediately loaded into the
//! watchdog timer counter. If the parameter \e ulLoadVal is 0, then an
//! interrupt is immediately generated.
//!
//! \note This function will have no effect if the watchdog timer has
//! been locked.
//!
//! \sa WatchdogLock(), WatchdogUnlock(), WatchdogReloadGet()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_reloadset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogReloadSet(unsigned long ulBase, unsigned long ulLoadVal)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Set the load register.
    //
    HWREG(ulBase + WDT_O_LOAD) = ulLoadVal;
}
#endif

//*****************************************************************************
//
//! Gets the watchdog timer reload value.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! This function gets the value that is loaded into the watchdog timer when
//! the count reaches zero for the first time.
//!
//! \sa WatchdogReloadSet()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_reloadget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
WatchdogReloadGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Get the load register.
    //
    return(HWREG(ulBase + WDT_O_LOAD));
}
#endif

//*****************************************************************************
//
//! Gets the current watchdog timer value.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! This function reads the current value of the watchdog timer.
//!
//! \return Returns the current value of the watchdog timer.
//
//*****************************************************************************
#if defined(GROUP_valueget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
WatchdogValueGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Get the current watchdog timer register value.
    //
    return(HWREG(ulBase + WDT_O_VALUE));
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for watchdog timer interrupt.
//!
//! \param ulBase is the base address of the watchdog timer module.
//! \param pfnHandler is a pointer to the function to be called when the
//! watchdog timer interrupt occurs.
//!
//! This function does the actual registering of the interrupt handler.  This
//! will enable the global interrupt in the interrupt controller; the watchdog
//! timer interrupt must be enabled via WatchdogEnable(). It is the interrupt
//! handler's responsibility to clear the interrupt source via
//! WatchdogIntClear().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogIntRegister(unsigned long ulBase, void (*pfnHandler)(void))
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Register the interrupt handler.
    //
    IntRegister(INT_WATCHDOG, pfnHandler);

    //
    // Enable the watchdog timer interrupt.
    //
    IntEnable(INT_WATCHDOG);
}
#endif

//*****************************************************************************
//
//! Unregisters an interrupt handler for the watchdog timer interrupt.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! This function does the actual unregistering of the interrupt handler.  This
//! function will clear the handler to be called when a watchdog timer
//! interrupt occurs.  This will also mask off the interrupt in the interrupt
//! controller so that the interrupt handler no longer is called.
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intunregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogIntUnregister(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Disable the interrupt.
    //
    IntDisable(INT_WATCHDOG);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(INT_WATCHDOG);
}
#endif

//*****************************************************************************
//
//! Enables the watchdog timer interrupt.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! Enables the watchdog timer interrupt.
//!
//! \note This function will have no effect if the watchdog timer has
//! been locked.
//!
//! \sa WatchdogLock(), WatchdogUnlock(), WatchdogEnable()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogIntEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Enable the watchdog interrupt.
    //
    HWREG(ulBase + WDT_O_CTL) |= WDT_CTL_INTEN;
}
#endif

//*****************************************************************************
//
//! Gets the current watchdog timer interrupt status.
//!
//! \param ulBase is the base address of the watchdog timer module.
//! \param bMasked is \b false if the raw interrupt status is required and
//! \b true if the masked interrupt status is required.
//!
//! This returns the interrupt status for the watchdog timer module.  Either
//! the raw interrupt status or the status of interrupt that is allowed to
//! reflect to the processor can be returned.
//!
//! \return The current interrupt status, where a 1 indicates that the watchdog
//! interrupt is active, and a 0 indicates that it is not active.
//
//*****************************************************************************
#if defined(GROUP_intstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
WatchdogIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return(HWREG(ulBase + WDT_O_MIS));
    }
    else
    {
        return(HWREG(ulBase + WDT_O_RIS));
    }
}
#endif

//*****************************************************************************
//
//! Clears the watchdog timer interrupt.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! The watchdog timer interrupt source is cleared, so that it no longer
//! asserts.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogIntClear(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Clear the interrupt source.
    //
    HWREG(ulBase + WDT_O_ICR) = WDT_INT_TIMEOUT;
}
#endif

//*****************************************************************************
//
//! Enables stalling of the watchdog timer during debug events.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! This function allows the watchdog timer to stop counting when the processor
//! is stopped by the debugger.  By doing so, the watchdog is prevented from
//! expiring (typically almost immediately from a human time perspective) and
//! resetting the system (if reset is enabled).  The watchdog will instead
//! expired after the appropriate number of processor cycles have been executed
//! while debugging (or at the appropriate time after the processor has been
//! restarted).
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_stallenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogStallEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Enable timer stalling.
    //
    HWREG(ulBase + WDT_O_TEST) |= WDT_TEST_STALL;
}
#endif

//*****************************************************************************
//
//! Disables stalling of the watchdog timer during debug events.
//!
//! \param ulBase is the base address of the watchdog timer module.
//!
//! This function disables the debug mode stall of the watchdog timer.  By
//! doing so, the watchdog timer continues to count regardless of the processor
//! debug state.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_stalldisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
WatchdogStallDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == WATCHDOG_BASE);

    //
    // Disable timer stalling.
    //
    HWREG(ulBase + WDT_O_TEST) &= ~(WDT_TEST_STALL);
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
