//*****************************************************************************
//
// comp.c - Driver for the analog comparator.
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
//! \addtogroup comp_api
//! @{
//
//*****************************************************************************

#include "../hw_comp.h"
#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_types.h"
#include "comp.h"
#include "debug.h"
#include "interrupt.h"

//*****************************************************************************
//
//! Configures a comparator.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator to configure.
//! \param ulConfig is the configuration of the comparator.
//!
//! This function will configure a comparator.  The \e ulConfig parameter is
//! the result of a logical OR operation between the \b COMP_TRIG_xxx,
//! \b COMP_INT_xxx, \b COMP_ASRCP_xxx, and \b COMP_OUTPUT_xxx values.
//!
//! The \b COMP_TRIG_xxx term can take on the following values:
//!
//! - \b COMP_TRIG_NONE to have no trigger to the ADC.
//! - \b COMP_TRIG_HIGH to trigger the ADC when the comparator output is high.
//! - \b COMP_TRIG_LOW to trigger the ADC when the comparator output is low.
//! - \b COMP_TRIG_FALL to trigger the ADC when the comparator output goes low.
//! - \b COMP_TRIG_RISE to trigger the ADC when the comparator output goes
//! high.
//! - \b COMP_TRIG_BOTH to trigger the ADC when the comparator output goes low
//! or high.
//!
//! The \b COMP_INT_xxx term can take on the following values:
//!
//! - \b COMP_INT_HIGH to generate an interrupt when the comparator output is
//! high.
//! - \b COMP_INT_LOW to generate an interrupt when the comparator output is
//! low.
//! - \b COMP_INT_FALL to generate an interrupt when the comparator output goes
//! low.
//! - \b COMP_INT_RISE to generate an interrupt when the comparator output goes
//! high.
//! - \b COMP_INT_BOTH to generate an interrupt when the comparator output goes
//! low or high.
//!
//! The \b COMP_ASRCP_xxx term can take on the following values:
//!
//! - \b COMP_ASRCP_PIN to use the dedicated Comp+ pin as the reference
//! voltage.
//! - \b COMP_ASRCP_PIN0 to use the Comp0+ pin as the reference voltage (this
//! the same as \b COMP_ASRCP_PIN for the comparator 0).
//! - \b COMP_ASRCP_REF to use the internally generated voltage as the
//! reference voltage.
//!
//! The \b COMP_OUTPUT_xxx term can take on the following values:
//!
//! - \b COMP_OUTPUT_NONE to disable the output from the comparator to a device
//! pin.
//! - \b COMP_OUTPUT_NORMAL to enable a non-inverted output from the comparator
//! to a device pin.
//! - \b COMP_OUTPUT_INVERT to enable an inverted output from the comparator to
//! a device pin.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_configure) || defined(BUILD_ALL) || defined(DOXYGEN)
void
ComparatorConfigure(unsigned long ulBase, unsigned long ulComp,
                    unsigned long ulConfig)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Configure this comparator.
    //
    HWREG(ulBase + (ulComp * 0x20) + COMP_O_ACCTL0) = ulConfig;
}
#endif

//*****************************************************************************
//
//! Sets the internal reference voltage.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulRef is the desired reference voltage.
//!
//! This function will set the internal reference voltage value.  The voltage
//! is specified as one of the following values:
//!
//! - \b COMP_REF_OFF to turn off the reference voltage
//! - \b COMP_REF_0V to set the reference voltage to 0 V
//! - \b COMP_REF_0_1375V to set the reference voltage to 0.1375 V
//! - \b COMP_REF_0_275V to set the reference voltage to 0.275 V
//! - \b COMP_REF_0_4125V to set the reference voltage to 0.4125 V
//! - \b COMP_REF_0_55V to set the reference voltage to 0.55 V
//! - \b COMP_REF_0_6875V to set the reference voltage to 0.6875 V
//! - \b COMP_REF_0_825V to set the reference voltage to 0.825 V
//! - \b COMP_REF_0_928125V to set the reference voltage to 0.928125 V
//! - \b COMP_REF_0_9625V to set the reference voltage to 0.9625 V
//! - \b COMP_REF_1_03125V to set the reference voltage to 1.03125 V
//! - \b COMP_REF_1_134375V to set the reference voltage to 1.134375 V
//! - \b COMP_REF_1_1V to set the reference voltage to 1.1 V
//! - \b COMP_REF_1_2375V to set the reference voltage to 1.2375 V
//! - \b COMP_REF_1_340625V to set the reference voltage to 1.340625 V
//! - \b COMP_REF_1_375V to set the reference voltage to 1.375 V
//! - \b COMP_REF_1_44375V to set the reference voltage to 1.44375 V
//! - \b COMP_REF_1_5125V to set the reference voltage to 1.5125 V
//! - \b COMP_REF_1_546875V to set the reference voltage to 1.546875 V
//! - \b COMP_REF_1_65V to set the reference voltage to 1.65 V
//! - \b COMP_REF_1_753125V to set the reference voltage to 1.753125 V
//! - \b COMP_REF_1_7875V to set the reference voltage to 1.7875 V
//! - \b COMP_REF_1_85625V to set the reference voltage to 1.85625 V
//! - \b COMP_REF_1_925V to set the reference voltage to 1.925 V
//! - \b COMP_REF_1_959375V to set the reference voltage to 1.959375 V
//! - \b COMP_REF_2_0625V to set the reference voltage to 2.0625 V
//! - \b COMP_REF_2_165625V to set the reference voltage to 2.165625 V
//! - \b COMP_REF_2_26875V to set the reference voltage to 2.26875 V
//! - \b COMP_REF_2_371875V to set the reference voltage to 2.371875 V
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_refset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
ComparatorRefSet(unsigned long ulBase, unsigned long ulRef)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);

    //
    // Set the voltage reference voltage as requested.
    //
    HWREG(ulBase + COMP_O_REFCTL) = ulRef;
}
#endif

//*****************************************************************************
//
//! Gets the current comparator output value.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator.
//!
//! This function retrieves the current value of the comparator output.
//!
//! \return Returns \b true if the comparator output is high and \b false if
//! the comparator output is low.
//
//*****************************************************************************
#if defined(GROUP_valueget) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
ComparatorValueGet(unsigned long ulBase, unsigned long ulComp)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Return the appropriate value based on the comparator's present output
    // value.
    //
    if(HWREG(ulBase + (ulComp * 0x20) + COMP_O_ACSTAT0) & COMP_ACSTAT_OVAL)
    {
        return(true);
    }
    else
    {
        return(false);
    }
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for the comparator interrupt.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator.
//! \param pfnHandler is a pointer to the function to be called when the
//! comparator interrupt occurs.
//!
//! This sets the handler to be called when the comparator interrupt occurs.
//! This will enable the interrupt in the interrupt controller; it is the
//! interrupt-handler's responsibility to clear the interrupt source via
//! ComparatorIntClear().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
ComparatorIntRegister(unsigned long ulBase, unsigned long ulComp,
                      void (*pfnHandler)(void))
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Register the interrupt handler, returning an error if an error occurs.
    //
    IntRegister(INT_COMP0 + ulComp, pfnHandler);

    //
    // Enable the interrupt in the interrupt controller.
    //
    IntEnable(INT_COMP0 + ulComp);

    //
    // Enable the comparator interrupt.
    //
    HWREG(ulBase + COMP_O_INTEN) |= 1 << ulComp;
}
#endif

//*****************************************************************************
//
//! Unregisters an interrupt handler for a comparator interrupt.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator.
//!
//! This function will clear the handler to be called when a comparator
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
ComparatorIntUnregister(unsigned long ulBase, unsigned long ulComp)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Disable the comparator interrupt.
    //
    HWREG(ulBase + COMP_O_INTEN) &= ~(1 << ulComp);

    //
    // Disable the interrupt in the interrupt controller.
    //
    IntDisable(INT_COMP0 + ulComp);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(INT_COMP0 + ulComp);
}
#endif

//*****************************************************************************
//
//! Enables the comparator interrupt.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator.
//!
//! This function enables generation of an interrupt from the specified
//! comparator.  Only comparators whose interrupts are enabled can be reflected
//! to the processor.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
ComparatorIntEnable(unsigned long ulBase, unsigned long ulComp)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Enable the comparator interrupt.
    //
    HWREG(ulBase + COMP_O_INTEN) |= 1 << ulComp;
}
#endif

//*****************************************************************************
//
//! Disables the comparator interrupt.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator.
//!
//! This function disables generation of an interrupt from the specified
//! comparator.  Only comparators whose interrupts are enabled can be reflected
//! to the processor.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
ComparatorIntDisable(unsigned long ulBase, unsigned long ulComp)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Disable the comparator interrupt.
    //
    HWREG(ulBase + COMP_O_INTEN) &= ~(1 << ulComp);
}
#endif

//*****************************************************************************
//
//! Gets the current interrupt status.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator.
//! \param bMasked is \b false if the raw interrupt status is required and
//! \b true if the masked interrupt status is required.
//!
//! This returns the interrupt status for the comparator.  Either the raw or
//! the masked interrupt status can be returned.
//!
//! \return \b true if the interrupt is asserted and \b false if it is not
//! asserted.
//
//*****************************************************************************
#if defined(GROUP_intstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
ComparatorIntStatus(unsigned long ulBase, unsigned long ulComp,
                    tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return(((HWREG(ulBase + COMP_O_MIS) >> ulComp) & 1) ? true : false);
    }
    else
    {
        return(((HWREG(ulBase + COMP_O_RIS) >> ulComp) & 1) ? true : false);
    }
}
#endif

//*****************************************************************************
//
//! Clears a comparator interrupt.
//!
//! \param ulBase is the base address of the comparator module.
//! \param ulComp is the index of the comparator.
//!
//! The comparator interrupt is cleared, so that it no longer asserts.  This
//! must be done in the interrupt handler to keep it from being called again
//! immediately upon exit.  Note that for a level triggered interrupt, the
//! interrupt cannot be cleared until it stops asserting.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
ComparatorIntClear(unsigned long ulBase, unsigned long ulComp)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == COMP_BASE);
    ASSERT(ulComp < 3);

    //
    // Clear the interrupt.
    //
    HWREG(ulBase + COMP_O_MIS) = 1 << ulComp;
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
