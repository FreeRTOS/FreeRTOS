//*****************************************************************************
//
// qei.c - Driver for the Quadrature Encoder with Index.
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
//! \addtogroup qei_api
//! @{
//
//*****************************************************************************

#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_qei.h"
#include "../hw_types.h"
#include "debug.h"
#include "interrupt.h"
#include "qei.h"

//*****************************************************************************
//
//! Enables the quadrature encoder.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This will enable operation of the quadrature encoder module.  It must be
//! configured before it is enabled.
//!
//! \sa QEIConfigure()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_enable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Enable the QEI module.
    //
    HWREG(ulBase + QEI_O_CTL) |= QEI_CTL_ENABLE;
}
#endif

//*****************************************************************************
//
//! Disables the quadrature encoder.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This will disable operation of the quadrature encoder module.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_disable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Disable the QEI module.
    //
    HWREG(ulBase + QEI_O_CTL) &= ~(QEI_CTL_ENABLE);
}
#endif

//*****************************************************************************
//
//! Configures the quadrature encoder.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param ulConfig is the configuration for the quadrature encoder.  See below
//! for a description of this parameter.
//! \param ulMaxPosition specifies the maximum position value.
//!
//! This will configure the operation of the quadrature encoder.  The
//! \e ulConfig parameter provides the configuration of the encoder and is the
//! logical OR of several values:
//!
//! - \b QEI_CONFIG_CAPTURE_A or \b QEI_CONFIG_CAPTURE_A_B to specify if edges
//!   on channel A or on both channels A and B should be counted by the
//!   position integrator and velocity accumulator.
//! - \b QEI_CONFIG_NO_RESET or \b QEI_CONFIG_RESET_IDX to specify if the
//!   position integrator should be reset when the index pulse is detected.
//! - \b QEI_CONFIG_QUADRATURE or \b QEI_CONFIG_CLOCK_DIR to specify if
//!   quadrature signals are being provided on ChA and ChB, or if a direction
//!   signal and a clock are being provided instead.
//! - \b QEI_CONFIG_NO_SWAP or \b QEI_CONFIG_SWAP to specify if the signals
//!   provided on ChA and ChB should be swapped before being processed.
//!
//! \e ulMaxPosition is the maximum value of the position integrator, and is
//! the value used to reset the position capture when in index reset mode and
//! moving in the reverse (negative) direction.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_configure) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIConfigure(unsigned long ulBase, unsigned long ulConfig,
             unsigned long ulMaxPosition)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Write the new configuration to the hardware.
    //
    HWREG(ulBase + QEI_O_CTL) = ((HWREG(ulBase + QEI_O_CTL) &
                                  ~(QEI_CTL_CAPMODE | QEI_CTL_RESMODE |
                                    QEI_CTL_SIGMODE | QEI_CTL_SWAP)) |
                                 ulConfig);

    //
    // Set the maximum position.
    //
    HWREG(ulBase + QEI_O_MAXPOS) = ulMaxPosition;
}
#endif

//*****************************************************************************
//
//! Gets the current encoder position.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This returns the current position of the encoder.  Depending upon the
//! configuration of the encoder, and the incident of an index pulse, this
//! value may or may not contain the expected data (i.e. if in reset on index
//! mode, if an index pulse has not been encountered, the position counter will
//! not be aligned with the index pulse yet).
//!
//! \return The current position of the encoder.
//
//*****************************************************************************
#if defined(GROUP_positionget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
QEIPositionGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Return the current position counter.
    //
    return(HWREG(ulBase + QEI_O_POS));
}
#endif

//*****************************************************************************
//
//! Sets the current encoder position.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param ulPosition is the new position for the encoder.
//!
//! This sets the current position of the encoder; the encoder position will
//! then be measured relative to this value.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_positionset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIPositionSet(unsigned long ulBase, unsigned long ulPosition)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Set the position counter.
    //
    HWREG(ulBase + QEI_O_POS) = ulPosition;
}
#endif

//*****************************************************************************
//
//! Gets the current direction of rotation.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This returns the current direction of rotation.  In this case, current
//! means the most recently detected direction of the encoder; it may not be
//! presently moving but this is the direction it last moved before it stopped.
//!
//! \return 1 if moving in the forward direction or -1 if moving in the reverse
//! direction.
//
//*****************************************************************************
#if defined(GROUP_directionget) || defined(BUILD_ALL) || defined(DOXYGEN)
long
QEIDirectionGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Return the direction of rotation.
    //
    return((HWREG(ulBase + QEI_O_STAT) & QEI_STAT_DIRECTION) ? -1 : 1);
}
#endif

//*****************************************************************************
//
//! Gets the encoder error indicator.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This returns the error indicator for the quadrature encoder.  It is an
//! error for both of the signals of the quadrature input to change at the same
//! time.
//!
//! \return true if an error has occurred and false otherwise.
//
//*****************************************************************************
#if defined(GROUP_errorget) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
QEIErrorGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Return the error indicator.
    //
    return((HWREG(ulBase + QEI_O_STAT) & QEI_STAT_ERROR) ? true : false);
}
#endif

//*****************************************************************************
//
//! Enables the velocity capture.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This will enable operation of the velocity capture in the quadrature
//! encoder module.  It must be configured before it is enabled.  Velocity
//! capture will not occur if the quadrature encoder is not enabled.
//!
//! \sa QEIVelocityConfigure() and QEIEnable()
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_velocityenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIVelocityEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Enable the velocity capture.
    //
    HWREG(ulBase + QEI_O_CTL) |= QEI_CTL_VELEN;
}
#endif

//*****************************************************************************
//
//! Disables the velocity capture.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This will disable operation of the velocity capture in the quadrature
//! encoder module.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_velocitydisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIVelocityDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Disable the velocity capture.
    //
    HWREG(ulBase + QEI_O_CTL) &= ~(QEI_CTL_VELEN);
}
#endif

//*****************************************************************************
//
//! Configures the velocity capture.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param ulPreDiv specifies the predivider applied to the input quadrature
//! signal before it is counted; can be one of QEI_VELDIV_1, QEI_VELDIV_2,
//! QEI_VELDIV_4, QEI_VELDIV_8, QEI_VELDIV_16, QEI_VELDIV_32, QEI_VELDIV_64, or
//! QEI_VELDIV_128.
//! \param ulPeriod specifies the number of clock ticks over which to measure
//! the velocity; must be non-zero.
//!
//! This will configure the operation of the velocity capture portion of the
//! quadrature encoder.  The position increment signal is predivided as
//! specified by \e ulPreDiv before being accumulated by the velocity capture.
//! The divided signal is accumulated over \e ulPeriod system clock before
//! being saved and resetting the accumulator.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_velocityconfigure) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIVelocityConfigure(unsigned long ulBase, unsigned long ulPreDiv,
                     unsigned long ulPeriod)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);
    ASSERT(!(ulPreDiv & ~(QEI_CTL_VELDIV_M)));
    ASSERT(ulPeriod != 0);

    //
    // Set the velocity predivider.
    //
    HWREG(ulBase + QEI_O_CTL) = ((HWREG(ulBase + QEI_O_CTL) &
                                  ~(QEI_CTL_VELDIV_M)) | ulPreDiv);

    //
    // Set the timer period.
    //
    HWREG(ulBase + QEI_O_LOAD) = ulPeriod - 1;
}
#endif

//*****************************************************************************
//
//! Gets the current encoder speed.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This returns the current speed of the encoder.  The value returned is the
//! number of pulses detected in the specified time period; this number can be
//! multiplied by the number of time periods per second and divided by the
//! number of pulses per revolution to obtain the number of revolutions per
//! second.
//!
//! \return The number of pulses captured in the given time period.
//
//*****************************************************************************
#if defined(GROUP_velocityget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
QEIVelocityGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Return the speed capture value.
    //
    return(HWREG(ulBase + QEI_O_SPEED));
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for the quadrature encoder interrupt.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param pfnHandler is a pointer to the function to be called when the
//! quadrature encoder interrupt occurs.
//!
//! This sets the handler to be called when a quadrature encoder interrupt
//! occurs.  This will enable the global interrupt in the interrupt controller;
//! specific quadrature encoder interrupts must be enabled via QEIIntEnable().
//! It is the interrupt handler's responsibility to clear the interrupt source
//! via QEIIntClear().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIIntRegister(unsigned long ulBase, void (*pfnHandler)(void))
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Register the interrupt handler, returning an error if an error occurs.
    //
    IntRegister(INT_QEI, pfnHandler);

    //
    // Enable the quadrature encoder interrupt.
    //
    IntEnable(INT_QEI);
}
#endif

//*****************************************************************************
//
//! Unregisters an interrupt handler for the quadrature encoder interrupt.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//!
//! This function will clear the handler to be called when a quadrature encoder
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
QEIIntUnregister(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Disable the interrupt.
    //
    IntDisable(INT_QEI);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(INT_QEI);
}
#endif

//*****************************************************************************
//
//! Enables individual quadrature encoder interrupt sources.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param ulIntFlags is a bit mask of the interrupt sources to be enabled.
//! Can be any of the QEI_INTERROR, QEI_INTDIR, QEI_INTTIMER, or QEI_INTINDEX
//! values.
//!
//! Enables the indicated quadrature encoder interrupt sources.  Only the
//! sources that are enabled can be reflected to the processor interrupt;
//! disabled sources have no effect on the processor.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIIntEnable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Enable the specified interrupts.
    //
    HWREG(ulBase + QEI_O_INTEN) |= ulIntFlags;
}
#endif

//*****************************************************************************
//
//! Disables individual quadrature encoder interrupt sources.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param ulIntFlags is a bit mask of the interrupt sources to be disabled.
//! Can be any of the QEI_INTERROR, QEI_INTDIR, QEI_INTTIMER, or QEI_INTINDEX
//! values.
//!
//! Disables the indicated quadrature encoder interrupt sources.  Only the
//! sources that are enabled can be reflected to the processor interrupt;
//! disabled sources have no effect on the processor.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIIntDisable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Disable the specified interrupts.
    //
    HWREG(ulBase + QEI_O_INTEN) &= ~(ulIntFlags);
}
#endif

//*****************************************************************************
//
//! Gets the current interrupt status.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param bMasked is false if the raw interrupt status is required and true if
//! the masked interrupt status is required.
//!
//! This returns the interrupt status for the quadrature encoder module.
//! Either the raw interrupt status or the status of interrupts that are
//! allowed to reflect to the processor can be returned.
//!
//! \return The current interrupt status, enumerated as a bit field of
//! QEI_INTERROR, QEI_INTDIR, QEI_INTTIMER, and QEI_INTINDEX.
//
//*****************************************************************************
#if defined(GROUP_intstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
QEIIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return(HWREG(ulBase + QEI_O_ISC));
    }
    else
    {
        return(HWREG(ulBase + QEI_O_RIS));
    }
}
#endif

//*****************************************************************************
//
//! Clears quadrature encoder interrupt sources.
//!
//! \param ulBase is the base address of the quadrature encoder module.
//! \param ulIntFlags is a bit mask of the interrupt sources to be cleared.
//! Can be any of the QEI_INTERROR, QEI_INTDIR, QEI_INTTIMER, or QEI_INTINDEX
//! values.
//!
//! The specified quadrature encoder interrupt sources are cleared, so that
//! they no longer assert.  This must be done in the interrupt handler to keep
//! it from being called again immediately upon exit.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
QEIIntClear(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == QEI_BASE);

    //
    // Clear the requested interrupt sources.
    //
    HWREG(ulBase + QEI_O_ISC) = ulIntFlags;
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
