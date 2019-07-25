//*****************************************************************************
//
// ssi.c - Driver for Synchronous Serial Interface.
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
//! \addtogroup ssi_api
//! @{
//
//*****************************************************************************

#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_ssi.h"
#include "../hw_types.h"
#include "debug.h"
#include "interrupt.h"
#include "ssi.h"
#include "sysctl.h"

//*****************************************************************************
//
//! Configures the synchronous serial interface.
//!
//! \param ulBase specifies the SSI module base address.
//! \param ulProtocol specifies the data transfer protocol.
//! \param ulMode specifies the mode of operation.
//! \param ulBitRate specifies the clock rate.
//! \param ulDataWidth specifies number of bits transfered per frame.
//!
//! This function configures the synchronous serial interface. It sets
//! the SSI protocol, mode of operation, bit rate, and data width.
//!
//! The parameter \e ulProtocol defines the data frame format. The parameter
//! \e ulProtocol can be one of the following values: SSI_FRF_MOTO_MODE_0,
//! SSI_FRF_MOTO_MODE_1, SSI_FRF_MOTO_MODE_2, SSI_FRF_MOTO_MODE_3,
//! SSI_FRF_TI, or SSI_FRF_NMW. The Motorola frame formats imply the
//! following polarity and phase configurations:
//! <pre>
//! Polarity Phase       Mode
//!   0       0   SSI_FRF_MOTO_MODE_0
//!   0       1   SSI_FRF_MOTO_MODE_1
//!   1       0   SSI_FRF_MOTO_MODE_2
//!   1       1   SSI_FRF_MOTO_MODE_3
//! </pre>
//!
//! The parameter \e ulMode defines the operating mode of the SSI module. The
//! SSI module can operate as a master or slave; if a slave, the SSI can be
//! configured to disable output on its serial output line. The parameter
//! \e ulMode can be one of the following values: SSI_MODE_MASTER,
//! SSI_MODE_SLAVE, or SSI_MODE_SLAVE_OD.
//!
//! The parameter \e ulBitRate defines the bit rate for the SSI. This bit rate
//! must satisfy the following clock ratio criteria:
//! - FSSI >= 2 * bit rate (master mode)
//! - FSSI >= 12 * bit rate (slave modes)
//!
//! where FSSI is the frequency of the clock supplied to the SSI module.
//!
//! The parameter \e ulDataWidth defines the width of the data transfers.
//! The parameter \e ulDataWidth can be a value between 4 and 16, inclusive.
//!
//! The SSI clocking is dependent upon the system clock rate returned by
//! SysCtlClockGet(); if it does not return the correct system clock rate then
//! the SSI clock rate will be incorrect.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_config) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIConfig(unsigned long ulBase, unsigned long ulProtocol, unsigned long ulMode,
          unsigned long ulBitRate, unsigned long ulDataWidth)
{
    unsigned long ulMaxBitRate;
    unsigned long ulRegVal;
    unsigned long ulPreDiv;
    unsigned long ulSCR;
    unsigned long ulSPH_SPO;
    unsigned long ulClock;

    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);
    ASSERT((ulProtocol == SSI_FRF_MOTO_MODE_0) ||
           (ulProtocol == SSI_FRF_MOTO_MODE_1) ||
           (ulProtocol == SSI_FRF_MOTO_MODE_2) ||
           (ulProtocol == SSI_FRF_MOTO_MODE_3) ||
           (ulProtocol == SSI_FRF_TI) ||
           (ulProtocol == SSI_FRF_NMW));
    ASSERT((ulMode == SSI_MODE_MASTER) ||
           (ulMode == SSI_MODE_SLAVE) ||
           (ulMode == SSI_MODE_SLAVE_OD));
    ASSERT((ulDataWidth >= 4) && (ulDataWidth <= 16));

    //
    // Get the processor clock rate.
    //
    ulClock = SysCtlClockGet();

    //
    // Validate the clock speed.
    //
    ASSERT(((ulMode == SSI_MODE_MASTER) && (ulBitRate <= (ulClock / 2))) ||
           ((ulMode != SSI_MODE_MASTER) && (ulBitRate <= (ulClock / 12))));
    ASSERT((ulClock / ulBitRate) <= (254 * 256));

    //
    // Set the mode.
    //
    ulRegVal = (ulMode == SSI_MODE_SLAVE_OD) ? SSI_CR1_SOD : 0;
    ulRegVal |= (ulMode == SSI_MODE_MASTER) ? 0 : SSI_CR1_MS;
    HWREG(ulBase + SSI_O_CR1) = ulRegVal;

    //
    // Set the clock predivider.
    //
    ulMaxBitRate = ulClock / ulBitRate;
    ulPreDiv = 0;
    do
    {
        ulPreDiv += 2;
        ulSCR = (ulMaxBitRate / ulPreDiv) - 1;
    }
    while(ulSCR > 255);
    HWREG(ulBase + SSI_O_CPSR) = ulPreDiv;

    //
    // Set protocol and clock rate.
    //
    ulSPH_SPO = ulProtocol << 6;
    ulProtocol &= SSI_CR0_FRF_MASK;
    ulRegVal = (ulSCR << 8) | ulSPH_SPO | ulProtocol | (ulDataWidth - 1);
    HWREG(ulBase + SSI_O_CR0) = ulRegVal;
}
#endif

//*****************************************************************************
//
//! Enables the synchronous serial interface.
//!
//! \param ulBase specifies the SSI module base address.
//!
//! This will enable operation of the synchronous serial interface. It must be
//! configured before it is enabled.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_enable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Read-modify-write the enable bit.
    //
    HWREG(ulBase + SSI_O_CR1) |= SSI_CR1_SSE;
}
#endif

//*****************************************************************************
//
//! Disables the synchronous serial interface.
//!
//! \param ulBase specifies the SSI module base address.
//!
//! This will disable operation of the synchronous serial interface.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_disable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Read-modify-write the enable bit.
    //
    HWREG(ulBase + SSI_O_CR1) &= ~(SSI_CR1_SSE);
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for the synchronous serial interface.
//!
//! \param ulBase specifies the SSI module base address.
//! \param pfnHandler is a pointer to the function to be called when the
//! synchronous serial interface interrupt occurs.
//!
//! This sets the handler to be called when an SSI interrupt
//! occurs.  This will enable the global interrupt in the interrupt controller;
//! specific SSI interrupts must be enabled via SSIIntEnable().  If necessary,
//! it is the interrupt handler's responsibility to clear the interrupt source
//! via SSIIntClear().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIIntRegister(unsigned long ulBase, void (*pfnHandler)(void))
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Register the interrupt handler, returning an error if an error occurs.
    //
    IntRegister(INT_SSI, pfnHandler);

    //
    // Enable the synchronous serial interface interrupt.
    //
    IntEnable(INT_SSI);
}
#endif

//*****************************************************************************
//
//! Unregisters an interrupt handler for the synchronous serial interface.
//!
//! \param ulBase specifies the SSI module base address.
//!
//! This function will clear the handler to be called when a SSI
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
SSIIntUnregister(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Disable the interrupt.
    //
    IntDisable(INT_SSI);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(INT_SSI);
}
#endif

//*****************************************************************************
//
//! Enables individual SSI interrupt sources.
//!
//! \param ulBase specifies the SSI module base address.
//! \param ulIntFlags is a bit mask of the interrupt sources to be enabled.
//!
//! Enables the indicated SSI interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources
//! have no effect on the processor.  The parameter \e ulIntFlags Can be
//! any of the SSI_TXFF, SSI_RXFF, SSI_RXTO, or SSI_RXOR values.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIIntEnable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Enable the specified interrupts.
    //
    HWREG(ulBase + SSI_O_IM) |= ulIntFlags;
}
#endif

//*****************************************************************************
//
//! Disables individual SSI interrupt sources.
//!
//! \param ulBase specifies the SSI module base address.
//! \param ulIntFlags is a bit mask of the interrupt sources to be disabled.
//!
//! Disables the indicated SSI interrupt sources. The parameter
//! \e ulIntFlags Can be any of the SSI_TXFF, SSI_RXFF, SSI_RXTO,
//! or SSI_RXOR values.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIIntDisable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Disable the specified interrupts.
    //
    HWREG(ulBase + SSI_O_IM) &= ~(ulIntFlags);
}
#endif

//*****************************************************************************
//
//! Gets the current interrupt status.
//!
//! \param ulBase specifies the SSI module base address.
//! \param bMasked is false if the raw interrupt status is required and
//! true if the masked interrupt status is required.
//!
//! This returns the interrupt status for the SSI module.
//! Either the raw interrupt status or the status of interrupts that are
//! allowed to reflect to the processor can be returned.
//!
//! \return The current interrupt status, enumerated as a bit field of
//! SSI_TXFF, SSI_RXFF, SSI_RXTO, and SSI_RXOR.
//
//*****************************************************************************
#if defined(GROUP_intstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
SSIIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return(HWREG(ulBase + SSI_O_MIS));
    }
    else
    {
        return(HWREG(ulBase + SSI_O_RIS));
    }
}
#endif

//*****************************************************************************
//
//! Clears SSI interrupt sources.
//!
//! \param ulBase specifies the SSI module base address.
//! \param ulIntFlags is a bit mask of the interrupt sources to be cleared.
//!
//! The specified SSI interrupt sources are cleared, so that
//! they no longer assert.  This must be done in the interrupt handler to
//! keep it from being called again immediately upon exit.
//! The parameter \e ulIntFlags can consist of either or both the SSI_RXTO
//! and SSI_RXOR values.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIIntClear(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Clear the requested interrupt sources.
    //
    HWREG(ulBase + SSI_O_ICR) = ulIntFlags;
}
#endif

//*****************************************************************************
//
//! Puts a data element into the SSI transmit FIFO.
//!
//! \param ulBase specifies the SSI module base address.
//! \param ulData data to be transmitted over the SSI interface.
//!
//! This function will place the supplied data into the transmit FIFO of
//! the specified SSI module.
//!
//! \note The upper 32 - N bits of the \e ulData will be discarded by the
//! hardware, where N is the data width as configured by SSIConfig().  For
//! example, if the interface is configured for 8 bit data width, the upper 24
//! bits of \e ulData will be discarded.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_dataput) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIDataPut(unsigned long ulBase, unsigned long ulData)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);
    ASSERT((ulData & (0xfffffffe << (HWREG(ulBase + SSI_O_CR0) &
                                     SSI_CR0_DSS))) == 0);

    //
    // Wait until there is space.
    //
    while(!(HWREG(ulBase + SSI_O_SR) & SSI_SR_TNF))
    {
    }

    //
    // Write the data to the SSI.
    //
    HWREG(ulBase + SSI_O_DR) = ulData;
}
#endif

//*****************************************************************************
//
//! Puts a data element into the SSI transmit FIFO.
//!
//! \param ulBase specifies the SSI module base address.
//! \param ulData data to be transmitted over the SSI interface.
//!
//! This function will place the supplied data into the transmit FIFO of
//! the specified SSI module. If there is no space in the FIFO, then this
//! function will return a zero.
//!
//! \note The upper 32 - N bits of the \e ulData will be discarded by the
//! hardware, where N is the data width as configured by SSIConfig().  For
//! example, if the interface is configured for 8 bit data width, the upper 24
//! bits of \e ulData will be discarded.
//!
//! \return Returns the number of elements written to the SSI transmit FIFO.
//
//*****************************************************************************
#if defined(GROUP_datanonblockingput) || defined(BUILD_ALL) || defined(DOXYGEN)
long
SSIDataNonBlockingPut(unsigned long ulBase, unsigned long ulData)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);
    ASSERT((ulData & (0xfffffffe << (HWREG(ulBase + SSI_O_CR0) &
                                     SSI_CR0_DSS))) == 0);

    //
    // Check for space to write.
    //
    if(HWREG(ulBase + SSI_O_SR) & SSI_SR_TNF)
    {
        HWREG(ulBase + SSI_O_DR) = ulData;
        return(1);
    }
    else
    {
        return(0);
    }
}
#endif

//*****************************************************************************
//
//! Gets a data element from the SSI receive FIFO.
//!
//! \param ulBase specifies the SSI module base address.
//! \param pulData pointer to a storage location for data that was received
//! over the SSI interface.
//!
//! This function will get received data from the receive FIFO of the specified
//! SSI module, and place that data into the location specified by the
//! \e pulData parameter.
//!
//! \note Only the lower N bits of the value written to \e pulData will contain
//! valid data, where N is the data width as configured by SSIConfig().  For
//! example, if the interface is configured for 8 bit data width, only the
//! lower 8 bits of the value written to \e pulData will contain valid data.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_dataget) || defined(BUILD_ALL) || defined(DOXYGEN)
void
SSIDataGet(unsigned long ulBase, unsigned long *pulData)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Wait until there is data to be read.
    //
    while(!(HWREG(ulBase + SSI_O_SR) & SSI_SR_RNE))
    {
    }

    //
    // Read data from SSI.
    //
    *pulData = HWREG(ulBase + SSI_O_DR);
}
#endif

//*****************************************************************************
//
//! Gets a data element from the SSI receive FIFO.
//!
//! \param ulBase specifies the SSI module base address.
//! \param pulData pointer to a storage location for data that was received
//! over the SSI interface.
//!
//! This function will get received data from the receive FIFO of
//! the specified SSI module, and place that data into the location specified
//! by the \e ulData parameter. If there is no data in the FIFO, then this
//! function will return a zero.
//!
//! \note Only the lower N bits of the value written to \e pulData will contain
//! valid data, where N is the data width as configured by SSIConfig().  For
//! example, if the interface is configured for 8 bit data width, only the
//! lower 8 bits of the value written to \e pulData will contain valid data.
//!
//! \return Returns the number of elements read from the SSI receive FIFO.
//
//*****************************************************************************
#if defined(GROUP_datanonblockingget) || defined(BUILD_ALL) || defined(DOXYGEN)
long
SSIDataNonBlockingGet(unsigned long ulBase, unsigned long *pulData)
{ 
   //
    // Check the arguments.
    //
    ASSERT(ulBase == SSI_BASE);

    //
    // Check for data to read.
    //
    if(HWREG(ulBase + SSI_O_SR) & SSI_SR_RNE)
    {
        *pulData = HWREG(ulBase + SSI_O_DR);
        return(1);
    }
    else
    {
        return(0);
    }
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
