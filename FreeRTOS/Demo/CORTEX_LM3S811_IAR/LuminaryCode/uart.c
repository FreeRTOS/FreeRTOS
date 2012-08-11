//*****************************************************************************
//
// uart.c - Driver for the UART.
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
//! \addtogroup uart_api
//! @{
//
//*****************************************************************************

#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_types.h"
#include "../hw_uart.h"
#include "debug.h"
#include "interrupt.h"
#include "sysctl.h"
#include "uart.h"

//*****************************************************************************
//
//! Sets the type of parity.
//!
//! \param ulBase is the base address of the UART port.
//! \param ulParity specifies the type of parity to use.
//!
//! Sets the type of parity to use for transmitting and expect when receiving.
//! The \e ulParity parameter must be one of \b UART_CONFIG_PAR_NONE,
//! \b UART_CONFIG_PAR_EVEN, \b UART_CONFIG_PAR_ODD, \b UART_CONFIG_PAR_ONE,
//! or \b UART_CONFIG_PAR_ZERO.  The last two allow direct control of the
//! parity bit; it will always be either be one or zero based on the mode.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_paritymodeset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTParityModeSet(unsigned long ulBase, unsigned long ulParity)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));
    ASSERT((ulParity == UART_CONFIG_PAR_NONE) ||
           (ulParity == UART_CONFIG_PAR_EVEN) ||
           (ulParity == UART_CONFIG_PAR_ODD) ||
           (ulParity == UART_CONFIG_PAR_ONE) ||
           (ulParity == UART_CONFIG_PAR_ZERO));

    //
    // Set the parity mode.
    //
    HWREG(ulBase + UART_O_LCR_H) = ((HWREG(ulBase + UART_O_LCR_H) &
                                     ~(UART_LCR_H_SPS | UART_LCR_H_EPS |
                                       UART_LCR_H_PEN)) | ulParity);
}
#endif

//*****************************************************************************
//
//! Gets the type of parity currently being used.
//!
//! \param ulBase is the base address of the UART port.
//!
//! \return The current parity settings, specified as one of
//! \b UART_CONFIG_PAR_NONE, \b UART_CONFIG_PAR_EVEN, \b UART_CONFIG_PAR_ODD,
//! \b UART_CONFIG_PAR_ONE, or \b UART_CONFIG_PAR_ZERO.
//
//*****************************************************************************
#if defined(GROUP_paritymodeget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
UARTParityModeGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Return the current parity setting.
    //
    return(HWREG(ulBase + UART_O_LCR_H) &
           (UART_LCR_H_SPS | UART_LCR_H_EPS | UART_LCR_H_PEN));
}
#endif

//*****************************************************************************
//
//! Sets the configuration of a UART.
//!
//! \param ulBase is the base address of the UART port.
//! \param ulBaud is the desired baud rate.
//! \param ulConfig is the data format for the port (number of data bits,
//! number of stop bits, and parity).
//!
//! This function will configure the UART for operation in the specified data
//! format.  The baud rate is provided in the \e ulBaud parameter and the
//! data format in the \e ulConfig parameter.
//!
//! The \e ulConfig parameter is the logical OR of three values: the number of
//! data bits, the number of stop bits, and the parity.  \b UART_CONFIG_WLEN_8,
//! \b UART_CONFIG_WLEN_7, \b UART_CONFIG_WLEN_6, and \b UART_CONFIG_WLEN_5
//! select from eight to five data bits per byte (respectively).
//! \b UART_CONFIG_STOP_ONE and \b UART_CONFIG_STOP_TWO select one or two stop
//! bits (respectively).  \b UART_CONFIG_PAR_NONE, \b UART_CONFIG_PAR_EVEN,
//! \b UART_CONFIG_PAR_ODD, \b UART_CONFIG_PAR_ONE, and \b UART_CONFIG_PAR_ZERO
//! select the parity mode (no parity bit, even parity bit, odd parity bit,
//! parity bit always one, and parity bit always zero, respectively).
//!
//! The baud rate is dependent upon the system clock rate returned by
//! SysCtlClockGet(); if it does not return the correct system clock rate then
//! the baud rate will be incorrect.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_configset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTConfigSet(unsigned long ulBase, unsigned long ulBaud,
              unsigned long ulConfig)
{
    unsigned long ulUARTClk, ulInt, ulFrac;

    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Stop the UART.
    //
    UARTDisable(ulBase);

    //
    // Determine the UART clock rate.
    //
    ulUARTClk = SysCtlClockGet();

    //
    // Compute the fractional baud rate divider.
    //
    ulInt = ulUARTClk / (16 * ulBaud);
    ulFrac = ulUARTClk % (16 * ulBaud);
    ulFrac = ((((2 * ulFrac * 4) / ulBaud) + 1) / 2);

    //
    // Set the baud rate.
    //
    HWREG(ulBase + UART_O_IBRD) = ulInt;
    HWREG(ulBase + UART_O_FBRD) = ulFrac;

    //
    // Set parity, data length, and number of stop bits.
    //
    HWREG(ulBase + UART_O_LCR_H) = ulConfig;

    //
    // Clear the flags register.
    //
    HWREG(ulBase + UART_O_FR) = 0;

    //
    // Start the UART.
    //
    UARTEnable(ulBase);
}
#endif

//*****************************************************************************
//
//! Gets the current configuration of a UART.
//!
//! \param ulBase is the base address of the UART port.
//! \param pulBaud is a pointer to storage for the baud rate.
//! \param pulConfig is a pointer to storage for the data format.
//!
//! The baud rate and data format for the UART is determined.  The returned
//! baud rate is the actual baud rate; it may not be the exact baud rate
//! requested or an ``official'' baud rate.  The data format returned in
//! \e pulConfig is enumerated the same as the \e ulConfig parameter of
//! UARTConfigSet().
//!
//! The baud rate is dependent upon the system clock rate returned by
//! SysCtlClockGet(); if it does not return the correct system clock rate then
//! the baud rate will be computed incorrectly.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_configget) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTConfigGet(unsigned long ulBase, unsigned long *pulBaud,
              unsigned long *pulConfig)

{
    unsigned long ulInt, ulFrac;

    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Compute the baud rate.
    //
    ulInt = HWREG(ulBase + UART_O_IBRD);
    ulFrac = HWREG(ulBase + UART_O_FBRD);
    *pulBaud = (SysCtlClockGet() * 4) / ((64 * ulInt) + ulFrac);

    //
    // Get the parity, data length, and number of stop bits.
    //
    *pulConfig = (HWREG(ulBase + UART_O_LCR_H) &
                  (UART_LCR_H_SPS | UART_LCR_H_WLEN | UART_LCR_H_STP2 |
                   UART_LCR_H_EPS | UART_LCR_H_PEN));
}
#endif

//*****************************************************************************
//
//! Enables transmitting and receiving.
//!
//! \param ulBase is the base address of the UART port.
//!
//! Sets the UARTEN, TXE, and RXE bits, and enables the transmit and receive
//! FIFOs.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_enable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Enable the FIFO.
    //
    HWREG(ulBase + UART_O_LCR_H) |= UART_LCR_H_FEN;

    //
    // Enable RX, TX, and the UART.
    //
    HWREG(ulBase + UART_O_CTL) |= (UART_CTL_UARTEN | UART_CTL_TXE |
                                   UART_CTL_RXE);
}
#endif

//*****************************************************************************
//
//! Disables transmitting and receiving.
//!
//! \param ulBase is the base address of the UART port.
//!
//! Clears the UARTEN, TXE, and RXE bits, then waits for the end of
//! transmission of the current character, and flushes the transmit FIFO.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_disable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Wait for end of TX.
    //
    while(HWREG(ulBase + UART_O_FR) & UART_FR_BUSY)
    {
    }

    //
    // Disable the FIFO.
    //
    HWREG(ulBase + UART_O_LCR_H) &= ~(UART_LCR_H_FEN);

    //
    // Disable the UART.
    //
    HWREG(ulBase + UART_O_CTL) &= ~(UART_CTL_UARTEN | UART_CTL_TXE |
                                    UART_CTL_RXE);
}
#endif

//*****************************************************************************
//
//! Determines if there are any characters in the receive FIFO.
//!
//! \param ulBase is the base address of the UART port.
//!
//! This function returns a flag indicating whether or not there is data
//! available in the receive FIFO.
//!
//! \return Returns \b true if there is data in the receive FIFO, and \b false
//! if there is no data in the receive FIFO.
//
//*****************************************************************************
#if defined(GROUP_charsavail) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
UARTCharsAvail(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Return the availability of characters.
    //
    return((HWREG(ulBase + UART_O_FR) & UART_FR_RXFE) ? false : true);
}
#endif

//*****************************************************************************
//
//! Determines if there is any space in the transmit FIFO.
//!
//! \param ulBase is the base address of the UART port.
//!
//! This function returns a flag indicating whether or not there is space
//! available in the transmit FIFO.
//!
//! \return Returns \b true if there is space available in the transmit FIFO,
//! and \b false if there is no space available in the transmit FIFO.
//
//*****************************************************************************
#if defined(GROUP_spaceavail) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
UARTSpaceAvail(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Return the availability of space.
    //
    return((HWREG(ulBase + UART_O_FR) & UART_FR_TXFF) ? false : true);
}
#endif

//*****************************************************************************
//
//! Receives a character from the specified port.
//!
//! \param ulBase is the base address of the UART port.
//!
//! Gets a character from the receive FIFO for the specified port.
//!
//! \return Returns the character read from the specified port, cast as a
//! \e long.  A \b -1 will be returned if there are no characters present in
//! the receive FIFO.  The UARTCharsAvail() function should be called before
//! attempting to call this function.
//
//*****************************************************************************
#if defined(GROUP_charnonblockingget) || defined(BUILD_ALL) || defined(DOXYGEN)
long
UARTCharNonBlockingGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // See if there are any characters in the receive FIFO.
    //
    if(!(HWREG(ulBase + UART_O_FR) & UART_FR_RXFE))
    {
        //
        // Read and return the next character.
        //
        return(HWREG(ulBase + UART_O_DR));
    }
    else
    {
        //
        // There are no characters, so return a failure.
        //
        return(-1);
    }
}
#endif

//*****************************************************************************
//
//! Waits for a character from the specified port.
//!
//! \param ulBase is the base address of the UART port.
//!
//! Gets a character from the receive FIFO for the specified port.  If there
//! are no characters available, this function will wait until a character is
//! received before returning.
//!
//! \return Returns the character read from the specified port, cast as an
//! \e int.
//
//*****************************************************************************
#if defined(GROUP_charget) || defined(BUILD_ALL) || defined(DOXYGEN)
long
UARTCharGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Wait until a char is available.
    //
    while(HWREG(ulBase + UART_O_FR) & UART_FR_RXFE)
    {
    }

    //
    // Now get the char.
    //
    return(HWREG(ulBase + UART_O_DR));
}
#endif

//*****************************************************************************
//
//! Sends a character to the specified port.
//!
//! \param ulBase is the base address of the UART port.
//! \param ucData is the character to be transmitted.
//!
//! Writes the character \e ucData to the transmit FIFO for the specified port.
//! This function does not block, so if there is no space available, then a
//! \b false is returned, and the application will have to retry the function
//! later.
//!
//! \return Returns \b true if the character was successfully placed in the
//! transmit FIFO, and \b false if there was no space available in the transmit
//! FIFO.
//
//*****************************************************************************
#if defined(GROUP_charnonblockingput) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
UARTCharNonBlockingPut(unsigned long ulBase, unsigned char ucData)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // See if there is space in the transmit FIFO.
    //
    if(!(HWREG(ulBase + UART_O_FR) & UART_FR_TXFF))
    {
        //
        // Write this character to the transmit FIFO.
        //
        HWREG(ulBase + UART_O_DR) = ucData;

        //
        // Success.
        //
        return(true);
    }
    else
    {
        //
        // There is no space in the transmit FIFO, so return a failure.
        //
        return(false);
    }
}
#endif

//*****************************************************************************
//
//! Waits to send a character from the specified port.
//!
//! \param ulBase is the base address of the UART port.
//! \param ucData is the character to be transmitted.
//!
//! Sends the character \e ucData to the transmit FIFO for the specified port.
//! If there is no space available in the transmit FIFO, this function will
//! wait until there is space available before returning.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_charput) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTCharPut(unsigned long ulBase, unsigned char ucData)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Wait until space is available.
    //
    while(HWREG(ulBase + UART_O_FR) & UART_FR_TXFF)
    {
    }

    //
    // Send the char.
    //
    HWREG(ulBase + UART_O_DR) = ucData;
}
#endif

//*****************************************************************************
//
//! Causes a BREAK to be sent.
//!
//! \param ulBase is the base address of the UART port.
//! \param bBreakState controls the output level.
//!
//! Calling this function with \e bBreakState set to \b true will assert a
//! break condition on the UART.  Calling this function with \e bBreakState set
//! to \b false will remove the break condition.  For proper transmission of a
//! break command, the break must be asserted for at least two complete frames.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_breakctl) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTBreakCtl(unsigned long ulBase, tBoolean bBreakState)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Set the break condition as requested.
    //
    HWREG(ulBase + UART_O_LCR_H) =
        (bBreakState ?
         (HWREG(ulBase + UART_O_LCR_H) | UART_LCR_H_BRK) :
         (HWREG(ulBase + UART_O_LCR_H) & ~(UART_LCR_H_BRK)));
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for a UART interrupt.
//!
//! \param ulBase is the base address of the UART port.
//! \param pfnHandler is a pointer to the function to be called when the
//! UART interrupt occurs.
//!
//! This function does the actual registering of the interrupt handler.  This
//! will enable the global interrupt in the interrupt controller; specific UART
//! interrupts must be enabled via UARTIntEnable().  It is the interrupt
//! handler's responsibility to clear the interrupt source.
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTIntRegister(unsigned long ulBase, void (*pfnHandler)(void))
{
    unsigned long ulInt;

    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Determine the interrupt number based on the UART port.
    //
    ulInt = (ulBase == UART0_BASE) ? INT_UART0 : INT_UART1;

    //
    // Register the interrupt handler.
    //
    IntRegister(ulInt, pfnHandler);

    //
    // Enable the UART interrupt.
    //
    IntEnable(ulInt);
}
#endif

//*****************************************************************************
//
//! Unregisters an interrupt handler for a UART interrupt.
//!
//! \param ulBase is the base address of the UART port.
//!
//! This function does the actual unregistering of the interrupt handler.  It
//! will clear the handler to be called when a UART interrupt occurs.  This
//! will also mask off the interrupt in the interrupt controller so that the
//! interrupt handler no longer is called.
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intunregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTIntUnregister(unsigned long ulBase)
{
    unsigned long ulInt;

    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Determine the interrupt number based on the UART port.
    //
    ulInt = (ulBase == UART0_BASE) ? INT_UART0 : INT_UART1;

    //
    // Disable the interrupt.
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
//! Enables individual UART interrupt sources.
//!
//! \param ulBase is the base address of the UART port.
//! \param ulIntFlags is the bit mask of the interrupt sources to be enabled.
//!
//! Enables the indicated UART interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! The parameter \e ulIntFlags is the logical OR of any of the following:
//!
//! - UART_INT_OE - Overrun Error interrupt
//! - UART_INT_BE - Break Error interrupt
//! - UART_INT_PE - Parity Error interrupt
//! - UART_INT_FE - Framing Error interrupt
//! - UART_INT_RT - Receive Timeout interrupt
//! - UART_INT_TX - Transmit interrupt
//! - UART_INT_RX - Receive interrupt
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTIntEnable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Enable the specified interrupts.
    //
    HWREG(ulBase + UART_O_IM) |= ulIntFlags;
}
#endif

//*****************************************************************************
//
//! Disables individual UART interrupt sources.
//!
//! \param ulBase is the base address of the UART port.
//! \param ulIntFlags is the bit mask of the interrupt sources to be disabled.
//!
//! Disables the indicated UART interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! The parameter \e ulIntFlags has the same definition as the same parameter
//! to UARTIntEnable().
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTIntDisable(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Disable the specified interrupts.
    //
    HWREG(ulBase + UART_O_IM) &= ~(ulIntFlags);
}
#endif

//*****************************************************************************
//
//! Gets the current interrupt status.
//!
//! \param ulBase is the base address of the UART port.
//! \param bMasked is false if the raw interrupt status is required and true
//! if the masked interrupt status is required.
//!
//! This returns the interrupt status for the specified UART.  Either the raw
//! interrupt status or the status of interrupts that are allowed to reflect to
//! the processor can be returned.
//!
//! \return The current interrupt status, enumerated as a bit field of
//! values described in UARTIntEnable().
//
//*****************************************************************************
#if defined(GROUP_intstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
UARTIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return(HWREG(ulBase + UART_O_MIS));
    }
    else
    {
        return(HWREG(ulBase + UART_O_RIS));
    }
}
#endif

//*****************************************************************************
//
//! Clears UART interrupt sources.
//!
//! \param ulBase is the base address of the UART port.
//! \param ulIntFlags is a bit mask of the interrupt sources to be cleared.
//!
//! The specified UART interrupt sources are cleared, so that they no longer
//! assert.  This must be done in the interrupt handler to keep it from being
//! called again immediately upon exit.
//!
//! The parameter \e ulIntFlags has the same definition as the same parameter
//! to UARTIntEnable().
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
UARTIntClear(unsigned long ulBase, unsigned long ulIntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ulBase == UART0_BASE) || (ulBase == UART1_BASE));

    //
    // Clear the requested interrupt sources.
    //
    HWREG(ulBase + UART_O_ICR) = ulIntFlags;
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
