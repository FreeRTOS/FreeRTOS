//*****************************************************************************
//
// i2c.c - Driver for Inter-IC (I2C) bus block.
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
//! \addtogroup i2c_api
//! @{
//
//*****************************************************************************

#include "../hw_i2c.h"
#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_types.h"
#include "debug.h"
#include "i2c.h"
#include "interrupt.h"
#include "sysctl.h"

//*****************************************************************************
//
//! Initializes the I2C Master block.
//!
//! \param ulBase base address of the I2C Master module
//! \param bFast set up for fast data transfers
//!
//! This function initializes operation of the I2C Master block. Upon
//! successful initialization of the I2C block, this function will have
//! set the bus speed for the master, and will have enabled the I2C Master
//! block.
//!
//! If the parameter \e bFast is \b true, then the master block will be
//! set up to transfer data at 400 kbps; otherwise, it will be set up to
//! transfer data at 100 kbps.
//!
//! The I2C clocking is dependent upon the system clock rate returned by
//! SysCtlClockGet(); if it does not return the correct system clock rate then
//! the I2C clock rate will be incorrect.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterinit) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterInit(unsigned long ulBase, tBoolean bFast)
{
    unsigned long ulSysClk;
    unsigned long ulSCLFreq;
    unsigned long ulTPR;

    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Must enable the device before doing anything else.
    //
    I2CMasterEnable(ulBase);

    //
    // Get the system clock speed.
    //
    ulSysClk = SysCtlClockGet();

    //
    // Get the desired SCL speed.
    //
    if(bFast == true)
    {
        ulSCLFreq = I2C_SCL_FAST;
    }
    else
    {
        ulSCLFreq = I2C_SCL_STANDARD;
    }

    //
    // Compute the clock divider that achieves the fastest speed less than or
    // equal to the desired speed.  The numerator is biases to favor a larger
    // clock divider so that the resulting clock is always less than or equal
    // to the desired clock, never greater.
    //
    ulTPR = (((ulSysClk + (2 * I2C_MASTER_TPR_SCL * ulSCLFreq) - 1) /
              (2 * I2C_MASTER_TPR_SCL * ulSCLFreq)) - 1);
    HWREG(ulBase + I2C_MASTER_O_TPR) = ulTPR;
}
#endif

//*****************************************************************************
//
//! Initializes the I2C Slave block.
//!
//! \param ulBase base address of the I2C Slave module
//! \param ucSlaveAddr 7-bit slave address
//!
//! This function initializes operation of the I2C Slave block. Upon
//! successful initialization of the I2C blocks, this function will have
//! set the slave address and have enabled the I2C Slave block.
//!
//! The parameter \e ucSlaveAddr is the value that will be compared
//! against the slave address sent by an I2C master.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slaveinit) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CSlaveInit(unsigned long ulBase, unsigned char ucSlaveAddr)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);
    ASSERT(!(ucSlaveAddr & 0x80));

    //
    // Must enable the device before doing anything else.
    //
    I2CSlaveEnable(ulBase);

    //
    // Set up the slave address.
    //
    HWREG(ulBase + I2C_SLAVE_O_OAR) = ucSlaveAddr;
}
#endif

//*****************************************************************************
//
//! Enables the I2C Master block.
//!
//! \param ulBase base address of the I2C Master module
//!
//! This will enable operation of the I2C Master block.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Enable the master block.
    //
    HWREG(ulBase + I2C_MASTER_O_CR) |= I2C_MASTER_CR_MFE;
}
#endif

//*****************************************************************************
//
//! Enables the I2C Slave block.
//!
//! \param ulBase base address of the I2C Slave module
//!
//! This will enable operation of the I2C Slave block.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slaveenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CSlaveEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Enable the clock to the slave block.
    //
    HWREG(ulBase - I2C_O_SLAVE + I2C_MASTER_O_CR) |= I2C_MASTER_CR_SFE;

    //
    // Enable the slave.
    //
    HWREG(ulBase + I2C_SLAVE_O_CSR) = I2C_SLAVE_CSR_DA;
}
#endif

//*****************************************************************************
//
//! Disables the I2C master block.
//!
//! \param ulBase base address of the I2C Master module
//!
//! This will disable operation of the I2C master block.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Disable the master block.
    //
    HWREG(ulBase + I2C_MASTER_O_CR) &= ~(I2C_MASTER_CR_MFE);
}
#endif

//*****************************************************************************
//
//! Disables the I2C slave block.
//!
//! \param ulBase base address of the I2C Slave module
//!
//! This will disable operation of the I2C slave block.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slavedisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CSlaveDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Disable the slave.
    //
    HWREG(ulBase + I2C_SLAVE_O_CSR) = 0;

    //
    // Disable the clock to the slave block.
    //
    HWREG(ulBase - I2C_O_SLAVE + I2C_MASTER_O_CR) &= ~(I2C_MASTER_CR_SFE);
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for the I2C module
//!
//! \param ulBase base address of the I2C module
//! \param pfnHandler is a pointer to the function to be called when the
//! synchronous serial interface interrupt occurs.
//!
//! This sets the handler to be called when an I2C interrupt occurs.  This
//! will enable the global interrupt in the interrupt controller; specific I2C
//! interrupts must be enabled via I2CMasterIntEnable() and
//! I2CSlaveIntEnable().  If necessary, it is the interrupt handler's
//! responsibility to clear the interrupt source via I2CMasterIntClear() and
//! I2CSlaveIntClear().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CIntRegister(unsigned long ulBase, void (*pfnHandler)(void))
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Register the interrupt handler, returning an error if an error occurs.
    //
    IntRegister(INT_I2C, pfnHandler);

    //
    // Enable the I2C interrupt.
    //
    IntEnable(INT_I2C);
}
#endif

//*****************************************************************************
//
//! Unregisters an interrupt handler for the I2C module.
//!
//! \param ulBase base address of the I2C module
//!
//! This function will clear the handler to be called when an I2C
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
I2CIntUnregister(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Disable the interrupt.
    //
    IntDisable(INT_I2C);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(INT_I2C);
}
#endif

//*****************************************************************************
//
//! Enables the I2C Master interrupt.
//!
//! \param ulBase base address of the I2C Master module
//!
//! Enables the I2C Master interrupt source.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterintenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterIntEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Enable the master interrupt.
    //
    HWREG(ulBase + I2C_MASTER_O_IMR) = 1;
}
#endif

//*****************************************************************************
//
//! Enables the I2C Slave interrupt.
//!
//! \param ulBase base address of the I2C Slave module
//!
//! Enables the I2C Slave interrupt source.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slaveintenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CSlaveIntEnable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Enable the slave interrupt.
    //
    HWREG(ulBase + I2C_SLAVE_O_IM) = 1;
}
#endif

//*****************************************************************************
//
//! Disables the I2C Master interrupt.
//!
//! \param ulBase base address of the I2C Master module
//!
//! Disables the I2C Master interrupt source.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterintdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterIntDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Disable the master interrupt.
    //
    HWREG(ulBase + I2C_MASTER_O_IMR) = 0;
}
#endif

//*****************************************************************************
//
//! Disables the I2C Slave interrupt.
//!
//! \param ulBase base address of the I2C Slave module
//!
//! Disables the I2C Slave interrupt source.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slaveintdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CSlaveIntDisable(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Disable the slave interrupt.
    //
    HWREG(ulBase + I2C_SLAVE_O_IM) = 0;
}
#endif

//*****************************************************************************
//
//! Gets the current I2C Master interrupt status.
//!
//! \param ulBase base address of the I2C Master module
//! \param bMasked is false if the raw interrupt status is requested and
//! true if the masked interrupt status is requested.
//!
//! This returns the interrupt status for the I2C Master module.
//! Either the raw interrupt status or the status of interrupts that are
//! allowed to reflect to the processor can be returned.
//!
//! \return The current interrupt status, returned as \b true if active
//! or \b false if not active.
//
//*****************************************************************************
#if defined(GROUP_masterintstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
I2CMasterIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return((HWREG(ulBase + I2C_MASTER_O_MIS)) ? true : false);
    }
    else
    {
        return((HWREG(ulBase + I2C_MASTER_O_RIS)) ? true : false);
    }
}
#endif

//*****************************************************************************
//
//! Gets the current I2C Slave interrupt status.
//!
//! \param ulBase base address of the I2C Slave module
//! \param bMasked is false if the raw interrupt status is requested and
//! true if the masked interrupt status is requested.
//!
//! This returns the interrupt status for the I2C Slave module.
//! Either the raw interrupt status or the status of interrupts that are
//! allowed to reflect to the processor can be returned.
//!
//! \return The current interrupt status, returned as \b true if active
//! or \b false if not active.
//
//*****************************************************************************
#if defined(GROUP_slaveintstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
I2CSlaveIntStatus(unsigned long ulBase, tBoolean bMasked)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return((HWREG(ulBase + I2C_SLAVE_O_MIS)) ? true : false);
    }
    else
    {
        return((HWREG(ulBase + I2C_SLAVE_O_RIS)) ? true : false);
    }
}
#endif

//*****************************************************************************
//
//! Clears I2C Master interrupt sources.
//!
//! \param ulBase base address of the I2C Master module
//!
//! The I2C Master interrupt source is cleared, so that it no longer asserts.
//! This must be done in the interrupt handler to keep it from being called
//! again immediately upon exit.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterintclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterIntClear(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Clear the I2C master interrupt source.
    //
    HWREG(ulBase + I2C_MASTER_O_MICR) = I2C_MASTER_MICR_IC;

    //
    // Workaround for I2C master interrupt clear errata for rev B Stellaris
    // devices.  For later devices, this write is ignored and therefore
    // harmless (other than the slight performance hit).
    //
    HWREG(ulBase + I2C_MASTER_O_MIS) = I2C_MASTER_MICR_IC;
}
#endif

//*****************************************************************************
//
//! Clears I2C Slave interrupt sources.
//!
//! \param ulBase base address of the I2C Slave module
//!
//! The I2C Slave interrupt source is cleared, so that it no longer asserts.
//! This must be done in the interrupt handler to keep it from being called
//! again immediately upon exit.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slaveintclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CSlaveIntClear(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Clear the I2C slave interrupt source.
    //
    HWREG(ulBase + I2C_SLAVE_O_SICR) = I2C_SLAVE_SICR_IC;
}
#endif

//*****************************************************************************
//
//! Sets the address that the I2C Master will place on the bus.
//!
//! \param ulBase base address of the I2C Master module
//! \param ucSlaveAddr 7-bit slave address
//! \param bReceive flag indicating the type of communication with the slave
//!
//! This function will set the address that the I2C Master will place on the
//! bus when initiating a transaction. When the parameter \e bReceive is set
//! to \b true, the address will indicate that the I2C Master is initiating
//! a read from the slave; otherwise the address will indicate that the I2C
//! Master is initiating a write to the slave.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterslaveaddrset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterSlaveAddrSet(unsigned long ulBase, unsigned char ucSlaveAddr,
                      tBoolean bReceive)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);
    ASSERT(!(ucSlaveAddr & 0x80));

    //
    // Set the address of the slave with which the master will communicate.
    //
    HWREG(ulBase + I2C_MASTER_O_SA) = (ucSlaveAddr << 1) | bReceive;
}
#endif

//*****************************************************************************
//
//! Indicates whether or not the I2C Master is busy.
//!
//! \param ulBase base address of the I2C Master module
//!
//! This function returns an indication of whether or not the I2C Master is
//! busy transmitting or receiving data.
//!
//! \return Returns \b true if the I2C Master is busy; otherwise, returns
//! \b false.
//
//*****************************************************************************
#if defined(GROUP_masterbusy) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
I2CMasterBusy(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Return the busy status.
    //
    if(HWREG(ulBase + I2C_MASTER_O_CS) & I2C_MASTER_CS_BUSY)
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
//! Indicates whether or not the I2C bus is busy.
//!
//! \param ulBase base address of the I2C Master module
//!
//! This function returns an indication of whether or not the I2C bus is
//! busy. This function can be used in a multi-master environment to
//! determine if another master is currently using the bus.
//!
//! \return Returns \b true if the I2C bus is busy; otherwise, returns
//! \b false.
//
//*****************************************************************************
#if defined(GROUP_masterbusbusy) || defined(BUILD_ALL) || defined(DOXYGEN)
tBoolean
I2CMasterBusBusy(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Return the bus busy status.
    //
    if(HWREG(ulBase + I2C_MASTER_O_CS) & I2C_MASTER_CS_BUS_BUSY)
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
//! Controls the state of the I2C Master module.
//!
//! \param ulBase base address of the I2C Master module
//! \param ulCmd command to be issued to the I2C Master module
//!
//! This function is used to control the state of the Master module send and
//! receive operations. The parameter \e ucCmd can be one of the following
//! values:
//!
//! - I2C_MASTER_CMD_SINGLE_SEND
//! - I2C_MASTER_CMD_SINGLE_RECEIVE
//! - I2C_MASTER_CMD_BURST_SEND_START
//! - I2C_MASTER_CMD_BURST_SEND_CONT
//! - I2C_MASTER_CMD_BURST_SEND_FINISH
//! - I2C_MASTER_CMD_BURST_SEND_ERROR_STOP
//! - I2C_MASTER_CMD_BURST_RECEIVE_START
//! - I2C_MASTER_CMD_BURST_RECEIVE_CONT
//! - I2C_MASTER_CMD_BURST_RECEIVE_FINISH
//! - I2C_MASTER_CMD_BURST_RECEIVE_ERROR_STOP
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_mastercontrol) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterControl(unsigned long ulBase, unsigned long ulCmd)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);
    ASSERT((ulCmd == I2C_MASTER_CMD_SINGLE_SEND) ||
           (ulCmd == I2C_MASTER_CMD_SINGLE_RECEIVE) ||
           (ulCmd == I2C_MASTER_CMD_BURST_SEND_START) ||
           (ulCmd == I2C_MASTER_CMD_BURST_SEND_CONT) ||
           (ulCmd == I2C_MASTER_CMD_BURST_SEND_FINISH) ||
           (ulCmd == I2C_MASTER_CMD_BURST_SEND_ERROR_STOP) ||
           (ulCmd == I2C_MASTER_CMD_BURST_RECEIVE_START) ||
           (ulCmd == I2C_MASTER_CMD_BURST_RECEIVE_CONT) ||
           (ulCmd == I2C_MASTER_CMD_BURST_RECEIVE_FINISH) ||
           (ulCmd == I2C_MASTER_CMD_BURST_RECEIVE_ERROR_STOP));

    //
    // Send the command.
    //
    HWREG(ulBase + I2C_MASTER_O_CS) = ulCmd;
}
#endif

//*****************************************************************************
//
//! Gets the error status of the I2C Master module.
//!
//! \param ulBase base address of the I2C Master module
//!
//! This function is used to obtain the error status of the Master module
//! send and receive operations. It returns one of the following values:
//!
//! - I2C_MASTER_ERR_NONE
//! - I2C_MASTER_ERR_ADDR_ACK
//! - I2C_MASTER_ERR_DATA_ACK
//! - I2C_MASTER_ERR_ARB_LOST
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_mastererr) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
I2CMasterErr(unsigned long ulBase)
{
    unsigned long ulErr;

    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Get the raw error state
    //
    ulErr = HWREG(ulBase + I2C_MASTER_O_CS);

    //
    // If the I2C master is busy, then all the other bit are invalid, and
    // don't have an error to report.
    //
    if(ulErr & I2C_MASTER_CS_BUSY)
    {
        return(I2C_MASTER_ERR_NONE);
    }

    //
    // Check for errors.
    //
    if(ulErr & I2C_MASTER_CS_ERROR)
    {
        return(ulErr & (I2C_MASTER_CS_ERR_MASK));
    }
    else
    {
        return(I2C_MASTER_ERR_NONE);
    }
}
#endif

//*****************************************************************************
//
//! Transmits a byte from the I2C Master.
//!
//! \param ulBase base address of the I2C Master module
//! \param ucData data to be transmitted from the I2C Master
//!
//! This function will place the supplied data into I2C Master Data Register.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_masterdataput) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CMasterDataPut(unsigned long ulBase, unsigned char ucData)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Write the byte.
    //
    HWREG(ulBase + I2C_MASTER_O_DR) = ucData;
}
#endif

//*****************************************************************************
//
//! Receives a byte that has been sent to the I2C Master.
//!
//! \param ulBase base address of the I2C Master module
//!
//! This function reads a byte of data from the I2C Master Data Register.
//!
//! \return Returns the byte received from by the I2C Master, cast as an
//! unsigned long.
//
//*****************************************************************************
#if defined(GROUP_masterdataget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
I2CMasterDataGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_MASTER_BASE);

    //
    // Read a byte.
    //
    return(HWREG(ulBase + I2C_MASTER_O_DR));
}
#endif

//*****************************************************************************
//
//! Gets the I2C Slave module status
//!
//! \param ulBase base address of the I2C Slave module
//!
//! This function will return the action requested from a master, if any. The
//! possible values returned are:
//!
//! - I2C_SLAVE_ACT_NONE
//! - I2C_SLAVE_ACT_RREQ
//! - I2C_SLAVE_ACT_TREQ
//!
//! where I2C_SLAVE_ACT_NONE means that no action has been requested of the
//! I2C Slave module, I2C_SLAVE_ACT_RREQ means that an I2C master has sent
//! data to the I2C Slave module, and I2C_SLAVE_ACT_TREQ means that an I2C
//! master has requested that the I2C Slave module send data.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slavestatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
I2CSlaveStatus(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Return the slave status.
    //
    return(HWREG(ulBase + I2C_SLAVE_O_CSR));
}
#endif

//*****************************************************************************
//
//! Transmits a byte from the I2C Slave.
//!
//! \param ulBase base address of the I2C Slave module
//! \param ucData data to be transmitted from the I2C Slave
//!
//! This function will place the supplied data into I2C Slave Data Register.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_slavedataput) || defined(BUILD_ALL) || defined(DOXYGEN)
void
I2CSlaveDataPut(unsigned long ulBase, unsigned char ucData)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Write the byte.
    //
    HWREG(ulBase + I2C_SLAVE_O_DR) = ucData;
}
#endif

//*****************************************************************************
//
//! Receives a byte that has been sent to the I2C Slave.
//!
//! \param ulBase base address of the I2C Slave module
//!
//! This function reads a byte of data from the I2C Slave Data Register.
//!
//! \return Returns the byte received from by the I2C Slave, cast as an
//! unsigned long.
//
//*****************************************************************************
#if defined(GROUP_slavedataget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
I2CSlaveDataGet(unsigned long ulBase)
{
    //
    // Check the arguments.
    //
    ASSERT(ulBase == I2C_SLAVE_BASE);

    //
    // Read a byte.
    //
    return(HWREG(ulBase + I2C_SLAVE_O_DR));
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
