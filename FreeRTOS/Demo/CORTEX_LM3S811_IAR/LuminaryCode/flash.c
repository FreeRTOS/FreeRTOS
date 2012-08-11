//*****************************************************************************
//
// flash.c - Driver for programming the on-chip flash.
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
//! \addtogroup flash_api
//! @{
//
//*****************************************************************************

#include "../hw_flash.h"
#include "../hw_ints.h"
#include "../hw_memmap.h"
#include "../hw_sysctl.h"
#include "../hw_types.h"
#include "debug.h"
#include "flash.h"
#include "interrupt.h"

//*****************************************************************************
//
//! Gets the number of processor clocks per micro-second.
//!
//! This function returns the number of clocks per micro-second, as presently
//! known by the flash controller.
//!
//! \return Returns the number of processor clocks per micro-second.
//
//*****************************************************************************
#if defined(GROUP_usecget) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
FlashUsecGet(void)
{
    //
    // Return the number of clocks per micro-second.
    //
    return(HWREG(FLASH_USECRL) + 1);
}
#endif

//*****************************************************************************
//
//! Sets the number of processor clocks per micro-second.
//!
//! \param ulClocks is the number of processor clocks per micro-second.
//!
//! This function is used to tell the flash controller the number of processor
//! clocks per micro-second.  This value must be programmed correctly or the
//! flash most likely will not program correctly; it has no affect on reading
//! flash.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_usecset) || defined(BUILD_ALL) || defined(DOXYGEN)
void
FlashUsecSet(unsigned long ulClocks)
{
    //
    // Set the number of clocks per micro-second.
    //
    HWREG(FLASH_USECRL) = ulClocks - 1;
}
#endif

//*****************************************************************************
//
//! Erases a block of flash.
//!
//! \param ulAddress is the start address of the flash block to be erased.
//!
//! This function will erase a 1 kB block of the on-chip flash.  After erasing,
//! the block will be filled with 0xFF bytes.  Read-only and execute-only
//! blocks cannot be erased.
//!
//! This function will not return until the block has been erased.
//!
//! \return Returns 0 on success, or -1 if an invalid block address was
//! specified or the block is write-protected.
//
//*****************************************************************************
#if defined(GROUP_erase) || defined(BUILD_ALL) || defined(DOXYGEN)
long
FlashErase(unsigned long ulAddress)
{
    //
    // Check the arguments.
    //
    ASSERT(!(ulAddress & (FLASH_ERASE_SIZE - 1)));

    //
    // Clear the flash access interrupt.
    //
    HWREG(FLASH_FCMISC) = FLASH_FCMISC_ACCESS;

    //
    // Erase the block.
    //
    HWREG(FLASH_FMA) = ulAddress;
    HWREG(FLASH_FMC) = FLASH_FMC_WRKEY | FLASH_FMC_ERASE;

    //
    // Wait until the word has been programmed.
    //
    while(HWREG(FLASH_FMC) & FLASH_FMC_ERASE)
    {
    }

    //
    // Return an error if an access violation occurred.
    //
    if(HWREG(FLASH_FCRIS) & FLASH_FCRIS_ACCESS)
    {
        return(-1);
    }

    //
    // Success.
    //
    return(0);
}
#endif

//*****************************************************************************
//
//! Programs flash.
//!
//! \param pulData is a pointer to the data to be programmed.
//! \param ulAddress is the starting address in flash to be programmed.  Must
//! be a multiple of four.
//! \param ulCount is the number of bytes to be programmed.  Must be a multiple
//! of four.
//!
//! This function will program a sequence of words into the on-chip flash.
//! Programming each location consists of the result of an AND operation
//! of the new data and the existing data; in other words bits that contain
//! 1 can remain 1 or be changed to 0, but bits that are 0 cannot be changed
//! to 1.  Therefore, a word can be programmed multiple times as long as these
//! rules are followed; if a program operation attempts to change a 0 bit to
//! a 1 bit, that bit will not have its value changed.
//!
//! Since the flash is programmed one word at a time, the starting address and
//! byte count must both be multiples of four.  It is up to the caller to
//! verify the programmed contents, if such verification is required.
//!
//! This function will not return until the data has been programmed.
//!
//! \return Returns 0 on success, or -1 if a programming error is encountered.
//
//*****************************************************************************
#if defined(GROUP_program) || defined(BUILD_ALL) || defined(DOXYGEN)
long
FlashProgram(unsigned long *pulData, unsigned long ulAddress,
             unsigned long ulCount)
{
    //
    // Check the arguments.
    //
    ASSERT(!(ulAddress & 3));
    ASSERT(!(ulCount & 3));

    //
    // Clear the flash access interrupt.
    //
    HWREG(FLASH_FCMISC) = FLASH_FCMISC_ACCESS;

    //
    // Loop over the words to be programmed.
    //
    while(ulCount)
    {
        //
        // Program the next word.
        //
        HWREG(FLASH_FMA) = ulAddress;
        HWREG(FLASH_FMD) = *pulData;
        HWREG(FLASH_FMC) = FLASH_FMC_WRKEY | FLASH_FMC_WRITE;

        //
        // Wait until the word has been programmed.
        //
        while(HWREG(FLASH_FMC) & FLASH_FMC_WRITE)
        {
        }

        //
        // Increment to the next word.
        //
        pulData++;
        ulAddress += 4;
        ulCount -= 4;
    }

    //
    // Return an error if an access violation occurred.
    //
    if(HWREG(FLASH_FCRIS) & FLASH_FCRIS_ACCESS)
    {
        return(-1);
    }

    //
    // Success.
    //
    return(0);
}
#endif

//*****************************************************************************
//
//! Gets the protection setting for a block of flash.
//!
//! \param ulAddress is the start address of the flash block to be queried.
//!
//! This function will get the current protection for the specified 2 kB block
//! of flash.  Each block can be read/write, read-only, or execute-only.
//! Read/write blocks can be read, executed, erased, and programmed.  Read-only
//! blocks can be read and executed.  Execute-only blocks can only be executed;
//! processor and debugger data reads are not allowed.
//!
//! \return Returns the protection setting for this block.  See
//! FlashProtectSet() for possible values.
//
//*****************************************************************************
#if defined(GROUP_protectget) || defined(BUILD_ALL) || defined(DOXYGEN)
tFlashProtection
FlashProtectGet(unsigned long ulAddress)
{
    unsigned long ulFMPRE, ulFMPPE;

    //
    // Check the argument.
    //
    ASSERT(!(ulAddress & (FLASH_PROTECT_SIZE - 1)));

    //
    // Read the flash protection register and get the bits that apply to the
    // specified block.
    //
    ulFMPRE = HWREG(FLASH_FMPRE);
    ulFMPPE = HWREG(FLASH_FMPPE);
    switch((((ulFMPRE >> (ulAddress / FLASH_PROTECT_SIZE)) &
             FLASH_FMP_BLOCK_0) << 1) |
           ((ulFMPPE >> (ulAddress / FLASH_PROTECT_SIZE)) & FLASH_FMP_BLOCK_0))
    {
        //
        // This block is marked as execute only (i.e. it can not be erased or
        // programmed, and the only reads allowed are via the instruction fecth
        // interface).
        //
        case 0:
        case 1:
        {
            return(FlashExecuteOnly);
        }

        //
        // This block is marked as read only (i.e. it can not be erased or
        // programmed).
        //
        case 2:
        {
            return(FlashReadOnly);
        }

        //
        // This block is read/write; it can be read, erased, and programmed.
        //
        case 3:
        default:
        {
            return(FlashReadWrite);
        }
    }
}
#endif

//*****************************************************************************
//
//! Sets the protection setting for a block of flash.
//!
//! \param ulAddress is the start address of the flash block to be protected.
//! \param eProtect is the protection to be applied to the block.  Can be one
//! of \b FlashReadWrite, \b FlashReadOnly, or \b FlashExecuteOnly.
//!
//! This function will set the protection for the specified 2 kB block of
//! flash.  Blocks which are read/write can be made read-only or execute-only.
//! Blocks which are read-only can be made execute-only.  Blocks which are
//! execute-only cannot have their protection modified.  Attempts to make the
//! block protection less stringent (i.e. read-only to read/write) will result
//! in a failure (and be prevented by the hardware).
//!
//! Changes to the flash protection are maintained only until the next reset.
//! This allows the application to be executed in the desired flash protection
//! environment to check for inappropriate flash access (via the flash
//! interrupt).  To make the flash protection permanent, use the
//! FlashProtectSave() function.
//!
//! \return Returns 0 on success, or -1 if an invalid address or an invalid
//! protection was specified.
//
//*****************************************************************************
#if defined(GROUP_protectset) || defined(BUILD_ALL) || defined(DOXYGEN)
long
FlashProtectSet(unsigned long ulAddress, tFlashProtection eProtect)
{
    unsigned long ulProtectRE, ulProtectPE;

    //
    // Check the argument.
    //
    ASSERT(!(ulAddress & (FLASH_PROTECT_SIZE - 1)));
    ASSERT((eProtect == FlashReadWrite) || (eProtect == FlashReadOnly) ||
           (eProtect == FlashExecuteOnly));

    //
    // Convert the address into a block number.
    //
    ulAddress /= FLASH_PROTECT_SIZE;

    //
    // Get the current protection.
    //
    ulProtectRE = HWREG(FLASH_FMPRE);
    ulProtectPE = HWREG(FLASH_FMPPE);

    //
    // Set the protection based on the requested proection.
    //
    switch(eProtect)
    {
        //
        // Make this block execute only.
        //
        case FlashExecuteOnly:
        {
            //
            // Turn off the read and program bits for this block.
            //
            ulProtectRE &= ~(FLASH_FMP_BLOCK_0 << ulAddress);
            ulProtectPE &= ~(FLASH_FMP_BLOCK_0 << ulAddress);

            //
            // We're done handling this protection.
            //
            break;
        }

        //
        // Make this block read only.
        //
        case FlashReadOnly:
        {
            //
            // The block can not be made read only if it is execute only.
            //
            if(((ulProtectRE >> ulAddress) & FLASH_FMP_BLOCK_0) !=
               FLASH_FMP_BLOCK_0)
            {
                return(-1);
            }

            //
            // Make this block read only.
            //
            ulProtectPE &= ~(FLASH_FMP_BLOCK_0 << ulAddress);

            //
            // We're done handling this protection.
            //
            break;
        }

        //
        // Make this block read/write.
        //
        case FlashReadWrite:
        default:
        {
            //
            // The block can not be made read/write if it is not already
            // read/write.
            //
            if((((ulProtectRE >> ulAddress) & FLASH_FMP_BLOCK_0) !=
                FLASH_FMP_BLOCK_0) ||
               (((ulProtectPE >> ulAddress) & FLASH_FMP_BLOCK_0) !=
                FLASH_FMP_BLOCK_0))
            {
                return(-1);
            }

            //
            // The block is already read/write, so there is nothing to do.
            //
            return(0);
        }
    }

    //
    // Set the new protection.
    //
    HWREG(FLASH_FMPRE) = ulProtectRE;
    HWREG(FLASH_FMPPE) = ulProtectPE;

    //
    // Success.
    //
    return(0);
}
#endif

//*****************************************************************************
//
//! Saves the flash protection settings.
//!
//! This function will make the currently programmed flash protection settings
//! permanent.  This is a non-reversible operation; a chip reset or power cycle
//! will not change the flash protection.
//!
//! This function will not return until the protection has been saved.
//!
//! \return Returns 0 on success, or -1 if a hardware error is encountered.
//
//*****************************************************************************
#if defined(GROUP_protectsave) || defined(BUILD_ALL) || defined(DOXYGEN)
long
FlashProtectSave(void)
{
    //
    // Tell the flash controller to write the flash read protection register.
    //
    HWREG(FLASH_FMA) = 0;
    HWREG(FLASH_FMC) = FLASH_FMC_WRKEY | FLASH_FMC_COMT;

    //
    // Wait until the write has completed.
    //
    while(HWREG(FLASH_FMC) & FLASH_FMC_COMT)
    {
    }

    //
    // Tell the flash controller to write the flash program protection
    // register.
    //
    HWREG(FLASH_FMA) = 1;
    HWREG(FLASH_FMC) = FLASH_FMC_WRKEY | FLASH_FMC_COMT;

    //
    // Wait until the write has completed.
    //
    while(HWREG(FLASH_FMC) & FLASH_FMC_COMT)
    {
    }

    //
    // Success.
    //
    return(0);
}
#endif

//*****************************************************************************
//
//! Registers an interrupt handler for the flash interrupt.
//!
//! \param pfnHandler is a pointer to the function to be called when the flash
//! interrupt occurs.
//!
//! This sets the handler to be called when the flash interrupt occurs.  The
//! flash controller can generate an interrupt when an invalid flash access
//! occurs, such as trying to program or erase a read-only block, or trying to
//! read from an execute-only block.  It can also generate an interrupt when a
//! program or erase operation has completed.  The interrupt will be
//! automatically enabled when the handler is registered.
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
FlashIntRegister(void (*pfnHandler)(void))
{
    //
    // Register the interrupt handler, returning an error if an error occurs.
    //
    IntRegister(INT_FLASH, pfnHandler);

    //
    // Enable the flash interrupt.
    //
    IntEnable(INT_FLASH);
}
#endif

//*****************************************************************************
//
//! Unregisters the interrupt handler for the flash interrupt.
//!
//! This function will clear the handler to be called when the flash interrupt
//! occurs.  This will also mask off the interrupt in the interrupt controller
//! so that the interrupt handler is no longer called.
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intunregister) || defined(BUILD_ALL) || defined(DOXYGEN)
void
FlashIntUnregister(void)
{
    //
    // Disable the interrupt.
    //
    IntDisable(INT_FLASH);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(INT_FLASH);
}
#endif

//*****************************************************************************
//
//! Enables individual flash controller interrupt sources.
//!
//! \param ulIntFlags is a bit mask of the interrupt sources to be enabled.
//! Can be any of the \b FLASH_FCIM_PROGRAM or \b FLASH_FCIM_ACCESS values.
//!
//! Enables the indicated flash controller interrupt sources.  Only the sources
//! that are enabled can be reflected to the processor interrupt; disabled
//! sources have no effect on the processor.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intenable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
FlashIntEnable(unsigned long ulIntFlags)
{
    //
    // Enable the specified interrupts.
    //
    HWREG(FLASH_FCIM) |= ulIntFlags;
}
#endif

//*****************************************************************************
//
//! Disables individual flash controller interrupt sources.
//!
//! \param ulIntFlags is a bit mask of the interrupt sources to be disabled.
//! Can be any of the \b FLASH_FCIM_PROGRAM or \b FLASH_FCIM_ACCESS values.
//!
//! Disables the indicated flash controller interrupt sources.  Only the
//! sources that are enabled can be reflected to the processor interrupt;
//! disabled sources have no effect on the processor.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intdisable) || defined(BUILD_ALL) || defined(DOXYGEN)
void
FlashIntDisable(unsigned long ulIntFlags)
{
    //
    // Disable the specified interrupts.
    //
    HWREG(FLASH_FCIM) &= ~(ulIntFlags);
}
#endif

//*****************************************************************************
//
//! Gets the current interrupt status.
//!
//! \param bMasked is false if the raw interrupt status is required and true if
//! the masked interrupt status is required.
//!
//! This returns the interrupt status for the flash controller.  Either the raw
//! interrupt status or the status of interrupts that are allowed to reflect to
//! the processor can be returned.
//!
//! \return The current interrupt status, enumerated as a bit field of
//! \b FLASH_FCMISC_PROGRAM and \b FLASH_FCMISC_ACCESS.
//
//*****************************************************************************
#if defined(GROUP_intgetstatus) || defined(BUILD_ALL) || defined(DOXYGEN)
unsigned long
FlashIntGetStatus(tBoolean bMasked)
{
    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        return(HWREG(FLASH_FCMISC));
    }
    else
    {
        return(HWREG(FLASH_FCRIS));
    }
}
#endif

//*****************************************************************************
//
//! Clears flash controller interrupt sources.
//!
//! \param ulIntFlags is the bit mask of the interrupt sources to be cleared.
//! Can be any of the \b FLASH_FCMISC_PROGRAM or \b FLASH_FCMISC_ACCESS
//! values.
//!
//! The specified flash controller interrupt sources are cleared, so that they
//! no longer assert.  This must be done in the interrupt handler to keep it
//! from being called again immediately upon exit.
//!
//! \return None.
//
//*****************************************************************************
#if defined(GROUP_intclear) || defined(BUILD_ALL) || defined(DOXYGEN)
void
FlashIntClear(unsigned long ulIntFlags)
{
    //
    // Clear the flash interrupt.
    //
    HWREG(FLASH_FCMISC) = ulIntFlags;
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
