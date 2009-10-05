//*****************************************************************************
//
// pdc.c - Driver for the Peripheral Device Controller (PDC) on the Stellaris
//         development board.
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
//*****************************************************************************

#include "LM3Sxxx.h"
#include "pdc.h"

//*****************************************************************************
//
//! Initializes the connection to the PDC.
//!
//! This function will enable clocking to the SSI and GPIO A modules, configure
//! the GPIO pins to be used for an SSI interface, and it will configure the
//! SSI as a 1Mb master device, operating in MOTO mode.  It will also enable
//! the SSI module, and will enable the chip select for the PDC on the
//! Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCInit(void)
{
    //
    // Enable the peripherals used to drive the PDC.
    //
    SysCtlPeripheralEnable(SYSCTL_PERIPH_SSI);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOA);

    //
    // Configure the appropriate pins to be SSI instead of GPIO.
    //
    GPIODirModeSet(GPIO_PORTA_BASE, SSI_CLK | SSI_TX | SSI_RX,
                   GPIO_DIR_MODE_HW);
    GPIODirModeSet(GPIO_PORTA_BASE, SSI_CS, GPIO_DIR_MODE_OUT);
    GPIOPadConfigSet(GPIO_PORTA_BASE, SSI_CLK, GPIO_STRENGTH_4MA,
                     GPIO_PIN_TYPE_STD_WPU);

    //
    // Configure the SSI port.
    //
    SSIConfig(SSI_BASE, SSI_FRF_MOTO_MODE_0, SSI_MODE_MASTER, 1000000, 8);
    SSIEnable(SSI_BASE);

    //
    // Reset the PDC SSI state machine.  The chip select needs to be held low
    // for 100ns; the procedure call overhead more than accounts for this time.
    //
    GPIOPinWrite(GPIO_PORTA_BASE, PDC_CS, 0);
    GPIOPinWrite(GPIO_PORTA_BASE, PDC_CS, PDC_CS);
}

//*****************************************************************************
//
//! Write a PDC register.
//!
//! \param ucAddr specifies the PDC register to write.
//! \param ucData specifies the data to write.
//!
//! This function will perform the SSI transfers required to write a register
//! in the PDC on the Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCWrite(unsigned char ucAddr, unsigned char ucData)
{
    unsigned long ulTemp;

    //
    // Send address and write command.
    //
    SSIDataPut(SSI_BASE, (ucAddr & 0x0F) | PDC_WR);

    //
    // Write the data.
    //
    SSIDataPut(SSI_BASE, ucData);

    //
    // Flush data read during address write.
    //
    SSIDataGet(SSI_BASE, &ulTemp);

    //
    // Flush data read during data write.
    //
    SSIDataGet(SSI_BASE, &ulTemp);
}
