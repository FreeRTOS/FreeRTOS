/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// eusci_b_spi.c - Driver for the eusci_b_spi Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup eusci_b_spi_api eusci_b_spi
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_EUSCI_Bx__
#include "eusci_b_spi.h"

#include <assert.h>

void EUSCI_B_SPI_initMaster(uint16_t baseAddress,
                            EUSCI_B_SPI_initMasterParam *param)
{
    //Disable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;

    //Reset OFS_UCBxCTLW0 values
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCCKPH + UCCKPL + UC7BIT + UCMSB +
                                              UCMST + UCMODE_3 + UCSYNC);

    //Reset OFS_UCBxCTLW0 values
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCSSEL_3);

    //Select Clock
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= param->selectClockSource;

    HWREG16(baseAddress + OFS_UCBxBRW) =
        (uint16_t)(param->clockSourceFrequency / param->desiredSpiClock);

    /*
     * Configure as SPI master mode.
     * Clock phase select, polarity, msb
     * UCMST = Master mode
     * UCSYNC = Synchronous mode
     * UCMODE_0 = 3-pin SPI
     */
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= (
        param->msbFirst +
        param->clockPhase +
        param->clockPolarity +
        UCMST +
        UCSYNC +
        param->spiMode
        );
}

void EUSCI_B_SPI_select4PinFunctionality(uint16_t baseAddress,
                                         uint8_t select4PinFunctionality)
{
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~UCSTEM;
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= select4PinFunctionality;
}

void EUSCI_B_SPI_changeMasterClock(uint16_t baseAddress,
                                   EUSCI_B_SPI_changeMasterClockParam *param)
{
    //Disable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;

    HWREG16(baseAddress + OFS_UCBxBRW) =
        (uint16_t)(param->clockSourceFrequency / param->desiredSpiClock);

    //Reset the UCSWRST bit to enable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCSWRST);
}

void EUSCI_B_SPI_initSlave(uint16_t baseAddress,
                           EUSCI_B_SPI_initSlaveParam *param)
{
    //Disable USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;

    //Reset OFS_UCBxCTLW0 register
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCMSB +
                                              UC7BIT +
                                              UCMST +
                                              UCCKPL +
                                              UCCKPH +
                                              UCMODE_3
                                              );

    //Clock polarity, phase select, msbFirst, SYNC, Mode0
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= (param->clockPhase +
                                             param->clockPolarity +
                                             param->msbFirst +
                                             UCSYNC +
                                             param->spiMode
                                             );
}

void EUSCI_B_SPI_changeClockPhasePolarity(uint16_t baseAddress,
                                          uint16_t clockPhase,
                                          uint16_t clockPolarity)
{
    //Disable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;

    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCCKPH + UCCKPL);

    HWREG16(baseAddress + OFS_UCBxCTLW0) |= (
        clockPhase +
        clockPolarity
        );

    //Reset the UCSWRST bit to enable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCSWRST);
}

void EUSCI_B_SPI_transmitData(uint16_t baseAddress,
                              uint8_t transmitData)
{
    HWREG16(baseAddress + OFS_UCBxTXBUF) = transmitData;
}

uint8_t EUSCI_B_SPI_receiveData(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_UCBxRXBUF));
}

void EUSCI_B_SPI_enableInterrupt(uint16_t baseAddress,
                                 uint8_t mask)
{
    HWREG16(baseAddress + OFS_UCBxIE) |= mask;
}

void EUSCI_B_SPI_disableInterrupt(uint16_t baseAddress,
                                  uint8_t mask)
{
    HWREG16(baseAddress + OFS_UCBxIE) &= ~mask;
}

uint8_t EUSCI_B_SPI_getInterruptStatus(uint16_t baseAddress,
                                       uint8_t mask)
{
    return (HWREG16(baseAddress + OFS_UCBxIFG) & mask);
}

void EUSCI_B_SPI_clearInterrupt(uint16_t baseAddress,
                                uint8_t mask)
{
    HWREG16(baseAddress + OFS_UCBxIFG) &= ~mask;
}

void EUSCI_B_SPI_enable(uint16_t baseAddress)
{
    //Reset the UCSWRST bit to enable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCSWRST);
}

void EUSCI_B_SPI_disable(uint16_t baseAddress)
{
    //Set the UCSWRST bit to disable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;
}

uint32_t EUSCI_B_SPI_getReceiveBufferAddress(uint16_t baseAddress)
{
    return (baseAddress + OFS_UCBxRXBUF);
}

uint32_t EUSCI_B_SPI_getTransmitBufferAddress(uint16_t baseAddress)
{
    return (baseAddress + OFS_UCBxTXBUF);
}

uint16_t EUSCI_B_SPI_isBusy(uint16_t baseAddress)
{
    //Return the bus busy status.
    return (HWREG16(baseAddress + OFS_UCBxSTATW) & UCBUSY);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for eusci_b_spi_api
//! @}
//
//*****************************************************************************
