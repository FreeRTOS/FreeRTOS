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
// eusci_a_uart.c - Driver for the eusci_a_uart Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup eusci_a_uart_api eusci_a_uart
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_EUSCI_Ax__
#include "eusci_a_uart.h"

#include <assert.h>

bool EUSCI_A_UART_init(uint16_t baseAddress,
                       EUSCI_A_UART_initParam *param)
{
    bool retVal = STATUS_SUCCESS;

    //Disable the USCI Module
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCSWRST;

    //Clock source select
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~UCSSEL_3;
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= param->selectClockSource;

    //MSB, LSB select
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~UCMSB;
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= param->msborLsbFirst;

    //UCSPB = 0(1 stop bit) OR 1(2 stop bits)
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~UCSPB;
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= param->numberofStopBits;

    //Parity
    switch(param->parity)
    {
    case EUSCI_A_UART_NO_PARITY:
        //No Parity
        HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~UCPEN;
        break;
    case EUSCI_A_UART_ODD_PARITY:
        //Odd Parity
        HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCPEN;
        HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~UCPAR;
        break;
    case EUSCI_A_UART_EVEN_PARITY:
        //Even Parity
        HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCPEN;
        HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCPAR;
        break;
    }

    //BaudRate Control Register
    HWREG16(baseAddress + OFS_UCAxBRW) = param->clockPrescalar;
    //Modulation Control Register
    HWREG16(baseAddress + OFS_UCAxMCTLW) = ((param->secondModReg << 8)
                                            + (param->firstModReg <<
    4) + param->overSampling);

    //Asynchronous mode & 8 bit character select & clear mode
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~(UCSYNC +
                                              UC7BIT +
                                              UCMODE_3
                                              );

    //Configure  UART mode.
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= param->uartMode;

    //Reset UCRXIE, UCBRKIE, UCDORM, UCTXADDR, UCTXBRK
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~(UCRXEIE + UCBRKIE + UCDORM +
                                              UCTXADDR + UCTXBRK
                                              );
    return (retVal);
}

void EUSCI_A_UART_transmitData(uint16_t baseAddress,
                               uint8_t transmitData)
{
    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCAxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag
        while(!(HWREG16(baseAddress + OFS_UCAxIFG) & UCTXIFG))
        {
            ;
        }
    }

    HWREG16(baseAddress + OFS_UCAxTXBUF) = transmitData;
}

uint8_t EUSCI_A_UART_receiveData(uint16_t baseAddress)
{
    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCAxIE) & UCRXIE))
    {
        //Poll for receive interrupt flag
        while(!(HWREG16(baseAddress + OFS_UCAxIFG) & UCRXIFG))
        {
            ;
        }
    }

    return (HWREG16(baseAddress + OFS_UCAxRXBUF));
}

void EUSCI_A_UART_enableInterrupt(uint16_t baseAddress,
                                  uint8_t mask)
{
    uint8_t locMask;

    locMask = (mask & (EUSCI_A_UART_RECEIVE_INTERRUPT
                       | EUSCI_A_UART_TRANSMIT_INTERRUPT
                       | EUSCI_A_UART_STARTBIT_INTERRUPT
                       | EUSCI_A_UART_TRANSMIT_COMPLETE_INTERRUPT));

    HWREG16(baseAddress + OFS_UCAxIE) |= locMask;

    locMask = (mask & (EUSCI_A_UART_RECEIVE_ERRONEOUSCHAR_INTERRUPT
                       | EUSCI_A_UART_BREAKCHAR_INTERRUPT));
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= locMask;
}

void EUSCI_A_UART_disableInterrupt(uint16_t baseAddress,
                                   uint8_t mask)
{
    uint8_t locMask;

    locMask = (mask & (EUSCI_A_UART_RECEIVE_INTERRUPT
                       | EUSCI_A_UART_TRANSMIT_INTERRUPT
                       | EUSCI_A_UART_STARTBIT_INTERRUPT
                       | EUSCI_A_UART_TRANSMIT_COMPLETE_INTERRUPT));
    HWREG16(baseAddress + OFS_UCAxIE) &= ~locMask;

    locMask = (mask & (EUSCI_A_UART_RECEIVE_ERRONEOUSCHAR_INTERRUPT
                       | EUSCI_A_UART_BREAKCHAR_INTERRUPT));
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~locMask;
}

uint8_t EUSCI_A_UART_getInterruptStatus(uint16_t baseAddress,
                                        uint8_t mask)
{
    return (HWREG16(baseAddress + OFS_UCAxIFG) & mask);
}

void EUSCI_A_UART_clearInterrupt(uint16_t baseAddress,
                                 uint8_t mask)
{
    //Clear the UART interrupt source.
    HWREG16(baseAddress + OFS_UCAxIFG) &= ~(mask);
}

void EUSCI_A_UART_enable(uint16_t baseAddress)
{
    //Reset the UCSWRST bit to enable the USCI Module
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~(UCSWRST);
}

void EUSCI_A_UART_disable(uint16_t baseAddress)
{
    //Set the UCSWRST bit to disable the USCI Module
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCSWRST;
}

uint8_t EUSCI_A_UART_queryStatusFlags(uint16_t baseAddress,
                                      uint8_t mask)
{
    return (HWREG16(baseAddress + OFS_UCAxSTATW) & mask);
}

void EUSCI_A_UART_setDormant(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCDORM;
}

void EUSCI_A_UART_resetDormant(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_UCAxCTLW0) &= ~UCDORM;
}

void EUSCI_A_UART_transmitAddress(uint16_t baseAddress,
                                  uint8_t transmitAddress)
{
    //Set UCTXADDR bit
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCTXADDR;

    //Place next byte to be sent into the transmit buffer
    HWREG16(baseAddress + OFS_UCAxTXBUF) = transmitAddress;
}

void EUSCI_A_UART_transmitBreak(uint16_t baseAddress)
{
    //Set UCTXADDR bit
    HWREG16(baseAddress + OFS_UCAxCTLW0) |= UCTXBRK;

    //If current mode is automatic baud-rate detection
    if(EUSCI_A_UART_AUTOMATIC_BAUDRATE_DETECTION_MODE ==
       (HWREG16(baseAddress + OFS_UCAxCTLW0) &
        EUSCI_A_UART_AUTOMATIC_BAUDRATE_DETECTION_MODE))
    {
        HWREG16(baseAddress +
                OFS_UCAxTXBUF) = EUSCI_A_UART_AUTOMATICBAUDRATE_SYNC;
    }
    else
    {
        HWREG16(baseAddress + OFS_UCAxTXBUF) = DEFAULT_SYNC;
    }

    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCAxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag
        while(!(HWREG16(baseAddress + OFS_UCAxIFG) & UCTXIFG))
        {
            ;
        }
    }
}

uint32_t EUSCI_A_UART_getReceiveBufferAddress(uint16_t baseAddress)
{
    return (baseAddress + OFS_UCAxRXBUF);
}

uint32_t EUSCI_A_UART_getTransmitBufferAddress(uint16_t baseAddress)
{
    return (baseAddress + OFS_UCAxTXBUF);
}

void EUSCI_A_UART_selectDeglitchTime(uint16_t baseAddress,
                                     uint16_t deglitchTime)
{
    HWREG16(baseAddress + OFS_UCAxCTLW1) &= ~(UCGLIT1 + UCGLIT0);

    HWREG16(baseAddress + OFS_UCAxCTLW1) |= deglitchTime;
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for eusci_a_uart_api
//! @}
//
//*****************************************************************************
