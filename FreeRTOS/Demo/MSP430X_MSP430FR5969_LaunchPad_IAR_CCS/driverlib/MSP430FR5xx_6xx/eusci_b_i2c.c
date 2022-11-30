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
// eusci_b_i2c.c - Driver for the eusci_b_i2c Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup eusci_b_i2c_api eusci_b_i2c
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_EUSCI_Bx__
#include "eusci_b_i2c.h"

#include <assert.h>

void EUSCI_B_I2C_initMaster(uint16_t baseAddress,
                            EUSCI_B_I2C_initMasterParam *param)
{
    uint16_t preScalarValue;

    //Disable the USCI module and clears the other bits of control register
    HWREG16(baseAddress + OFS_UCBxCTLW0) = UCSWRST;

    //Configure Automatic STOP condition generation
    HWREG16(baseAddress + OFS_UCBxCTLW1) &= ~UCASTP_3;
    HWREG16(baseAddress + OFS_UCBxCTLW1) |= param->autoSTOPGeneration;

    //Byte Count Threshold
    HWREG16(baseAddress + OFS_UCBxTBCNT) = param->byteCounterThreshold;
    /*
     * Configure as I2C master mode.
     * UCMST = Master mode
     * UCMODE_3 = I2C mode
     * UCSYNC = Synchronous mode
     */
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCMST + UCMODE_3 + UCSYNC;

    //Configure I2C clock source
    HWREG16(baseAddress +
            OFS_UCBxCTLW0) |= (param->selectClockSource + UCSWRST);

    /*
     * Compute the clock divider that achieves the fastest speed less than or
     * equal to the desired speed.  The numerator is biased to favor a larger
     * clock divider so that the resulting clock is always less than or equal
     * to the desired clock, never greater.
     */
    preScalarValue = (uint16_t)(param->i2cClk / param->dataRate);
    HWREG16(baseAddress + OFS_UCBxBRW) = preScalarValue;
}

void EUSCI_B_I2C_initSlave(uint16_t baseAddress,
                           EUSCI_B_I2C_initSlaveParam *param)
{
    //Disable the USCI module
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;

    //Clear USCI master mode
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~UCMST;

    //Configure I2C as Slave and Synchronous mode
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCMODE_3 + UCSYNC;

    //Set up the slave address.
    HWREG16(baseAddress + OFS_UCBxI2COA0 + param->slaveAddressOffset)
        = param->slaveAddress + param->slaveOwnAddressEnable;
}

void EUSCI_B_I2C_enable(uint16_t baseAddress)
{
    //Reset the UCSWRST bit to enable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~(UCSWRST);
}

void EUSCI_B_I2C_disable(uint16_t baseAddress)
{
    //Set the UCSWRST bit to disable the USCI Module
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;
}

void EUSCI_B_I2C_setSlaveAddress(uint16_t baseAddress,
                                 uint8_t slaveAddress)
{
    //Set the address of the slave with which the master will communicate.
    HWREG16(baseAddress + OFS_UCBxI2CSA) = (slaveAddress);
}

void EUSCI_B_I2C_setMode(uint16_t baseAddress,
                         uint8_t mode)
{
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~EUSCI_B_I2C_TRANSMIT_MODE;
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= mode;
}

uint8_t EUSCI_B_I2C_getMode(uint16_t baseAddress)
{
    //Read the I2C mode.
    return ((HWREG16(baseAddress + OFS_UCBxCTLW0) & UCTR));
}

void EUSCI_B_I2C_slavePutData(uint16_t baseAddress,
                              uint8_t transmitData)
{
    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = transmitData;
}

uint8_t EUSCI_B_I2C_slaveGetData(uint16_t baseAddress)
{
    //Read a byte.
    return (HWREG16(baseAddress + OFS_UCBxRXBUF));
}

uint16_t EUSCI_B_I2C_isBusBusy(uint16_t baseAddress)
{
    //Return the bus busy status.
    return (HWREG16(baseAddress + OFS_UCBxSTATW) & UCBBUSY);
}

uint16_t EUSCI_B_I2C_masterIsStopSent(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_UCBxCTLW0) & UCTXSTP);
}

uint16_t EUSCI_B_I2C_masterIsStartSent(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_UCBxCTLW0) & UCTXSTT);
}

void EUSCI_B_I2C_enableInterrupt(uint16_t baseAddress,
                                 uint16_t mask)
{
    //Enable the interrupt masked bit
    HWREG16(baseAddress + OFS_UCBxIE) |= mask;
}

void EUSCI_B_I2C_disableInterrupt(uint16_t baseAddress,
                                  uint16_t mask)
{
    //Disable the interrupt masked bit
    HWREG16(baseAddress + OFS_UCBxIE) &= ~(mask);
}

void EUSCI_B_I2C_clearInterrupt(uint16_t baseAddress,
                                uint16_t mask)
{
    //Clear the I2C interrupt source.
    HWREG16(baseAddress + OFS_UCBxIFG) &= ~(mask);
}

uint16_t EUSCI_B_I2C_getInterruptStatus(uint16_t baseAddress,
                                        uint16_t mask)
{
    //Return the interrupt status of the request masked bit.
    return (HWREG16(baseAddress + OFS_UCBxIFG) & mask);
}

void EUSCI_B_I2C_masterSendSingleByte(uint16_t baseAddress,
                                      uint8_t txData)
{
    //Store current TXIE status
    uint16_t txieStatus = HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE;

    //Disable transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) &= ~(UCTXIE);

    //Send start condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTR + UCTXSTT;

    //Poll for transmit interrupt flag.
    while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG))
    {
        ;
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;

    //Poll for transmit interrupt flag.
    while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG))
    {
        ;
    }

    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;

    //Clear transmit interrupt flag before enabling interrupt again
    HWREG16(baseAddress + OFS_UCBxIFG) &= ~(UCTXIFG);

    //Reinstate transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) |= txieStatus;
}

uint8_t EUSCI_B_I2C_masterReceiveSingleByte(uint16_t baseAddress)
{
    //Set USCI in Receive mode
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~UCTR;

    //Send start
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= (UCTXSTT + UCTXSTP);

    //Poll for receive interrupt flag.
    while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCRXIFG))
    {
        ;
    }

    //Send single byte data.
    return (HWREG16(baseAddress + OFS_UCBxRXBUF));
}

bool EUSCI_B_I2C_masterSendSingleByteWithTimeout(uint16_t baseAddress,
                                                 uint8_t txData,
                                                 uint32_t timeout)
{
    // Creating variable for second timeout scenario
    uint32_t timeout2 = timeout;

    //Store current TXIE status
    uint16_t txieStatus = HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE;

    //Disable transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) &= ~(UCTXIE);

    //Send start condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTR + UCTXSTT;

    //Poll for transmit interrupt flag.
    while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG)) && --timeout)
    {
        ;
    }

    //Check if transfer timed out
    if(timeout == 0)
    {
        return (STATUS_FAIL);
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;

    //Poll for transmit interrupt flag.
    while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG)) && --timeout2)
    {
        ;
    }

    //Check if transfer timed out
    if(timeout2 == 0)
    {
        return (STATUS_FAIL);
    }

    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;

    //Clear transmit interrupt flag before enabling interrupt again
    HWREG16(baseAddress + OFS_UCBxIFG) &= ~(UCTXIFG);

    //Reinstate transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) |= txieStatus;

    return (STATUS_SUCCESS);
}

void EUSCI_B_I2C_masterSendMultiByteStart(uint16_t baseAddress,
                                          uint8_t txData)
{
    //Store current transmit interrupt enable
    uint16_t txieStatus = HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE;

    //Disable transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) &= ~(UCTXIE);

    //Send start condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTR + UCTXSTT;

    //Poll for transmit interrupt flag.
    while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG))
    {
        ;
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;

    //Reinstate transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) |= txieStatus;
}

bool EUSCI_B_I2C_masterSendMultiByteStartWithTimeout(uint16_t baseAddress,
                                                     uint8_t txData,
                                                     uint32_t timeout)
{
    //Store current transmit interrupt enable
    uint16_t txieStatus = HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE;

    //Disable transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) &= ~(UCTXIE);

    //Send start condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTR + UCTXSTT;

    //Poll for transmit interrupt flag.
    while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG)) && --timeout)
    {
        ;
    }

    //Check if transfer timed out
    if(timeout == 0)
    {
        return (STATUS_FAIL);
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;

    //Reinstate transmit interrupt enable
    HWREG16(baseAddress + OFS_UCBxIE) |= txieStatus;

    return(STATUS_SUCCESS);
}

void EUSCI_B_I2C_masterSendMultiByteNext(uint16_t baseAddress,
                                         uint8_t txData)
{
    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag.
        while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG))
        {
            ;
        }
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;
}

bool EUSCI_B_I2C_masterSendMultiByteNextWithTimeout(uint16_t baseAddress,
                                                    uint8_t txData,
                                                    uint32_t timeout)
{
    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag.
        while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG)) && --timeout)
        {
            ;
        }

        //Check if transfer timed out
        if(timeout == 0)
        {
            return (STATUS_FAIL);
        }
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;

    return(STATUS_SUCCESS);
}

void EUSCI_B_I2C_masterSendMultiByteFinish(uint16_t baseAddress,
                                           uint8_t txData)
{
    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag.
        while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG))
        {
            ;
        }
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;

    //Poll for transmit interrupt flag.
    while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG))
    {
        ;
    }

    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;
}

bool EUSCI_B_I2C_masterSendMultiByteFinishWithTimeout(uint16_t baseAddress,
                                                      uint8_t txData,
                                                      uint32_t timeout)
{
    uint32_t timeout2 = timeout;

    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag.
        while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG)) && --timeout)
        {
            ;
        }

        //Check if transfer timed out
        if(timeout == 0)
        {
            return (STATUS_FAIL);
        }
    }

    //Send single byte data.
    HWREG16(baseAddress + OFS_UCBxTXBUF) = txData;

    //Poll for transmit interrupt flag.
    while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG)) && --timeout2)
    {
        ;
    }

    //Check if transfer timed out
    if(timeout2 == 0)
    {
        return (STATUS_FAIL);
    }

    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;

    return(STATUS_SUCCESS);
}

void EUSCI_B_I2C_masterSendStart(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTT;
}

void EUSCI_B_I2C_masterSendMultiByteStop(uint16_t baseAddress)
{
    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag.
        while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG))
        {
            ;
        }
    }

    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;
}

bool EUSCI_B_I2C_masterSendMultiByteStopWithTimeout(uint16_t baseAddress,
                                                    uint32_t timeout)
{
    //If interrupts are not used, poll for flags
    if(!(HWREG16(baseAddress + OFS_UCBxIE) & UCTXIE))
    {
        //Poll for transmit interrupt flag.
        while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCTXIFG)) && --timeout)
        {
            ;
        }

        //Check if transfer timed out
        if(timeout == 0)
        {
            return (STATUS_FAIL);
        }
    }

    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;

    return (STATUS_SUCCESS);
}

void EUSCI_B_I2C_masterReceiveStart(uint16_t baseAddress)
{
    //Set USCI in Receive mode
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~UCTR;
    //Send start
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTT;
}

uint8_t EUSCI_B_I2C_masterReceiveMultiByteNext(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_UCBxRXBUF));
}

uint8_t EUSCI_B_I2C_masterReceiveMultiByteFinish(uint16_t baseAddress)
{
    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;

    //Wait for Stop to finish
    while(HWREG16(baseAddress + OFS_UCBxCTLW0) & UCTXSTP)
    {
        // Wait for RX buffer
        while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCRXIFG))
        {
            ;
        }
    }

    //Capture data from receive buffer after setting stop bit due to
    //MSP430 I2C critical timing.
    return (HWREG16(baseAddress + OFS_UCBxRXBUF));
}

bool EUSCI_B_I2C_masterReceiveMultiByteFinishWithTimeout(uint16_t baseAddress,
                                                         uint8_t *txData,
                                                         uint32_t timeout)
{
    uint32_t timeout2 = timeout;

    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;

    //Wait for Stop to finish
    while((HWREG16(baseAddress + OFS_UCBxCTLW0) & UCTXSTP) && --timeout)
    {
        ;
    }

    //Check if transfer timed out
    if(timeout == 0)
    {
        return (STATUS_FAIL);
    }

    // Wait for RX buffer
    while((!(HWREG16(baseAddress + OFS_UCBxIFG) & UCRXIFG)) && --timeout2)
    {
        ;
    }

    //Check if transfer timed out
    if(timeout2 == 0)
    {
        return (STATUS_FAIL);
    }

    //Capture data from receive buffer after setting stop bit due to
    //MSP430 I2C critical timing.
    *txData = (HWREG8(baseAddress + OFS_UCBxRXBUF));

    return (STATUS_SUCCESS);
}

void EUSCI_B_I2C_masterReceiveMultiByteStop(uint16_t baseAddress)
{
    //Send stop condition.
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCTXSTP;
}

void EUSCI_B_I2C_enableMultiMasterMode(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCMM;
}

void EUSCI_B_I2C_disableMultiMasterMode(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_UCBxCTLW0) |= UCSWRST;
    HWREG16(baseAddress + OFS_UCBxCTLW0) &= ~UCMM;
}

uint8_t EUSCI_B_I2C_masterReceiveSingle(uint16_t baseAddress)
{
    //Polling RXIFG0 if RXIE is not enabled
    if(!(HWREG16(baseAddress + OFS_UCBxIE) & UCRXIE0))
    {
        while(!(HWREG16(baseAddress + OFS_UCBxIFG) & UCRXIFG0))
        {
            ;
        }
    }

    //Read a byte.
    return (HWREG16(baseAddress + OFS_UCBxRXBUF));
}

uint32_t EUSCI_B_I2C_getReceiveBufferAddress(uint16_t baseAddress)
{
    return (baseAddress + OFS_UCBxRXBUF);
}

uint32_t EUSCI_B_I2C_getTransmitBufferAddress(uint16_t baseAddress)
{
    return (baseAddress + OFS_UCBxTXBUF);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for eusci_b_i2c_api
//! @}
//
//*****************************************************************************
