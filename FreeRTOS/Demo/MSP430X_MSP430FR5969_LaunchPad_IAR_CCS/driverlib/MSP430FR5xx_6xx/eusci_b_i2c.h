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
// eusci_b_i2c.h - Driver for the EUSCI_B_I2C Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_EUSCI_B_I2C_H__
#define __MSP430WARE_EUSCI_B_I2C_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_EUSCI_Bx__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

#include "inc/hw_regaccess.h"
//*****************************************************************************
//
//! \brief Used in the EUSCI_B_I2C_initMaster() function as the param
//! parameter.
//
//*****************************************************************************
typedef struct EUSCI_B_I2C_initMasterParam
{
    //! Is the clocksource.
    //! \n Valid values are:
    //! - \b EUSCI_B_I2C_CLOCKSOURCE_ACLK
    //! - \b EUSCI_B_I2C_CLOCKSOURCE_SMCLK
    uint8_t selectClockSource;
    //! Is the rate of the clock supplied to the I2C module (the frequency in
    //! Hz of the clock source specified in selectClockSource).
    uint32_t i2cClk;
    //! Setup for selecting data transfer rate.
    //! \n Valid values are:
    //! - \b EUSCI_B_I2C_SET_DATA_RATE_400KBPS
    //! - \b EUSCI_B_I2C_SET_DATA_RATE_100KBPS
    uint32_t dataRate;
    //! Sets threshold for automatic STOP or UCSTPIFG
    uint8_t byteCounterThreshold;
    //! Sets up the STOP condition generation.
    //! \n Valid values are:
    //! - \b EUSCI_B_I2C_NO_AUTO_STOP
    //! - \b EUSCI_B_I2C_SET_BYTECOUNT_THRESHOLD_FLAG
    //! - \b EUSCI_B_I2C_SEND_STOP_AUTOMATICALLY_ON_BYTECOUNT_THRESHOLD
    uint8_t autoSTOPGeneration;
} EUSCI_B_I2C_initMasterParam;

//*****************************************************************************
//
//! \brief Used in the EUSCI_B_I2C_initSlave() function as the param parameter.
//
//*****************************************************************************
typedef struct EUSCI_B_I2C_initSlaveParam
{
    //! 7-bit slave address
    uint8_t slaveAddress;
    //! Own address Offset referred to- 'x' value of UCBxI2COAx.
    //! \n Valid values are:
    //! - \b EUSCI_B_I2C_OWN_ADDRESS_OFFSET0
    //! - \b EUSCI_B_I2C_OWN_ADDRESS_OFFSET1
    //! - \b EUSCI_B_I2C_OWN_ADDRESS_OFFSET2
    //! - \b EUSCI_B_I2C_OWN_ADDRESS_OFFSET3
    uint8_t slaveAddressOffset;
    //! Selects if the specified address is enabled or disabled.
    //! \n Valid values are:
    //! - \b EUSCI_B_I2C_OWN_ADDRESS_DISABLE
    //! - \b EUSCI_B_I2C_OWN_ADDRESS_ENABLE
    uint32_t slaveOwnAddressEnable;
} EUSCI_B_I2C_initSlaveParam;

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: EUSCI_B_I2C_initMaster().
//
//*****************************************************************************
#define EUSCI_B_I2C_NO_AUTO_STOP                                       UCASTP_0
#define EUSCI_B_I2C_SET_BYTECOUNT_THRESHOLD_FLAG                       UCASTP_1
#define EUSCI_B_I2C_SEND_STOP_AUTOMATICALLY_ON_BYTECOUNT_THRESHOLD     UCASTP_2

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: EUSCI_B_I2C_initMaster().
//
//*****************************************************************************
#define EUSCI_B_I2C_SET_DATA_RATE_400KBPS                                400000
#define EUSCI_B_I2C_SET_DATA_RATE_100KBPS                                100000

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: EUSCI_B_I2C_initMaster().
//
//*****************************************************************************
#define EUSCI_B_I2C_CLOCKSOURCE_ACLK                               UCSSEL__ACLK
#define EUSCI_B_I2C_CLOCKSOURCE_SMCLK                             UCSSEL__SMCLK

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: EUSCI_B_I2C_initSlave().
//
//*****************************************************************************
#define EUSCI_B_I2C_OWN_ADDRESS_OFFSET0                                    0x00
#define EUSCI_B_I2C_OWN_ADDRESS_OFFSET1                                    0x02
#define EUSCI_B_I2C_OWN_ADDRESS_OFFSET2                                    0x04
#define EUSCI_B_I2C_OWN_ADDRESS_OFFSET3                                    0x06

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: EUSCI_B_I2C_initSlave().
//
//*****************************************************************************
#define EUSCI_B_I2C_OWN_ADDRESS_DISABLE                                    0x00
#define EUSCI_B_I2C_OWN_ADDRESS_ENABLE                                   UCOAEN

//*****************************************************************************
//
// The following are values that can be passed to the mode parameter for
// functions: EUSCI_B_I2C_setMode() as well as returned by the
// EUSCI_B_I2C_getMode() function.
//
//*****************************************************************************
#define EUSCI_B_I2C_TRANSMIT_MODE                                          UCTR
#define EUSCI_B_I2C_RECEIVE_MODE                                           0x00

//*****************************************************************************
//
// The following are values that can be passed to the mask parameter for
// functions: EUSCI_B_I2C_enableInterrupt(), EUSCI_B_I2C_disableInterrupt(),
// EUSCI_B_I2C_clearInterrupt(), and EUSCI_B_I2C_getInterruptStatus() as well
// as returned by the EUSCI_B_I2C_getInterruptStatus() function.
//
//*****************************************************************************
#define EUSCI_B_I2C_NAK_INTERRUPT                                      UCNACKIE
#define EUSCI_B_I2C_ARBITRATIONLOST_INTERRUPT                            UCALIE
#define EUSCI_B_I2C_STOP_INTERRUPT                                      UCSTPIE
#define EUSCI_B_I2C_START_INTERRUPT                                     UCSTTIE
#define EUSCI_B_I2C_TRANSMIT_INTERRUPT0                                 UCTXIE0
#define EUSCI_B_I2C_TRANSMIT_INTERRUPT1                                 UCTXIE1
#define EUSCI_B_I2C_TRANSMIT_INTERRUPT2                                 UCTXIE2
#define EUSCI_B_I2C_TRANSMIT_INTERRUPT3                                 UCTXIE3
#define EUSCI_B_I2C_RECEIVE_INTERRUPT0                                  UCRXIE0
#define EUSCI_B_I2C_RECEIVE_INTERRUPT1                                  UCRXIE1
#define EUSCI_B_I2C_RECEIVE_INTERRUPT2                                  UCRXIE2
#define EUSCI_B_I2C_RECEIVE_INTERRUPT3                                  UCRXIE3
#define EUSCI_B_I2C_BIT9_POSITION_INTERRUPT                            UCBIT9IE
#define EUSCI_B_I2C_CLOCK_LOW_TIMEOUT_INTERRUPT                        UCCLTOIE
#define EUSCI_B_I2C_BYTE_COUNTER_INTERRUPT                             UCBCNTIE

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the EUSCI_B_I2C_isBusBusy() function.
//
//*****************************************************************************
#define EUSCI_B_I2C_BUS_BUSY                                            UCBBUSY
#define EUSCI_B_I2C_BUS_NOT_BUSY                                           0x00

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the EUSCI_B_I2C_masterIsStopSent() function.
//
//*****************************************************************************
#define EUSCI_B_I2C_STOP_SEND_COMPLETE                                     0x00
#define EUSCI_B_I2C_SENDING_STOP                                        UCTXSTP

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the EUSCI_B_I2C_masterIsStartSent() function.
//
//*****************************************************************************
#define EUSCI_B_I2C_START_SEND_COMPLETE                                    0x00
#define EUSCI_B_I2C_SENDING_START                                       UCTXSTT

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Initializes the I2C Master block.
//!
//! This function initializes operation of the I2C Master block. Upon
//! successful initialization of the I2C block, this function will have set the
//! bus speed for the master; however I2C module is still disabled till
//! EUSCI_B_I2C_enable is invoked.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param param is the pointer to the struct for master initialization.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_initMaster(uint16_t baseAddress,
                                   EUSCI_B_I2C_initMasterParam *param);

//*****************************************************************************
//
//! \brief Initializes the I2C Slave block.
//!
//! This function initializes operation of the I2C as a Slave mode. Upon
//! successful initialization of the I2C blocks, this function will have set
//! the slave address but the I2C module is still disabled till
//! EUSCI_B_I2C_enable is invoked.
//!
//! \param baseAddress is the base address of the I2C Slave module.
//! \param param is the pointer to the struct for slave initialization.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_initSlave(uint16_t baseAddress,
                                  EUSCI_B_I2C_initSlaveParam *param);

//*****************************************************************************
//
//! \brief Enables the I2C block.
//!
//! This will enable operation of the I2C block.
//!
//! \param baseAddress is the base address of the USCI I2C module.
//!
//! Modified bits are \b UCSWRST of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_enable(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables the I2C block.
//!
//! This will disable operation of the I2C block.
//!
//! \param baseAddress is the base address of the USCI I2C module.
//!
//! Modified bits are \b UCSWRST of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_disable(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Sets the address that the I2C Master will place on the bus.
//!
//! This function will set the address that the I2C Master will place on the
//! bus when initiating a transaction.
//!
//! \param baseAddress is the base address of the USCI I2C module.
//! \param slaveAddress 7-bit slave address
//!
//! Modified bits of \b UCBxI2CSA register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_setSlaveAddress(uint16_t baseAddress,
                                        uint8_t slaveAddress);

//*****************************************************************************
//
//! \brief Sets the mode of the I2C device
//!
//! When the receive parameter is set to EUSCI_B_I2C_TRANSMIT_MODE, the address
//! will indicate that the I2C module is in receive mode; otherwise, the I2C
//! module is in send mode.
//!
//! \param baseAddress is the base address of the USCI I2C module.
//! \param mode Mode for the EUSCI_B_I2C module
//!        Valid values are:
//!        - \b EUSCI_B_I2C_TRANSMIT_MODE [Default]
//!        - \b EUSCI_B_I2C_RECEIVE_MODE
//!
//! Modified bits are \b UCTR of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_setMode(uint16_t baseAddress,
                                uint8_t mode);

//*****************************************************************************
//
//! \brief Gets the mode of the I2C device
//!
//! Current I2C transmit/receive mode.
//!
//! \param baseAddress is the base address of the I2C module.
//!
//! Modified bits are \b UCTR of \b UCBxCTLW0 register.
//!
//! \return One of the following:
//!         - \b EUSCI_B_I2C_TRANSMIT_MODE
//!         - \b EUSCI_B_I2C_RECEIVE_MODE
//!         \n indicating the current mode
//
//*****************************************************************************
extern uint8_t EUSCI_B_I2C_getMode(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Transmits a byte from the I2C Module.
//!
//! This function will place the supplied data into I2C transmit data register
//! to start transmission.
//!
//! \param baseAddress is the base address of the I2C Slave module.
//! \param transmitData data to be transmitted from the I2C module
//!
//! Modified bits of \b UCBxTXBUF register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_slavePutData(uint16_t baseAddress,
                                     uint8_t transmitData);

//*****************************************************************************
//
//! \brief Receives a byte that has been sent to the I2C Module.
//!
//! This function reads a byte of data from the I2C receive data Register.
//!
//! \param baseAddress is the base address of the I2C Slave module.
//!
//! \return Returns the byte received from by the I2C module, cast as an
//!         uint8_t.
//
//*****************************************************************************
extern uint8_t EUSCI_B_I2C_slaveGetData(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Indicates whether or not the I2C bus is busy.
//!
//! This function returns an indication of whether or not the I2C bus is busy.
//! This function checks the status of the bus via UCBBUSY bit in UCBxSTAT
//! register.
//!
//! \param baseAddress is the base address of the I2C module.
//!
//! \return One of the following:
//!         - \b EUSCI_B_I2C_BUS_BUSY
//!         - \b EUSCI_B_I2C_BUS_NOT_BUSY
//!         \n indicating whether the bus is busy
//
//*****************************************************************************
extern uint16_t EUSCI_B_I2C_isBusBusy(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Indicates whether STOP got sent.
//!
//! This function returns an indication of whether or not STOP got sent This
//! function checks the status of the bus via UCTXSTP bit in UCBxCTL1 register.
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! \return One of the following:
//!         - \b EUSCI_B_I2C_STOP_SEND_COMPLETE
//!         - \b EUSCI_B_I2C_SENDING_STOP
//!         \n indicating whether the stop was sent
//
//*****************************************************************************
extern uint16_t EUSCI_B_I2C_masterIsStopSent(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Indicates whether Start got sent.
//!
//! This function returns an indication of whether or not Start got sent This
//! function checks the status of the bus via UCTXSTT bit in UCBxCTL1 register.
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! \return One of the following:
//!         - \b EUSCI_B_I2C_START_SEND_COMPLETE
//!         - \b EUSCI_B_I2C_SENDING_START
//!         \n indicating whether the start was sent
//
//*****************************************************************************
extern uint16_t EUSCI_B_I2C_masterIsStartSent(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enables individual I2C interrupt sources.
//!
//! Enables the indicated I2C interrupt sources. Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! \param baseAddress is the base address of the I2C module.
//! \param mask is the bit mask of the interrupt sources to be enabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b EUSCI_B_I2C_NAK_INTERRUPT - Not-acknowledge interrupt
//!        - \b EUSCI_B_I2C_ARBITRATIONLOST_INTERRUPT - Arbitration lost
//!           interrupt
//!        - \b EUSCI_B_I2C_STOP_INTERRUPT - STOP condition interrupt
//!        - \b EUSCI_B_I2C_START_INTERRUPT - START condition interrupt
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT0 - Transmit interrupt0
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT1 - Transmit interrupt1
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT2 - Transmit interrupt2
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT3 - Transmit interrupt3
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT0 - Receive interrupt0
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT1 - Receive interrupt1
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT2 - Receive interrupt2
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT3 - Receive interrupt3
//!        - \b EUSCI_B_I2C_BIT9_POSITION_INTERRUPT - Bit position 9 interrupt
//!        - \b EUSCI_B_I2C_CLOCK_LOW_TIMEOUT_INTERRUPT - Clock low timeout
//!           interrupt enable
//!        - \b EUSCI_B_I2C_BYTE_COUNTER_INTERRUPT - Byte counter interrupt
//!           enable
//!
//! Modified bits of \b UCBxIE register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_enableInterrupt(uint16_t baseAddress,
                                        uint16_t mask);

//*****************************************************************************
//
//! \brief Disables individual I2C interrupt sources.
//!
//! Disables the indicated I2C interrupt sources. Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! \param baseAddress is the base address of the I2C module.
//! \param mask is the bit mask of the interrupt sources to be disabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b EUSCI_B_I2C_NAK_INTERRUPT - Not-acknowledge interrupt
//!        - \b EUSCI_B_I2C_ARBITRATIONLOST_INTERRUPT - Arbitration lost
//!           interrupt
//!        - \b EUSCI_B_I2C_STOP_INTERRUPT - STOP condition interrupt
//!        - \b EUSCI_B_I2C_START_INTERRUPT - START condition interrupt
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT0 - Transmit interrupt0
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT1 - Transmit interrupt1
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT2 - Transmit interrupt2
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT3 - Transmit interrupt3
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT0 - Receive interrupt0
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT1 - Receive interrupt1
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT2 - Receive interrupt2
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT3 - Receive interrupt3
//!        - \b EUSCI_B_I2C_BIT9_POSITION_INTERRUPT - Bit position 9 interrupt
//!        - \b EUSCI_B_I2C_CLOCK_LOW_TIMEOUT_INTERRUPT - Clock low timeout
//!           interrupt enable
//!        - \b EUSCI_B_I2C_BYTE_COUNTER_INTERRUPT - Byte counter interrupt
//!           enable
//!
//! Modified bits of \b UCBxIE register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_disableInterrupt(uint16_t baseAddress,
                                         uint16_t mask);

//*****************************************************************************
//
//! \brief Clears I2C interrupt sources.
//!
//! The I2C interrupt source is cleared, so that it no longer asserts. The
//! highest interrupt flag is automatically cleared when an interrupt vector
//! generator is used.
//!
//! \param baseAddress is the base address of the I2C module.
//! \param mask is a bit mask of the interrupt sources to be cleared.
//!        Mask value is the logical OR of any of the following:
//!        - \b EUSCI_B_I2C_NAK_INTERRUPT - Not-acknowledge interrupt
//!        - \b EUSCI_B_I2C_ARBITRATIONLOST_INTERRUPT - Arbitration lost
//!           interrupt
//!        - \b EUSCI_B_I2C_STOP_INTERRUPT - STOP condition interrupt
//!        - \b EUSCI_B_I2C_START_INTERRUPT - START condition interrupt
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT0 - Transmit interrupt0
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT1 - Transmit interrupt1
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT2 - Transmit interrupt2
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT3 - Transmit interrupt3
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT0 - Receive interrupt0
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT1 - Receive interrupt1
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT2 - Receive interrupt2
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT3 - Receive interrupt3
//!        - \b EUSCI_B_I2C_BIT9_POSITION_INTERRUPT - Bit position 9 interrupt
//!        - \b EUSCI_B_I2C_CLOCK_LOW_TIMEOUT_INTERRUPT - Clock low timeout
//!           interrupt enable
//!        - \b EUSCI_B_I2C_BYTE_COUNTER_INTERRUPT - Byte counter interrupt
//!           enable
//!
//! Modified bits of \b UCBxIFG register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_clearInterrupt(uint16_t baseAddress,
                                       uint16_t mask);

//*****************************************************************************
//
//! \brief Gets the current I2C interrupt status.
//!
//! This returns the interrupt status for the I2C module based on which flag is
//! passed.
//!
//! \param baseAddress is the base address of the I2C module.
//! \param mask is the masked interrupt flag status to be returned.
//!        Mask value is the logical OR of any of the following:
//!        - \b EUSCI_B_I2C_NAK_INTERRUPT - Not-acknowledge interrupt
//!        - \b EUSCI_B_I2C_ARBITRATIONLOST_INTERRUPT - Arbitration lost
//!           interrupt
//!        - \b EUSCI_B_I2C_STOP_INTERRUPT - STOP condition interrupt
//!        - \b EUSCI_B_I2C_START_INTERRUPT - START condition interrupt
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT0 - Transmit interrupt0
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT1 - Transmit interrupt1
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT2 - Transmit interrupt2
//!        - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT3 - Transmit interrupt3
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT0 - Receive interrupt0
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT1 - Receive interrupt1
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT2 - Receive interrupt2
//!        - \b EUSCI_B_I2C_RECEIVE_INTERRUPT3 - Receive interrupt3
//!        - \b EUSCI_B_I2C_BIT9_POSITION_INTERRUPT - Bit position 9 interrupt
//!        - \b EUSCI_B_I2C_CLOCK_LOW_TIMEOUT_INTERRUPT - Clock low timeout
//!           interrupt enable
//!        - \b EUSCI_B_I2C_BYTE_COUNTER_INTERRUPT - Byte counter interrupt
//!           enable
//!
//! \return Logical OR of any of the following:
//!         - \b EUSCI_B_I2C_NAK_INTERRUPT Not-acknowledge interrupt
//!         - \b EUSCI_B_I2C_ARBITRATIONLOST_INTERRUPT Arbitration lost
//!         interrupt
//!         - \b EUSCI_B_I2C_STOP_INTERRUPT STOP condition interrupt
//!         - \b EUSCI_B_I2C_START_INTERRUPT START condition interrupt
//!         - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT0 Transmit interrupt0
//!         - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT1 Transmit interrupt1
//!         - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT2 Transmit interrupt2
//!         - \b EUSCI_B_I2C_TRANSMIT_INTERRUPT3 Transmit interrupt3
//!         - \b EUSCI_B_I2C_RECEIVE_INTERRUPT0 Receive interrupt0
//!         - \b EUSCI_B_I2C_RECEIVE_INTERRUPT1 Receive interrupt1
//!         - \b EUSCI_B_I2C_RECEIVE_INTERRUPT2 Receive interrupt2
//!         - \b EUSCI_B_I2C_RECEIVE_INTERRUPT3 Receive interrupt3
//!         - \b EUSCI_B_I2C_BIT9_POSITION_INTERRUPT Bit position 9 interrupt
//!         - \b EUSCI_B_I2C_CLOCK_LOW_TIMEOUT_INTERRUPT Clock low timeout
//!         interrupt enable
//!         - \b EUSCI_B_I2C_BYTE_COUNTER_INTERRUPT Byte counter interrupt
//!         enable
//!         \n indicating the status of the masked interrupts
//
//*****************************************************************************
extern uint16_t EUSCI_B_I2C_getInterruptStatus(uint16_t baseAddress,
                                               uint16_t mask);

//*****************************************************************************
//
//! \brief Does single byte transmission from Master to Slave
//!
//! This function is used by the Master module to send a single byte. This
//! function sends a start, then transmits the byte to the slave and then sends
//! a stop.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the data byte to be transmitted
//!
//! Modified bits of \b UCBxTXBUF register, bits of \b UCBxCTLW0 register, bits
//! of \b UCBxIE register and bits of \b UCBxIFG register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterSendSingleByte(uint16_t baseAddress,
                                             uint8_t txData);

//*****************************************************************************
//
//! \brief Does single byte reception from Slave
//!
//! This function is used by the Master module to receive a single byte. This
//! function sends start and stop, waits for data reception and then receives
//! the data from the slave
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! Modified bits of \b UCBxTXBUF register, bits of \b UCBxCTLW0 register, bits
//! of \b UCBxIE register and bits of \b UCBxIFG register.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the transmission process.
//
//*****************************************************************************
extern uint8_t EUSCI_B_I2C_masterReceiveSingleByte(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Does single byte transmission from Master to Slave with timeout
//!
//! This function is used by the Master module to send a single byte. This
//! function sends a start, then transmits the byte to the slave and then sends
//! a stop.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the data byte to be transmitted
//! \param timeout is the amount of time to wait until giving up
//!
//! Modified bits of \b UCBxTXBUF register, bits of \b UCBxCTLW0 register, bits
//! of \b UCBxIE register and bits of \b UCBxIFG register.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the transmission process.
//
//*****************************************************************************
extern bool EUSCI_B_I2C_masterSendSingleByteWithTimeout(uint16_t baseAddress,
                                                        uint8_t txData,
                                                        uint32_t timeout);

//*****************************************************************************
//
//! \brief Starts multi-byte transmission from Master to Slave
//!
//! This function is used by the master module to start a multi byte
//! transaction.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the first data byte to be transmitted
//!
//! Modified bits of \b UCBxTXBUF register, bits of \b UCBxCTLW0 register, bits
//! of \b UCBxIE register and bits of \b UCBxIFG register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterSendMultiByteStart(uint16_t baseAddress,
                                                 uint8_t txData);

//*****************************************************************************
//
//! \brief Starts multi-byte transmission from Master to Slave with timeout
//!
//! This function is used by the master module to start a multi byte
//! transaction.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the first data byte to be transmitted
//! \param timeout is the amount of time to wait until giving up
//!
//! Modified bits of \b UCBxTXBUF register, bits of \b UCBxCTLW0 register, bits
//! of \b UCBxIE register and bits of \b UCBxIFG register.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the transmission process.
//
//*****************************************************************************
extern bool EUSCI_B_I2C_masterSendMultiByteStartWithTimeout(
    uint16_t baseAddress,
    uint8_t txData,
    uint32_t timeout);

//*****************************************************************************
//
//! \brief Continues multi-byte transmission from Master to Slave
//!
//! This function is used by the Master module continue each byte of a multi-
//! byte transmission. This function transmits each data byte of a multi-byte
//! transmission to the slave.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the next data byte to be transmitted
//!
//! Modified bits of \b UCBxTXBUF register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterSendMultiByteNext(uint16_t baseAddress,
                                                uint8_t txData);

//*****************************************************************************
//
//! \brief Continues multi-byte transmission from Master to Slave with timeout
//!
//! This function is used by the Master module continue each byte of a multi-
//! byte transmission. This function transmits each data byte of a multi-byte
//! transmission to the slave.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the next data byte to be transmitted
//! \param timeout is the amount of time to wait until giving up
//!
//! Modified bits of \b UCBxTXBUF register.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the transmission process.
//
//*****************************************************************************
extern bool EUSCI_B_I2C_masterSendMultiByteNextWithTimeout(uint16_t baseAddress,
                                                           uint8_t txData,
                                                           uint32_t timeout);

//*****************************************************************************
//
//! \brief Finishes multi-byte transmission from Master to Slave
//!
//! This function is used by the Master module to send the last byte and STOP.
//! This function transmits the last data byte of a multi-byte transmission to
//! the slave and then sends a stop.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the last data byte to be transmitted in a multi-byte
//!        transmission
//!
//! Modified bits of \b UCBxTXBUF register and bits of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterSendMultiByteFinish(uint16_t baseAddress,
                                                  uint8_t txData);

//*****************************************************************************
//
//! \brief Finishes multi-byte transmission from Master to Slave with timeout
//!
//! This function is used by the Master module to send the last byte and STOP.
//! This function transmits the last data byte of a multi-byte transmission to
//! the slave and then sends a stop.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is the last data byte to be transmitted in a multi-byte
//!        transmission
//! \param timeout is the amount of time to wait until giving up
//!
//! Modified bits of \b UCBxTXBUF register and bits of \b UCBxCTLW0 register.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the transmission process.
//
//*****************************************************************************
extern bool EUSCI_B_I2C_masterSendMultiByteFinishWithTimeout(
    uint16_t baseAddress,
    uint8_t txData,
    uint32_t timeout);

//*****************************************************************************
//
//! \brief This function is used by the Master module to initiate START
//!
//! This function is used by the Master module to initiate START
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! Modified bits are \b UCTXSTT of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterSendStart(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Send STOP byte at the end of a multi-byte transmission from Master
//! to Slave
//!
//! This function is used by the Master module send STOP at the end of a multi-
//! byte transmission. This function sends a stop after current transmission is
//! complete.
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! Modified bits are \b UCTXSTP of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterSendMultiByteStop(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Send STOP byte at the end of a multi-byte transmission from Master
//! to Slave with timeout
//!
//! This function is used by the Master module send STOP at the end of a multi-
//! byte transmission. This function sends a stop after current transmission is
//! complete.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param timeout is the amount of time to wait until giving up
//!
//! Modified bits are \b UCTXSTP of \b UCBxCTLW0 register.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the transmission process.
//
//*****************************************************************************
extern bool EUSCI_B_I2C_masterSendMultiByteStopWithTimeout(uint16_t baseAddress,
                                                           uint32_t timeout);

//*****************************************************************************
//
//! \brief Starts reception at the Master end
//!
//! This function is used by the Master module initiate reception of a single
//! byte. This function sends a start.
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! Modified bits are \b UCTXSTT of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterReceiveStart(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Starts multi-byte reception at the Master end one byte at a time
//!
//! This function is used by the Master module to receive each byte of a multi-
//! byte reception. This function reads currently received byte.
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! \return Received byte at Master end.
//
//*****************************************************************************
extern uint8_t EUSCI_B_I2C_masterReceiveMultiByteNext(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Finishes multi-byte reception at the Master end
//!
//! This function is used by the Master module to initiate completion of a
//! multi-byte reception. This function receives the current byte and initiates
//! the STOP from master to slave.
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! Modified bits are \b UCTXSTP of \b UCBxCTLW0 register.
//!
//! \return Received byte at Master end.
//
//*****************************************************************************
extern uint8_t EUSCI_B_I2C_masterReceiveMultiByteFinish(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Finishes multi-byte reception at the Master end with timeout
//!
//! This function is used by the Master module to initiate completion of a
//! multi-byte reception. This function receives the current byte and initiates
//! the STOP from master to slave.
//!
//! \param baseAddress is the base address of the I2C Master module.
//! \param txData is a pointer to the location to store the received byte at
//!        master end
//! \param timeout is the amount of time to wait until giving up
//!
//! Modified bits are \b UCTXSTP of \b UCBxCTLW0 register.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the reception process
//
//*****************************************************************************
extern bool EUSCI_B_I2C_masterReceiveMultiByteFinishWithTimeout(
    uint16_t baseAddress,
    uint8_t *txData,
    uint32_t timeout);

//*****************************************************************************
//
//! \brief Sends the STOP at the end of a multi-byte reception at the Master
//! end
//!
//! This function is used by the Master module to initiate STOP
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! Modified bits are \b UCTXSTP of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_masterReceiveMultiByteStop(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enables Multi Master Mode
//!
//! At the end of this function, the I2C module is still disabled till
//! EUSCI_B_I2C_enable is invoked
//!
//! \param baseAddress is the base address of the I2C module.
//!
//! Modified bits are \b UCSWRST and \b UCMM of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_enableMultiMasterMode(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables Multi Master Mode
//!
//! At the end of this function, the I2C module is still disabled till
//! EUSCI_B_I2C_enable is invoked
//!
//! \param baseAddress is the base address of the I2C module.
//!
//! Modified bits are \b UCSWRST and \b UCMM of \b UCBxCTLW0 register.
//!
//! \return None
//
//*****************************************************************************
extern void EUSCI_B_I2C_disableMultiMasterMode(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief receives a byte that has been sent to the I2C Master Module.
//!
//! This function reads a byte of data from the I2C receive data Register.
//!
//! \param baseAddress is the base address of the I2C Master module.
//!
//! \return Returns the byte received from by the I2C module, cast as an
//!         uint8_t.
//
//*****************************************************************************
extern uint8_t EUSCI_B_I2C_masterReceiveSingle(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the address of the RX Buffer of the I2C for the DMA module.
//!
//! Returns the address of the I2C RX Buffer. This can be used in conjunction
//! with the DMA to store the received data directly to memory.
//!
//! \param baseAddress is the base address of the I2C module.
//!
//! \return The address of the I2C RX Buffer
//
//*****************************************************************************
extern uint32_t EUSCI_B_I2C_getReceiveBufferAddress(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the address of the TX Buffer of the I2C for the DMA module.
//!
//! Returns the address of the I2C TX Buffer. This can be used in conjunction
//! with the DMA to obtain transmitted data directly from memory.
//!
//! \param baseAddress is the base address of the I2C module.
//!
//! \return The address of the I2C TX Buffer
//
//*****************************************************************************
extern uint32_t EUSCI_B_I2C_getTransmitBufferAddress(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_EUSCI_B_I2C_H__
