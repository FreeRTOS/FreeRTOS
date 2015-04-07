/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \addtogroup ssc_module Working with SSC
 * The SSC driver provides the interface to configure and use the SSC
 * peripheral.
 *
 * !Usage
 *
 * -# Enable the SSC interface pins.
 * -# Configure the SSC to operate at a specific frequency by calling
 *    SSC_Configure(). This function enables the peripheral clock of the SSC,
 *    but not its PIOs.
 * -# Configure the transmitter and/or the receiver using the
 *    SSC_ConfigureTransmitter() and SSC_ConfigureEmitter() functions.
 * -# Enable the PIOs or the transmitter and/or the received.
 * -# Enable the transmitter and/or the receiver using SSC_EnableTransmitter()
 *    and SSC_EnableReceiver()
 * -# Send data through the transmitter using SSC_Write() 
 * -# Receive data from the receiver using SSC_Read() 
 * -# Disable the transmitter and/or the receiver using SSC_DisableTransmitter()
 *    and SSC_DisableReceiver()
 *
 * For more accurate information, please look at the SSC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref ssc.c\n
 * \ref ssc.h.\n
*/
/*@{*/
/*@}*/


/**
 * \file
 *
 * Implementation of Synchronous Serial (SSC) controller.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *       Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures a SSC peripheral.If the divided clock is not used, the master
 * clock frequency can be set to 0.
 * \note The emitter and transmitter are disabled by this function.
 * \param ssc  Pointer to an SSC instance.
 * \param bitRate  bit rate.
 * \param masterClock  master clock.
 */
void SSC_Configure(Ssc *ssc, uint32_t bitRate, uint32_t masterClock)
{
    uint32_t id;
    uint32_t maxClock;
    id = (ssc == SSC0 )? ID_SSC0 : ID_SSC1;
    maxClock = PMC_SetPeriMaxClock(id, masterClock);
    
    /* Reset, disable receiver & transmitter */
    ssc->SSC_CR = SSC_CR_RXDIS | SSC_CR_TXDIS | SSC_CR_SWRST;

    /* Configure clock frequency */
    if (bitRate != 0) {

        ssc->SSC_CMR = maxClock / (2 * bitRate);
    }
    else {

        ssc->SSC_CMR = 0;
    }
    /* Enable SSC peripheral clock */
    PMC_EnablePeripheral(id);
}

/**
 * \brief Configures the transmitter of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 * \param tcmr Transmit Clock Mode Register value.
 * \param tfmr Transmit Frame Mode Register value.
 */
void SSC_ConfigureTransmitter(Ssc *ssc,uint32_t tcmr, uint32_t tfmr)
{
    ssc->SSC_TCMR = tcmr;
    ssc->SSC_TFMR = tfmr;
}

/**
 * \brief Configures the receiver of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 * \param rcmr Receive Clock Mode Register value.
 * \param rfmr Receive Frame Mode Register value.
 */
void SSC_ConfigureReceiver(Ssc *ssc, uint32_t rcmr, uint32_t rfmr)
{
    ssc->SSC_RCMR = rcmr;
    ssc->SSC_RFMR = rfmr;
}

/**
 * \brief Enables the transmitter of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 */
void SSC_EnableTransmitter(Ssc *ssc)
{
    ssc->SSC_CR = SSC_CR_TXEN;
}

/**
 * \brief Disables the transmitter of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 */
void SSC_DisableTransmitter(Ssc *ssc)
{
    ssc->SSC_CR = SSC_CR_TXDIS;
}

/**
 * \brief Enables the receiver of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 */
void SSC_EnableReceiver(Ssc *ssc)
{
    ssc->SSC_CR = SSC_CR_RXEN;
}

/**
 * \brief Disables the receiver of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 */
void SSC_DisableReceiver(Ssc *ssc)
{
    ssc->SSC_CR = SSC_CR_RXDIS;
}

/**
 * \brief Enables one or more interrupt sources of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 * \param sources Bitwise OR of selected interrupt sources.
 */
void SSC_EnableInterrupts(Ssc *ssc, uint32_t sources)
{
    ssc->SSC_IER = sources;
}

/**
 * \brief Disables one or more interrupt sources of a SSC peripheral.
 * \param ssc  Pointer to an SSC instance. 
 * \param sources Bitwise OR of selected interrupt sources.
 */
void SSC_DisableInterrupts(Ssc *ssc, uint32_t sources)
{
    ssc->SSC_IDR = sources;
}

/**
 * \brief Sends one data frame through a SSC peripheral. If another frame is currently
 * being sent, this function waits for the previous transfer to complete.
 * \param ssc  Pointer to an SSC instance. 
 * \param frame Data frame to send.
 */
void SSC_Write(Ssc *ssc, uint32_t frame)
{
    while ((ssc->SSC_SR & SSC_SR_TXRDY) == 0);
    ssc->SSC_THR = frame;
}

/**
 * \brief Waits until one frame is received on a SSC peripheral, and returns it.
 * \param ssc  Pointer to an SSC instance. 
 */
uint32_t SSC_Read(Ssc *ssc)
{
    while ((ssc->SSC_SR & SSC_SR_RXRDY) == 0);
    return ssc->SSC_RHR;
}

/**
 * \brief Return 1 if one frame is received, 0 otherwise.
 * \param ssc  Pointer to an SSC instance. 
 */
uint8_t SSC_IsRxReady(Ssc *ssc)
{
    return ((ssc->SSC_SR & SSC_SR_RXRDY) > 0);
}

