/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "ssc.h"
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// Configures a SSC peripheral. If the divided clock is not used, the master
/// clock frequency can be set to 0.
/// \note The emitter and transmitter are disabled by this function.
/// \param ssc  Pointer to an AT91S_SSC instance.
/// \param id  Peripheral ID of the SSC.
//------------------------------------------------------------------------------
void SSC_Configure(AT91S_SSC *ssc,
                          unsigned int id,
                          unsigned int bitRate,
                          unsigned int masterClock)
{
    // Enable SSC peripheral clock
    AT91C_BASE_PMC->PMC_PCER = 1 << id;

    // Reset, disable receiver & transmitter
    ssc->SSC_CR = AT91C_SSC_RXDIS | AT91C_SSC_TXDIS | AT91C_SSC_SWRST;
    ssc->SSC_PTCR = AT91C_PDC_RXTDIS | AT91C_PDC_TXTDIS;

    // Configure clock frequency
    if (bitRate != 0) {
    
        ssc->SSC_CMR = masterClock / (2 * bitRate);
    }
    else {

        ssc->SSC_CMR = 0;
    }
}

//------------------------------------------------------------------------------
/// Configures the transmitter of a SSC peripheral. Several macros can be used
/// to compute the values of the Transmit Clock Mode Register (TCMR) and the
/// Transmit Frame Mode Register (TFMR) (see "SSC configuration macros").
/// \param ssc  Pointer to a AT91S_SSC instance.
/// \param tcmr  Transmit Clock Mode Register value.
/// \param tfmr  Transmit Frame Mode Register value.
//------------------------------------------------------------------------------
void SSC_ConfigureTransmitter(AT91S_SSC *ssc,
                                     unsigned int tcmr,
                                     unsigned int tfmr)
{
    ssc->SSC_TCMR = tcmr;
    ssc->SSC_TFMR = tfmr;
}

//------------------------------------------------------------------------------
/// Configures the receiver of a SSC peripheral. Several macros can be used
/// to compute the values of the Receive Clock Mode Register (TCMR) and the
/// Receive Frame Mode Register (TFMR) (see "SSC configuration macros").
/// \param ssc  Pointer to a AT91S_SSC instance.
/// \param rcmr  Receive Clock Mode Register value.
/// \param rfmr  Receive Frame Mode Register value.
//------------------------------------------------------------------------------
void SSC_ConfigureReceiver(AT91S_SSC *ssc,
                                  unsigned int rcmr,
                                  unsigned int rfmr)
{
    ssc->SSC_RCMR = rcmr;
    ssc->SSC_RFMR = rfmr;
}

//------------------------------------------------------------------------------
/// Enables the transmitter of a SSC peripheral.
/// \param ssc  Pointer to an AT91S_SSC instance.
//------------------------------------------------------------------------------
void SSC_EnableTransmitter(AT91S_SSC *ssc)
{
    ssc->SSC_CR = AT91C_SSC_TXEN;
}

//------------------------------------------------------------------------------
/// Disables the transmitter of a SSC peripheral.
/// \param ssc  Pointer to an AT91S_SSC instance.
//------------------------------------------------------------------------------
void SSC_DisableTransmitter(AT91S_SSC *ssc)
{
    ssc->SSC_CR = AT91C_SSC_TXDIS;
}

//------------------------------------------------------------------------------
/// Enables the receiver of a SSC peripheral.
/// \param ssc  Pointer to an AT91S_SSC instance.
//------------------------------------------------------------------------------
void SSC_EnableReceiver(AT91S_SSC *ssc)
{
    ssc->SSC_CR = AT91C_SSC_RXEN;
}

//------------------------------------------------------------------------------
/// Disables the receiver of a SSC peripheral.
/// \param ssc  Pointer to an AT91S_SSC instance.
//------------------------------------------------------------------------------
void SSC_DisableReceiver(AT91S_SSC *ssc)
{
    ssc->SSC_CR = AT91C_SSC_RXDIS;
}

//------------------------------------------------------------------------------
/// Enables one or more interrupt sources of a SSC peripheral.
/// \param ssc  Pointer to an AT91S_SSC instance.
/// \param sources  Interrupt sources to enable.
//------------------------------------------------------------------------------
void SSC_EnableInterrupts(AT91S_SSC *ssc, unsigned int sources)
{
    ssc->SSC_IER = sources;
}

//------------------------------------------------------------------------------
/// Disables one or more interrupt sources of a SSC peripheral.
/// \param ssc  Pointer to an AT91S_SSC instance.
/// \param sources  Interrupt source to disable.
//------------------------------------------------------------------------------
void SSC_DisableInterrupts(AT91S_SSC *ssc, unsigned int sources)
{
    ssc->SSC_IDR = sources;
}

//------------------------------------------------------------------------------
/// Sends one data frame through a SSC peripheral. If another frame is currently
/// being sent, this function waits for the previous transfer to complete.
/// \param ssc  Pointer to an AT91S_SSC instance.
/// \param frame  Data frame to send.
//------------------------------------------------------------------------------
void SSC_Write(AT91S_SSC *ssc, unsigned int frame)
{
    while ((ssc->SSC_SR & AT91C_SSC_TXRDY) == 0);
    ssc->SSC_THR = frame;
}

//------------------------------------------------------------------------------
/// Sends the contents of a data buffer a SSC peripheral, using the PDC. Returns
/// true if the buffer has been queued for transmission; otherwise returns
/// false.
/// \param ssc  Pointer to an AT91S_SSC instance.
/// \param buffer  Data buffer to send.
/// \param length  Size of the data buffer.
//------------------------------------------------------------------------------
unsigned char SSC_WriteBuffer(AT91S_SSC *ssc,
                                     void *buffer,
                                     unsigned int length)
{
    // Check if first bank is free
    if (ssc->SSC_TCR == 0) {

        ssc->SSC_TPR = (unsigned int) buffer;
        ssc->SSC_TCR = length;
        ssc->SSC_PTCR = AT91C_PDC_TXTEN;
        return 1;
    }
    // Check if second bank is free
    else if (ssc->SSC_TNCR == 0) {

        ssc->SSC_TNPR = (unsigned int) buffer;
        ssc->SSC_TNCR = length;
        return 1;
    }
      
    // No free banks
    return 0;
}

//------------------------------------------------------------------------------
/// Waits until one frame is received on a SSC peripheral, and returns it.
/// \param ssc  Pointer to an AT91S_SSC instance.
//------------------------------------------------------------------------------
unsigned int SSC_Read(AT91S_SSC *ssc)
{
    while ((ssc->SSC_SR & AT91C_SSC_RXRDY) == 0);
    return ssc->SSC_RHR;
}

//------------------------------------------------------------------------------
/// Reads data coming from a SSC peripheral receiver and stores it into the
/// provided buffer. Returns true if the buffer has been queued for reception;
/// otherwise returns false.
/// \param ssc  Pointer to an AT91S_SSC instance.
/// \param buffer  Data buffer used for reception.
/// \param length  Size in bytes of the data buffer.
//------------------------------------------------------------------------------
unsigned char SSC_ReadBuffer(AT91S_SSC *ssc,
                                    void *buffer,
                                    unsigned int length)
{
    // Check if the first bank is free
    if (ssc->SSC_RCR == 0) {

        ssc->SSC_RPR = (unsigned int) buffer;
        ssc->SSC_RCR = length;
        ssc->SSC_PTCR = AT91C_PDC_RXTEN;
        return 1;
    }
    // Check if second bank is free
    else if (ssc->SSC_RNCR == 0) {

        ssc->SSC_RNPR = (unsigned int) buffer;
        ssc->SSC_RNCR = length;
        return 1;
    }

    // No free bank
    return 0;
}

