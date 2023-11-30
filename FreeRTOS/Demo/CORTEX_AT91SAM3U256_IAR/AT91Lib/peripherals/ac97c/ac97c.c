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

#include "ac97c.h"
#include <board.h>
#include <aic/aic.h>
#include <utility/assert.h>
#include <utility/trace.h>
#include <utility/math.h>

//------------------------------------------------------------------------------
//         Local constants
//------------------------------------------------------------------------------

/// Maximum size of one PDC buffer (in bytes).
#define MAX_PDC_COUNTER 65535

//------------------------------------------------------------------------------
//         Local types
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// AC97 transfer descriptor. Tracks the status and parameters of a transfer
/// on the AC97 bus.
//------------------------------------------------------------------------------
typedef struct _Ac97Transfer {

    /// Buffer containing the slots to send.
    unsigned char *pBuffer;
    /// Total number of samples to send.
    volatile unsigned int numSamples;
    /// Optional callback function.
    Ac97Callback callback;
    /// Optional argument to the callback function.
    void *pArg;

} Ac97Transfer;

//------------------------------------------------------------------------------
/// AC97 controller driver structure. Monitors the status of transfers on all
/// AC97 channels.
//------------------------------------------------------------------------------
typedef struct _Ac97c {

    /// List of transfers occuring on each channel.
    Ac97Transfer transfers[5];
} Ac97c;

//------------------------------------------------------------------------------
//         Local variables
//------------------------------------------------------------------------------

/// Global AC97 controller instance.
static Ac97c ac97c;

//------------------------------------------------------------------------------
//         Local functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Returns the size of one sample (in bytes) on the given channel.
/// \param channel  Channel number.
//------------------------------------------------------------------------------
static unsigned char GetSampleSize(unsigned char channel)
{
    unsigned int size = 0;

    SANITY_CHECK((channel == AC97C_CHANNEL_A)
                 || (channel == AC97C_CHANNEL_B)
                 || (channel == AC97C_CHANNEL_CODEC));

    // Check selected channel
    switch (channel) {
        case AC97C_CHANNEL_CODEC: return 2;

        case AC97C_CHANNEL_A:
            size = (AT91C_BASE_AC97C->AC97C_CAMR & AT91C_AC97C_SIZE) >> 16;
            break;

        case AC97C_CHANNEL_B:
            size = (AT91C_BASE_AC97C->AC97C_CBMR & AT91C_AC97C_SIZE) >> 16;
            break;
    }

    // Compute size in bytes given SIZE field
    if ((size & 2) != 0) {

        return 2;
    }
    else {

        return 4;
    }
}

//------------------------------------------------------------------------------
/// Interrupt service routine for Codec, is invoked by AC97C_Handler.
//------------------------------------------------------------------------------
static void CodecHandler(void)
{
    unsigned int status;
    unsigned int data;
    Ac97Transfer *pTransfer = &(ac97c.transfers[AC97C_CODEC_TRANSFER]);

    // Read CODEC status register
    status = AT91C_BASE_AC97C->AC97C_COSR;
    status &= AT91C_BASE_AC97C->AC97C_COMR;

    // A sample has been transmitted
    if (status & AT91C_AC97C_TXRDY) {

        pTransfer->numSamples--;

        // If there are remaining samples, transmit one
        if (pTransfer->numSamples > 0) {

            data = *((unsigned int *) pTransfer->pBuffer);
            AT91C_BASE_AC97C->AC97C_COMR &= ~(AT91C_AC97C_TXRDY);
            AT91C_BASE_AC97C->AC97C_COTHR = data;

            // Check if transfer is read or write
            if ((data & AT91C_AC97C_READ) != 0) {
    
                AT91C_BASE_AC97C->AC97C_COMR |= AT91C_AC97C_RXRDY;
            }
            else {
            
                pTransfer->pBuffer += sizeof(unsigned int);
                AT91C_BASE_AC97C->AC97C_COMR |= AT91C_AC97C_TXRDY;
            }
        }
        // Transfer finished
        else {

            AT91C_BASE_AC97C->AC97C_IDR = AT91C_AC97C_COEVT;
            AT91C_BASE_AC97C->AC97C_COMR &= ~(AT91C_AC97C_TXRDY);
            if (pTransfer->callback) {

                pTransfer->callback(pTransfer->pArg, 0, 0);
            }
        }   
    }

    // A sample has been received
    if (status & AT91C_AC97C_RXRDY) {

        // Store sample
        data = AT91C_BASE_AC97C->AC97C_CORHR;
        *((unsigned int *) pTransfer->pBuffer) = data;

        pTransfer->pBuffer += sizeof(unsigned int);
        pTransfer->numSamples--;

        // Transfer finished
        if (pTransfer->numSamples > 0) {

            data = *((unsigned int *) pTransfer->pBuffer);
            AT91C_BASE_AC97C->AC97C_COMR &= ~(AT91C_AC97C_RXRDY);
            AT91C_BASE_AC97C->AC97C_COTHR = data;

            // Check if transfer is read or write
            if ((data & AT91C_AC97C_READ) != 0) {
    
                AT91C_BASE_AC97C->AC97C_COMR |= AT91C_AC97C_RXRDY;
            }
            else {
            
                pTransfer->pBuffer += sizeof(unsigned int);
                AT91C_BASE_AC97C->AC97C_COMR |= AT91C_AC97C_TXRDY;
            }
        }
        else {

            AT91C_BASE_AC97C->AC97C_IDR = AT91C_AC97C_COEVT;
            AT91C_BASE_AC97C->AC97C_COMR &= ~(AT91C_AC97C_RXRDY);
            if (pTransfer->callback) {

                pTransfer->callback(pTransfer->pArg, 0, 0);
            }
        }
    }
}

//------------------------------------------------------------------------------
/// Interrupt service routine for channel A, is invoked by AC97C_Handler.
//------------------------------------------------------------------------------
static void ChannelAHandler(void)
{
    unsigned int status;
    Ac97Transfer *pTransmit = &(ac97c.transfers[AC97C_CHANNEL_A_TRANSMIT]);
    Ac97Transfer *pReceive = &(ac97c.transfers[AC97C_CHANNEL_A_RECEIVE]);

    // Read channel A status register
    status = AT91C_BASE_AC97C->AC97C_CASR;

    // A buffer has been transmitted
    if ((status & AT91C_AC97C_ENDTX) != 0) {

        // Update transfer information
        if (pTransmit->numSamples > MAX_PDC_COUNTER) {

            pTransmit->numSamples -= MAX_PDC_COUNTER;
        }
        else {

            pTransmit->numSamples = 0;
        }

        // Transmit new buffers if necessary
        if (pTransmit->numSamples > MAX_PDC_COUNTER) {

            // Fill next PDC
            AT91C_BASE_AC97C->AC97C_TNPR = (unsigned int) pTransmit->pBuffer;
            if (pTransmit->numSamples > 2 * MAX_PDC_COUNTER) {

                AT91C_BASE_AC97C->AC97C_TNCR = MAX_PDC_COUNTER;
                pTransmit->pBuffer += MAX_PDC_COUNTER
                                            * GetSampleSize(AC97C_CHANNEL_A);
            }
            else {

                AT91C_BASE_AC97C->AC97C_TNCR = pTransmit->numSamples
                                                            - MAX_PDC_COUNTER;
            }
        }
        // Only one buffer remaining
        else {

            AT91C_BASE_AC97C->AC97C_CAMR &= ~AT91C_AC97C_ENDTX;
            AT91C_BASE_AC97C->AC97C_CAMR |= AT91C_AC97C_TXBUFE;
        }
    }

    // Transmit completed
    if ((status & AT91C_AC97C_TXBUFE) != 0) {

        pTransmit->numSamples = 0;
        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_TXTDIS;
        AT91C_BASE_AC97C->AC97C_CAMR &= ~AT91C_AC97C_TXBUFE;
        if (pTransmit->callback) {

            pTransmit->callback(pTransmit->pArg, 0, 0);
        }
    }

    // A buffer has been received
    if (status & AT91C_AC97C_ENDRX) {

        if (pReceive->numSamples > MAX_PDC_COUNTER) {
        
            pReceive->numSamples -= MAX_PDC_COUNTER;
        }
        else {

            pReceive->numSamples = 0;
        }

        // Transfer remaining samples
        if (pReceive->numSamples > MAX_PDC_COUNTER) {

            AT91C_BASE_AC97C->AC97C_RNPR = (unsigned int) pReceive->pBuffer;
            if (pReceive->numSamples > 2 * MAX_PDC_COUNTER) {
            
                AT91C_BASE_AC97C->AC97C_RNCR = MAX_PDC_COUNTER;
                pReceive->pBuffer += MAX_PDC_COUNTER
                                            * GetSampleSize(AC97C_CHANNEL_A);
            }
            else {

                AT91C_BASE_AC97C->AC97C_RNCR = pReceive->numSamples 
                                                            - MAX_PDC_COUNTER;
            }
        }
        // Only one buffer remaining
        else {

            AT91C_BASE_AC97C->AC97C_CAMR &= ~(AT91C_AC97C_ENDRX);
            AT91C_BASE_AC97C->AC97C_CAMR |= AT91C_AC97C_RXBUFF;
        }
    }

    // Receive complete
    if ((status & AT91C_AC97C_RXBUFF) != 0) {

        pReceive->numSamples = 0;
        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_RXTDIS;
        AT91C_BASE_AC97C->AC97C_CAMR &= ~AT91C_AC97C_RXBUFF;
        if (pReceive->callback) {

            pReceive->callback(pReceive->pArg, 0, 0);
        }
    }
}

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// This handler function must be called by the AC97C interrupt service routine.
/// Identifies which event was activated and calls the associated function.
//------------------------------------------------------------------------------ 
void AC97C_Handler(void)
{
    unsigned int status;

    // Get the real interrupt source
    status = AT91C_BASE_AC97C->AC97C_SR;
    status &= AT91C_BASE_AC97C->AC97C_IMR;
    
    // Check if an event on the codec channel is active
    if ((status & AT91C_AC97C_COEVT) != 0) {

        CodecHandler();    
    }
    // Check if an event on channel A is active
    if ((status & AT91C_AC97C_CAEVT) != 0) {

        ChannelAHandler();  
    }
}

//------------------------------------------------------------------------------
/// Starts a read or write transfer on the given channel
/// \param channel particular channel (AC97C_CODEC_TRANSFER, 
///                AC97C_CHANNEL_A_RECEIVE, AC97C_CHANNEL_A_TRANSMIT,
///                AC97C_CHANNEL_B_RECEIVE or AC97C_CHANNEL_B_TRANSMIT).
/// \param pBuffer buffer containing the slots to send.
/// \param numSamples total number of samples to send.  
/// \param callback optional callback function.
/// \param pArg optional argument to the callback function.
//------------------------------------------------------------------------------
unsigned char AC97C_Transfer(
    unsigned char channel,
    unsigned char *pBuffer,
    unsigned int numSamples,
    Ac97Callback callback,
    void *pArg)
{
    unsigned int size;
    unsigned int data;
    Ac97Transfer *pTransfer;

    SANITY_CHECK(channel <= 5);
    SANITY_CHECK(pBuffer);
    SANITY_CHECK(numSamples > 0);

    // Check that no transfer is pending on the channel
    pTransfer = &(ac97c.transfers[channel]);
    if (pTransfer->numSamples > 0) {

        TRACE_WARNING(
            "AC97C_Transfer: Channel %d is busy\n\r", channel);
        return AC97C_ERROR_BUSY;
    }

    // Fill transfer information
    pTransfer->pBuffer = pBuffer;
    pTransfer->numSamples = numSamples;
    pTransfer->callback = callback;
    pTransfer->pArg = pArg;

    // Transmit or receive over codec channel
    if (channel == AC97C_CODEC_TRANSFER) {

        // Send command
        data = *((unsigned int *) pTransfer->pBuffer); 
        AT91C_BASE_AC97C->AC97C_COTHR = data;

        // Check if transfer is read or write
        if ((data & AT91C_AC97C_READ) != 0) {

            AT91C_BASE_AC97C->AC97C_COMR |= AT91C_AC97C_RXRDY;
        }
        else {
        
            pTransfer->pBuffer += sizeof(unsigned int);
            AT91C_BASE_AC97C->AC97C_COMR |= AT91C_AC97C_TXRDY;
        }

        // Enable interrupts
        AT91C_BASE_AC97C->AC97C_IER |= AT91C_AC97C_COEVT;
    }
    // Transmit over channel A
    else if (channel == AC97C_CHANNEL_A_TRANSMIT) {

        // Disable PDC
        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_TXTDIS;

        // Fill PDC buffers
        size = min(pTransfer->numSamples, MAX_PDC_COUNTER);
        AT91C_BASE_AC97C->AC97C_TPR = (unsigned int) pTransfer->pBuffer;
        AT91C_BASE_AC97C->AC97C_TCR = size;
        pTransfer->pBuffer += size * GetSampleSize(AC97C_CHANNEL_A);

        size = min(pTransfer->numSamples - size, MAX_PDC_COUNTER);
        if (size > 0) {

            AT91C_BASE_AC97C->AC97C_TNPR = (unsigned int) pTransfer->pBuffer;
            AT91C_BASE_AC97C->AC97C_TNCR = size;
            pTransfer->pBuffer += size * GetSampleSize(AC97C_CHANNEL_A);
        }

        // Enable interrupts
        AT91C_BASE_AC97C->AC97C_CAMR |= AT91C_AC97C_PDCEN | AT91C_AC97C_ENDTX;
        AT91C_BASE_AC97C->AC97C_IER |= AT91C_AC97C_CAEVT;

        // Start transfer
        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_TXTEN;
    }
    // Receive over channel A
    else if (channel == AC97C_CHANNEL_A_RECEIVE) {

        // Disable PDC
        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_RXTDIS;

        // Fill PDC buffers
        size = min(pTransfer->numSamples, MAX_PDC_COUNTER);
        AT91C_BASE_AC97C->AC97C_RPR = (unsigned int) pTransfer->pBuffer;
        AT91C_BASE_AC97C->AC97C_RCR = size;
        pTransfer->pBuffer += size * GetSampleSize(AC97C_CHANNEL_A);

        size = min(pTransfer->numSamples - size, MAX_PDC_COUNTER);
        if (size > 0) {

            AT91C_BASE_AC97C->AC97C_RNPR = (unsigned int) pTransfer->pBuffer;
            AT91C_BASE_AC97C->AC97C_RNCR = size;
            pTransfer->pBuffer += size * GetSampleSize(AC97C_CHANNEL_A);
        }

        // Enable interrupts
        AT91C_BASE_AC97C->AC97C_CAMR |= AT91C_AC97C_PDCEN | AT91C_AC97C_ENDRX;
        AT91C_BASE_AC97C->AC97C_IER |= AT91C_AC97C_CAEVT;

        // Start transfer
        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_RXTEN;
    }

    return 0;
}

//------------------------------------------------------------------------------
/// Stop read or write transfer on the given channel.
/// \param channel  Channel number.
//------------------------------------------------------------------------------
void AC97C_CancelTransfer(unsigned char channel)
{    
    unsigned int size = 0;
    Ac97Transfer *pTransfer;

    SANITY_CHECK(channel <= AC97C_CHANNEL_B_TRANSMIT);

    // Save remaining size
    pTransfer = &(ac97c.transfers[channel]);
    size = pTransfer->numSamples;
    pTransfer->numSamples = 0;

    // Stop PDC
    if (channel == AC97C_CHANNEL_A_TRANSMIT) {

        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_TXTDIS;
        size -= min(size, MAX_PDC_COUNTER) - AT91C_BASE_AC97C->AC97C_TCR;
    }
    if (channel == AC97C_CHANNEL_A_RECEIVE) {

        AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_RXTDIS;
        size -= min(size, MAX_PDC_COUNTER) - AT91C_BASE_AC97C->AC97C_RCR;
    }

    // Invoke callback if provided
    if (pTransfer->callback) {

        pTransfer->callback(pTransfer->pArg, AC97C_ERROR_STOPPED, size);
    }
}

//------------------------------------------------------------------------------
/// Initializes the AC97 controller.
//------------------------------------------------------------------------------
void AC97C_Configure(void)
{
    unsigned char channel;

    // Enable the AC97 controller peripheral clock
    AT91C_BASE_PMC->PMC_PCER = (1 << AT91C_ID_AC97C);   
    
    // Enable the peripheral and variable rate adjustment
    AT91C_BASE_AC97C->AC97C_MR = AT91C_AC97C_ENA  | AT91C_AC97C_VRA;

    // Unassigns all input & output slots
    AC97C_AssignInputSlots(0, 0xFFFF);
    AC97C_AssignOutputSlots(0, 0xFFFF);

    // Install the AC97C interrupt handler
    AT91C_BASE_AC97C->AC97C_IDR = 0xFFFFFFFF;
    AIC_ConfigureIT(AT91C_ID_AC97C, 0, AC97C_Handler);
    AIC_EnableIT(AT91C_ID_AC97C);  

    // Disable PDC transfers
    AT91C_BASE_AC97C->AC97C_PTCR = AT91C_PDC_TXTDIS | AT91C_PDC_RXTDIS;

    // Clear channel transfers
    for (channel = 0; channel < AC97C_CHANNEL_B_TRANSMIT; channel++) {

        ac97c.transfers[channel].numSamples = 0;
    }
}

//------------------------------------------------------------------------------
/// Configures the desired channel with the given value.
/// \param channel  Channel number.
/// \param cfg  Configuration value.
//------------------------------------------------------------------------------
void AC97C_ConfigureChannel(unsigned char channel, unsigned int cfg)
{
    SANITY_CHECK((channel == AC97C_CHANNEL_A) || (channel == AC97C_CHANNEL_B));

    if (channel == AC97C_CHANNEL_A) {

        AT91C_BASE_AC97C->AC97C_CAMR = cfg;
    }
    else {

        AT91C_BASE_AC97C->AC97C_CBMR = cfg;
    }
}

//------------------------------------------------------------------------------
/// Assigns the desired input slots to a particular channel.
/// \param channel  Channel number (or 0 to unassign slots).
/// \param slots  Bitfield value of slots to assign.
//------------------------------------------------------------------------------
void AC97C_AssignInputSlots(unsigned char channel, unsigned int slots)
{
    unsigned int value;
    unsigned int i;

    SANITY_CHECK(channel <= AC97C_CHANNEL_B);

    // Assign all slots
    slots >>= 3;
    for (i = 3; i < 15; i++) {

        // Check if slots is selected
        if (slots & 1) {

            value = AT91C_BASE_AC97C->AC97C_ICA;
            value &= ~(0x07 << ((i - 3) * 3));
            value |= channel << ((i - 3) * 3);
            AT91C_BASE_AC97C->AC97C_ICA = value;
        }
        slots >>= 1;
    }
}

//------------------------------------------------------------------------------
/// Assigns the desired output slots to a particular channel.
/// \param channel  Channel number (or 0 to unassign slots).
/// \param slots  Bitfield value of slots to assign.
//------------------------------------------------------------------------------
void AC97C_AssignOutputSlots(unsigned char channel, unsigned int slots)
{
    unsigned int value;
    unsigned int i;

    SANITY_CHECK(channel <= AC97C_CHANNEL_B);

    // Assign all slots
    slots >>= 3;
    for (i = 3; i < 15; i++) {

        // Check if slots is selected
        if (slots & 1) {

            value = AT91C_BASE_AC97C->AC97C_OCA;
            value &= ~(0x07 << ((i - 3) * 3));
            value |= channel << ((i - 3) * 3);
            AT91C_BASE_AC97C->AC97C_OCA = value;
        }
        slots >>= 1;
    }
}

//------------------------------------------------------------------------------
/// Returns 1 if no transfer is currently pending on the given channel;
/// otherwise, returns 0.
/// \param channel  Channel number.
//------------------------------------------------------------------------------
unsigned char AC97C_IsFinished(unsigned char channel)
{
    SANITY_CHECK(channel <= AC97C_CHANNEL_B_TRANSMIT);

    if (ac97c.transfers[channel].numSamples > 0) {

        return 0;
    }
    else {

        return 1;
    }
}

//------------------------------------------------------------------------------
/// Convenience function for synchronously sending commands to the codec.
/// \param address  Register address.
/// \param data  Command data.
//------------------------------------------------------------------------------
void AC97C_WriteCodec(unsigned char address, unsigned short data)
{
    unsigned int sample;

    sample = (address << 16) | data;
    AC97C_Transfer(AC97C_CODEC_TRANSFER, (unsigned char *) &sample, 1, 0, 0);
    while (!AC97C_IsFinished(AC97C_CODEC_TRANSFER));
}

//------------------------------------------------------------------------------
/// Convenience function for receiving data from the AC97 codec.
/// \param address  Register address.
//------------------------------------------------------------------------------
unsigned short AC97C_ReadCodec(unsigned char address)
{
    unsigned int sample;

    sample = AT91C_AC97C_READ | (address << 16);
    AC97C_Transfer(AC97C_CODEC_TRANSFER, (unsigned char *) &sample, 1, 0, 0);
    while (!AC97C_IsFinished(AC97C_CODEC_TRANSFER));

    return sample;
}
            
//------------------------------------------------------------------------------
/// Sets the size in bits of one sample on the given channel.
/// \param channel  Channel number.
/// \param size  Size of one sample in bits (10, 16, 18 or 24).
//------------------------------------------------------------------------------
void AC97C_SetChannelSize(unsigned char channel, unsigned char size)
{
    unsigned int bits = 0;

    SANITY_CHECK((size == 10) || (size == 16) || (size == 18) || (size == 24));
    SANITY_CHECK((channel == AC97C_CHANNEL_A) || (channel == AC97C_CHANNEL_B));

    switch (size) {

        case 10 : bits = AT91C_AC97C_SIZE_10_BITS; break;
        case 16 : bits = AT91C_AC97C_SIZE_16_BITS; break;
        case 18 : bits = AT91C_AC97C_SIZE_18_BITS; break;
        case 20 : bits = AT91C_AC97C_SIZE_20_BITS; break;
    }

    if (channel == AC97C_CHANNEL_A) {

        AT91C_BASE_AC97C->AC97C_CAMR &= ~(AT91C_AC97C_SIZE);
        AT91C_BASE_AC97C->AC97C_CAMR |= bits;
    }
    else {

        AT91C_BASE_AC97C->AC97C_CBMR &= ~(AT91C_AC97C_SIZE);
        AT91C_BASE_AC97C->AC97C_CBMR |= bits;
    }
}

