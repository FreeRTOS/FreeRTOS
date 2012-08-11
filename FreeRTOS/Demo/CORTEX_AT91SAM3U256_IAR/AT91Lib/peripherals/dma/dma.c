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

#include "dma.h"
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Configure a DMAC peripheral
//------------------------------------------------------------------------------
void DMA_Config(unsigned int flag)
{
    AT91C_BASE_HDMA->HDMA_GCFG = flag;
}

//------------------------------------------------------------------------------
/// Enables a DMAC peripheral
//------------------------------------------------------------------------------
void DMA_Enable(void)
{
    AT91C_BASE_HDMA->HDMA_EN = AT91C_HDMA_ENABLE;
}

//------------------------------------------------------------------------------
/// Disables DMAC peripheral
//------------------------------------------------------------------------------
void DMA_Disable(void)
{
    AT91C_BASE_HDMA->HDMA_EN = ~(AT91C_HDMA_ENABLE);
}

//-----------------------------------------------------------------------------
/// Enable DMA interrupt
/// \param flag IT to be enabled
//-----------------------------------------------------------------------------
void DMA_EnableIt (unsigned int flag)
{
    AT91C_BASE_HDMA->HDMA_EBCIER = flag;
}

//-----------------------------------------------------------------------------
/// Disable DMA interrupt
/// \param flag IT to be enabled
//-----------------------------------------------------------------------------
void DMA_DisableIt (unsigned int flag)
{
    AT91C_BASE_HDMA->HDMA_EBCIDR = flag;
}

//-----------------------------------------------------------------------------
/// Return DMA Interrupt Status
//-----------------------------------------------------------------------------
unsigned int DMA_GetStatus(void)
{
    return (AT91C_BASE_HDMA->HDMA_EBCISR);
}

//-----------------------------------------------------------------------------
/// Return DMA Interrupt Mask Status
//-----------------------------------------------------------------------------
unsigned int DMA_GetInterruptMask(void)
{
    return (AT91C_BASE_HDMA->HDMA_EBCIMR);
}

//-----------------------------------------------------------------------------
/// Returns the current status register of the given DMA peripheral, but
/// masking interrupt sources which are not currently enabled.
//-----------------------------------------------------------------------------
unsigned int DMA_GetMaskedStatus(void)
{
    unsigned int status;
    status = AT91C_BASE_HDMA->HDMA_EBCISR;
    status &= AT91C_BASE_HDMA->HDMA_EBCIMR;
    return status;
}

//------------------------------------------------------------------------------
/// Enables DMAC channel 
/// \param channel Particular channel number.
//------------------------------------------------------------------------------
void DMA_EnableChannel(unsigned int channel)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CHER |= DMA_ENA << channel;
}

//------------------------------------------------------------------------------
/// Disables a DMAC channel 
/// \param channel Particular channel number.
//------------------------------------------------------------------------------
void DMA_DisableChannel(unsigned int channel)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CHDR |= DMA_DIS << channel;
}

//------------------------------------------------------------------------------
/// Resume DMAC channel from an stall state.
/// \param channel Particular channel number.
//------------------------------------------------------------------------------
void DMA_KeeponChannel(unsigned int channel)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CHER |= DMA_KEEPON << channel;
}

//------------------------------------------------------------------------------
/// Clear automatic mode for multi-buffer transfer.
/// \param channel Particular channel number.
//------------------------------------------------------------------------------
void DMA_ClearAutoMode(unsigned int channel)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB &= 0x7FFFFFFF;
}

//------------------------------------------------------------------------------
/// Return DMAC channel status 
//------------------------------------------------------------------------------
unsigned int DMA_GetChannelStatus(void)
{
   return( AT91C_BASE_HDMA->HDMA_CHSR);
}

//-----------------------------------------------------------------------------
/// Set DMA source address used by a HDMA channel.
/// \param channel Particular channel number.
/// \param sources sources address.
//-----------------------------------------------------------------------------
void DMA_SetSourceAddr(unsigned char channel, unsigned int address)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_SADDR = address;
}

//-----------------------------------------------------------------------------
/// Set DMA destination address used by a HDMA channel.
/// \param channel Particular channel number.
/// \param sources destination address.
//-----------------------------------------------------------------------------
void DMA_SetDestinationAddr(unsigned char channel, unsigned int address)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_DADDR = address;
}

//-----------------------------------------------------------------------------
/// Set DMA descriptor address used by a HDMA channel.
/// \param channel Particular channel number.
/// \param sources destination address.
//-----------------------------------------------------------------------------
void DMA_SetDescriptorAddr(unsigned char channel, unsigned int address)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_DSCR = address ;
}


//-----------------------------------------------------------------------------
/// Set DMA control A register used by a HDMA channel.
/// \param channel Particular channel number.
/// \param size Dma transfer size in byte.
/// \param sourceWidth Single transfer width for source.
/// \param destWidth Single transfer width for destination.
/// \param done Transfer done field.
//-----------------------------------------------------------------------------
void DMA_SetSourceBufferSize(unsigned char channel,
                             unsigned int size, 
                             unsigned char sourceWidth, 
                             unsigned char destWidth,
                             unsigned char done)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    ASSERT(sourceWidth < 4, "width does not support");
    ASSERT(destWidth < 4, "width does not support");
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLA = (size |
                                                   sourceWidth << 24 |
                                                   destWidth << 28 |
                                                   done << 31);
}
                                
//-----------------------------------------------------------------------------
/// Set DMA transfer mode for source used by a HDMA channel.
/// \param channel Particular channel number.
/// \param transferMode Transfer buffer mode (single, LLI, reload or contiguous)
/// \param addressingType Type of addrassing mode
///                       0 : incrementing, 1: decrementing, 2: fixed.
//-----------------------------------------------------------------------------
void DMA_SetSourceBufferMode(unsigned char channel, 
                             unsigned char transferMode,
                             unsigned char addressingType)
{
    unsigned int value;
    
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    
    value = AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB;
    value &= ~ (AT91C_SRC_DSCR | AT91C_SRC_INCR | 1<<31);
    switch(transferMode){
        case DMA_TRANSFER_SINGLE:
             value |= AT91C_SRC_DSCR | addressingType << 24;
             break;
        case DMA_TRANSFER_LLI:
             value |= addressingType << 24;
             break;
        case DMA_TRANSFER_RELOAD:
        case DMA_TRANSFER_CONTIGUOUS:
             value |= AT91C_SRC_DSCR | addressingType << 24 | 1<<31;
             break;
    }             
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB = value;
    
    if(transferMode == DMA_TRANSFER_RELOAD || transferMode == DMA_TRANSFER_CONTIGUOUS){
        value = AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CFG;
        value &= ~ (AT91C_SRC_REP);
        // When automatic mode is activated, the source address and the control register are reloaded from previous transfer.
        if(transferMode == DMA_TRANSFER_RELOAD) {
            value |= AT91C_SRC_REP;
        }
        AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CFG = value;
    }
    else {
        AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CFG = 0;
    }
}

//-----------------------------------------------------------------------------
/// Set DMA transfer mode for destination used by a HDMA channel.
/// \param channel Particular channel number.
/// \param transferMode Transfer buffer mode (single, LLI, reload or contiguous)
/// \param addressingType Type of addrassing mode
///                       0 : incrementing, 1: decrementing, 2: fixed.
//-----------------------------------------------------------------------------
void DMA_SetDestBufferMode(unsigned char channel, 
                             unsigned char transferMode,
                             unsigned char addressingType)
{
    unsigned int value;
    
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    
    value = AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB;
    value &= ~ (AT91C_DST_DSCR | AT91C_DST_INCR);
    
    switch(transferMode){
        case DMA_TRANSFER_SINGLE:
        case DMA_TRANSFER_RELOAD:
        case DMA_TRANSFER_CONTIGUOUS:
             value |= AT91C_DST_DSCR | addressingType << 24;
             break;
        case DMA_TRANSFER_LLI:
             value |= addressingType << 24;
             break;
    }             
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB = value;
    if(transferMode == DMA_TRANSFER_RELOAD || transferMode == DMA_TRANSFER_CONTIGUOUS){
        value = AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CFG;
        value &= ~ (AT91C_DST_REP);
        // When automatic mode is activated, the source address and the control register are reloaded from previous transfer.
        if(transferMode == DMA_TRANSFER_RELOAD) {
            value |= AT91C_DST_REP;
        }
        AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CFG = value;
    }
    else {
        AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CFG = 0;
    }
}

//------------------------------------------------------------------------------
/// Set DMA configuration registe used by a HDMA channel.
/// \param channel Particular channel number.
/// \param value configuration value.
//------------------------------------------------------------------------------
void DMA_SetConfiguration(unsigned char channel, unsigned int value)
{
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CFG = value;
}

//------------------------------------------------------------------------------
/// Set DMA source PIP configuration used by a HDMA channel.
/// \param channel Particular channel number.
/// \param pipHole stop on done mode.
/// \param pipBoundary lock mode.
//------------------------------------------------------------------------------
void DMA_SPIPconfiguration(unsigned char channel, 
                           unsigned int pipHole, 
                           unsigned int pipBoundary)
                     
{
    unsigned int value;
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    value = AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB;
    value &= ~ (AT91C_SRC_PIP);
    value |= AT91C_SRC_PIP;
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB = value;
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_SPIP = (pipHole + 1) | pipBoundary <<16;
}

//------------------------------------------------------------------------------
/// Set DMA destination PIP configuration used by a HDMA channel.
/// \param channel Particular channel number.
/// \param pipHole stop on done mode.
/// \param pipBoundary lock mode.
//------------------------------------------------------------------------------
void DMA_DPIPconfiguration(unsigned char channel, 
                           unsigned int pipHole, 
                           unsigned int pipBoundary)
                     
{
    unsigned int value;
    ASSERT(channel < DMA_CHANNEL_NUM, "this channel does not exist");
    value = AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB;
    value &= ~ (AT91C_DST_PIP);
    value |= AT91C_DST_PIP;
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_CTRLB = value;
    AT91C_BASE_HDMA->HDMA_CH[channel].HDMA_DPIP = (pipHole + 1) | pipBoundary <<16;
}

