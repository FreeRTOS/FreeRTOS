/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support  -  ROUSSET  -
 * ----------------------------------------------------------------------------
 * Copyright (c) 2006, Atmel Corporation

 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaiimer below.
 * 
 * - Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the disclaimer below in the documentation and/or
 * other materials provided with the distribution. 
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
/// \dir
/// !Purpose
/// 
/// Interface for configuration the %DMA controller(DMAC).
///
/// !Usage
///
/// -# Enable or disable the a DMAC controller with 
///    DMA_Enable() and or DMA_Disable().
/// -# Enable or disable %Dma interrupt using DMA_EnableIt()
///    or DMA_DisableIt().
/// -# Get %Dma interrupt status by DMA_GetStatus().
/// -# Enable or disable specified %Dma channel with 
///    DMA_EnableChannel() or DMA_DisableChannel().
/// -# Get %Dma channel status by DMA_GetChannelStatus().
/// -# Configure source and/or destination start address with
///    DMA_SetSourceAddr() and/or DMA_SetDestAddr().
/// -# Set %Dma descriptor address using DMA_SetDescriptorAddr().
/// -# Set source transfer buffer size with DMA_SetSourceBufferSize().
/// -# Configure source and/or destination transfer mode with
///    DMA_SetSourceBufferMode() and/or DMA_SetDestBufferMode().
/// -# Configure source and/or destination Picture-In-Picutre 
///    mode with DMA_SPIPconfiguration() and/or DMA_DPIPconfiguration().
//------------------------------------------------------------------------------

#ifndef DMA_H
#define DMA_H

#include <board.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
#define DMA_CHANNEL_0            0
#define DMA_CHANNEL_1            1
#define DMA_CHANNEL_2            2
#define DMA_CHANNEL_3            3
#define DMA_CHANNEL_4            4
#define DMA_CHANNEL_5            5
#define DMA_CHANNEL_6            6
#define DMA_CHANNEL_7            7

#if defined(CHIP_DMA_CHANNEL_NUM)
#define DMA_CHANNEL_NUM      CHIP_DMA_CHANNEL_NUM
#endif

#define DMA_TRANSFER_SINGLE      0
#define DMA_TRANSFER_LLI         1  
#define DMA_TRANSFER_RELOAD      2
#define DMA_TRANSFER_CONTIGUOUS  3


#define DMA_ENA                  (1 << 0)
#define DMA_DIS                  (1 << 0)
#define DMA_SUSP                 (1 << 8)
#define DMA_KEEPON               (1 << 24)

#define DMA_BTC                  (1 << 0)
#define DMA_CBTC                 (1 << 8)
#define DMA_ERR                  (1 << 16)

#if defined(at91sam9m10) || defined(at91sam9m11) || defined(at91sam3u4)
    #define AT91C_SRC_DSCR AT91C_HDMA_SRC_DSCR
    #define AT91C_DST_DSCR AT91C_HDMA_DST_DSCR
    #define AT91C_SRC_INCR AT91C_HDMA_SRC_ADDRESS_MODE
    #define AT91C_DST_INCR AT91C_HDMA_DST_ADDRESS_MODE
    #define AT91C_SRC_PER  AT91C_HDMA_SRC_PER
    #define AT91C_DST_PER  AT91C_HDMA_DST_PER
    #define AT91C_SRC_REP  AT91C_HDMA_SRC_REP
    #define AT91C_DST_REP  AT91C_HDMA_DST_REP
    #define AT91C_SRC_PIP  AT91C_HDMA_SRC_PIP
    #define AT91C_DST_PIP  AT91C_HDMA_DST_PIP
    
    #define AT91C_BTC             (0xFF <<  0) 
    #define AT91C_CBTC            (0xFF <<  8) 
    #define AT91C_ERR             (0xFF << 16) 
#endif    

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

extern void DMA_Config(unsigned int flag);

extern void DMA_Enable(void);

extern void DMA_Disable(void);

extern void DMA_EnableChannel(unsigned int channel);

extern void DMA_DisableChannel(unsigned int channel);

extern void DMA_KeeponChannel(unsigned int channel);

extern void DMA_ClearAutoMode(unsigned int channel);

extern unsigned int DMA_GetChannelStatus(void);

extern unsigned int DMA_GetStatus(void);

extern unsigned int DMA_GetInterruptMask(void);

extern unsigned int DMA_GetMaskedStatus(void);

extern void DMA_EnableIt (unsigned int flag);

extern void DMA_DisableIt (unsigned int flag);

extern void DMA_SetSourceAddr(unsigned char channel, unsigned int address);

extern void DMA_SetDestinationAddr(unsigned char channel, unsigned int address);

extern void DMA_SetDescriptorAddr(unsigned char channel, unsigned int address);

extern void DMA_SetSourceBufferSize(unsigned char channel,
                             unsigned int size, 
                             unsigned char sourceWidth, 
                             unsigned char desDMAdth,
                             unsigned char done);

extern void DMA_SetSourceBufferMode(unsigned char channel, 
                             unsigned char transferMode,
                             unsigned char addressingType);
                             
extern void DMA_SetDestBufferMode(unsigned char channel, 
                             unsigned char transferMode,
                             unsigned char addressingType);
                             
extern void DMA_SetConfiguration(unsigned char channel, unsigned int value);

extern void DMA_SPIPconfiguration(unsigned char channel, 
                     unsigned int pipHole, unsigned int pipBoundary);

extern void DMA_DPIPconfiguration(unsigned char channel, 
                     unsigned int pipHole, unsigned int pipBoundary);

#endif //#ifndef DMA_H
