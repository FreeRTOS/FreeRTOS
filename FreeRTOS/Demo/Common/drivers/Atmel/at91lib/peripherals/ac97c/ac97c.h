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


#ifndef AC97C_H
#define AC97C_H

//------------------------------------------------------------------------------
//         Constants
//------------------------------------------------------------------------------

/// The channel is already busy with a transfer.
#define AC97C_ERROR_BUSY            1
/// The transfer has been stopped by the user.
#define AC97C_ERROR_STOPPED         2

/// Codec channel index.
#define AC97C_CHANNEL_CODEC	        0
/// Channel A index.
#define AC97C_CHANNEL_A	            1
/// Channel B index.
#define AC97C_CHANNEL_B	            2

/// Codec transmit/receive transfer index.
#define AC97C_CODEC_TRANSFER        0
/// Channel A receive transfer index.
#define AC97C_CHANNEL_A_RECEIVE     1
/// Channel A transmit transfer index.
#define AC97C_CHANNEL_A_TRANSMIT    2
/// Channel B receive transfer index.
#define AC97C_CHANNEL_B_RECEIVE     3
/// Channel B transmit transfer index.
#define AC97C_CHANNEL_B_TRANSMIT    4

//------------------------------------------------------------------------------
//         Types
//------------------------------------------------------------------------------

/// AC97C transfer callback function.
typedef void (*Ac97Callback)(void *pArg,
                             unsigned char status,
                             unsigned int remaining);

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

extern void AC97C_Configure();

extern void AC97C_ConfigureChannel(unsigned char channel, unsigned int cfg);

extern void AC97C_AssignInputSlots(unsigned char channel, unsigned int slots);

extern void AC97C_AssignOutputSlots(unsigned char channel, unsigned int slots);

extern unsigned char AC97C_Transfer(
				unsigned char channel,
				unsigned char *pBuffer,
				unsigned int numSamples,
				Ac97Callback callback,
				void *pArg);

extern unsigned char AC97C_IsFinished(unsigned char channel);

extern void AC97C_WriteCodec(unsigned char address, unsigned short data);

extern unsigned short AC97C_ReadCodec(unsigned char address);

extern void AC97C_SetChannelSize(unsigned char channel, unsigned char size);

extern void AC97C_CancelTransfer(unsigned char channel);

#endif //#ifndef AC97C_H

