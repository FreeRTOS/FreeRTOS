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
/// \unit
///
/// !Purpose
/// 
/// Interface for configuration the Image Sensor Interface (ISI) peripheral.
/// 
/// !Usage
/// 
/// -# ISI_Init: initialize ISI with default parameters
/// -# ISI_EnableInterrupt: enable one or more interrupts
/// -# ISI_DisableInterrupt: disable one or more interrupts
/// -# ISI_Enable: enable isi module
/// -# ISI_Disable: disable isi module
/// -# ISI_CodecPathFull: enable codec path
/// -# ISI_SetFrame: set frame rate
/// -# ISI_BytesForOnePixel: return number of byte for one pixel
/// -# ISI_StatusRegister: return ISI status register
/// -# ISI_Reset: make a software reset
//------------------------------------------------------------------------------

#ifndef ISI_H
#define ISI_H

//------------------------------------------------------------------------------
//         Types
//------------------------------------------------------------------------------

/// ISI descriptors
typedef struct
{
    /// Current LCD index, used with AT91C_ISI_MAX_PREV_BUFFER
    unsigned int CurrentLcdIndex;
    /// set if Fifo Codec Empty is present
    volatile unsigned int DisplayCodec;
    /// upgrade for each Fifo Codec Overflow (statistics use)
    unsigned int nb_codec_ovf;
    /// upgrade for each Fifo Preview Overflow (statistics use)
    unsigned int nb_prev_ovf;
}ISI_Descriptors;

/// Frame Buffer Descriptors
typedef struct
{
    /// Address of the Current FrameBuffer
    unsigned int Current;
#if defined (BOARD_ISI_V200)
    /// Address of the Control
    unsigned int Control;
#endif
    /// Address of the Next FrameBuffer
    unsigned int Next;
}ISI_FrameBufferDescriptors;

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
extern void ISI_Enable(void);
extern void ISI_Disable(void);
extern void ISI_EnableInterrupt(unsigned int flag);
extern void ISI_DisableInterrupt(unsigned int flag);
extern void ISI_CodecPathFull(void);
extern void ISI_SetFrame(unsigned int frate);
extern unsigned char ISI_BytesForOnePixel(unsigned char bmpRgb);
extern void ISI_Reset(void);
extern void ISI_Init(AT91PS_VIDEO pVideo);
extern unsigned int ISI_StatusRegister(void);

#endif //#ifndef ISI_H

