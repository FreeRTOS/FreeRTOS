/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

#ifndef WAV_H
#define WAV_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

/* Standard WAV file header information. */
typedef struct _WavHeader
{
    /* Contains the letters "RIFF" in ASCII form. */
    unsigned int  chunkID;
    /* Size of the rest of the chunk following this number.*/
    unsigned int  chunkSize;
    /* Contains the letters "WAVE".*/
    unsigned int format;
    /* Contains the letters "fmt ".*/
    unsigned int subchunk1ID;
    /* 16 for PCM.  This is the size of the rest of the Subchunk which follows this number.*/
    unsigned int  subchunk1Size;
    /* PCM = 1 (i.e. Linear quantization). Values other than 1 indicate some form of compression.*/
    unsigned short audioFormat;
    /* Mono = 1, Stereo = 2, etc.*/
    unsigned short numChannels;
    /* 8000, 44100, etc.*/
    unsigned int   sampleRate;
    /* SampleRate * NumChannels * BitsPerSample/8*/
    unsigned int   byteRate;
    /* NumChannels * BitsPerSample/8*/
    unsigned short blockAlign; 
    /* 8 bits = 8, 16 bits = 16, etc.*/
    unsigned short bitsPerSample;
    /* Contains the letters "data".*/
    unsigned int subchunk2ID;
    /* Number of bytes in the data.*/
    unsigned int subchunk2Size;

} WavHeader;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern unsigned char WAV_IsValid(const WavHeader *header);

extern void WAV_DisplayInfo(const WavHeader *header);

#endif //#ifndef WAV_H

