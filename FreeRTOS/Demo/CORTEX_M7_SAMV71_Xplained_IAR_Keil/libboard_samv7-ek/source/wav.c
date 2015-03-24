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
 
/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <stdio.h>

/*----------------------------------------------------------------------------
 *        Definiation
 *----------------------------------------------------------------------------*/

/* WAV letters "RIFF" */
#define WAV_CHUNKID       0x46464952
/* WAV letters "WAVE"*/
#define WAV_FORMAT        0x45564157
/* WAV letters "fmt "*/
#define WAV_SUBCHUNKID    0x20746D66

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Check if the header of a Wav file is valid ot not.
 *
 * \param file  Buffer holding the file to examinate.
 * \return 1 if the header of a Wav file is valid; otherwise returns 0.
 */
unsigned char WAV_IsValid(const WavHeader *header)
{
    return ((header->chunkID == WAV_CHUNKID)
            && (header->format == WAV_FORMAT)
            && (header->subchunk1Size == 0x10));
}

/**
 * \brief Display the information of the WAV file (sample rate, stereo/mono
 * and frame size).
 *
 * \param header  Wav head information.
 */

void WAV_DisplayInfo(const WavHeader *header)
{
    printf( "Wave file header information\n\r");
    printf( "--------------------------------\n\r");
    printf( "  - Chunk ID        = 0x%08X\n\r", header->chunkID);
    printf( "  - Chunk Size      = %u\n\r",     header->chunkSize);
    printf( "  - Format          = 0x%08X\n\r", header->format);
    printf( "  - SubChunk ID     = 0x%08X\n\r", header->subchunk1ID);
    printf( "  - Subchunk1 Size  = %u\n\r",     header->subchunk1Size);
    printf( "  - Audio Format    = 0x%04X\n\r", header->audioFormat);
    printf( "  - Num. Channels   = %d\n\r",     header->numChannels);
    printf( "  - Sample Rate     = %u\n\r",     header->sampleRate);
    printf( "  - Byte Rate       = %u\n\r",     header->byteRate);
    printf( "  - Block Align     = %d\n\r",     header->blockAlign);
    printf( "  - Bits Per Sample = %d\n\r",     header->bitsPerSample);
    printf( "  - Subchunk2 ID    = 0x%08X\n\r", header->subchunk2ID);
    printf( "  - Subchunk2 Size  = %u\n\r",     header->subchunk2Size);
}

