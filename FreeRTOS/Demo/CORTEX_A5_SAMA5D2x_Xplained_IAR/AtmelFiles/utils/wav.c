/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

#include <stdio.h>

#include "wav.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** WAV letters "RIFF" */
#define WAV_CHUNKID       0x46464952

/** WAV letters "WAVE"*/
#define WAV_FORMAT        0x45564157

/** WAV letters "fmt "*/
#define WAV_SUBCHUNKID    0x20746D66

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Check if the header of a Wav file is valid or not.
 *
 * \param header Wav header information.
 * \return true if the header of a Wav file is valid; otherwise returns false.
 */
bool wav_is_valid(const struct _wav_header *header)
{
	return (header->chunk_id == WAV_CHUNKID
			&& header->format == WAV_FORMAT
			&& header->subchunk1_size == 0x10);
}

/**
 * \brief Display the information of the WAV file (sample rate, stereo/mono
 * and frame size).
 *
 * \param header Wav header information.
 */

void wav_display_info(const struct _wav_header *header)
{
	printf("Wave file header information\n\r");
	printf("--------------------------------\n\r");
	printf("  - Chunk ID        = 0x%08X\n\r",
			(unsigned int)header->chunk_id);
	printf("  - Chunk Size      = %u\n\r",
			(unsigned int)header->chunk_size);
	printf("  - Format          = 0x%08X\n\r",
			(unsigned int)header->format);
	printf("  - SubChunk ID     = 0x%08X\n\r",
			(unsigned int)header->subchunk1_id);
	printf("  - Subchunk1 Size  = %u\n\r",
			(unsigned int)header->subchunk1_size);
	printf("  - Audio Format    = 0x%04X\n\r",
			(unsigned int)header->audio_format);
	printf("  - Num. Channels   = %d\n\r",
			(unsigned int)header->num_channels);
	printf("  - Sample Rate     = %u\n\r",
			(unsigned int)header->sample_rate);
	printf("  - Byte Rate       = %u\n\r",
			(unsigned int)header->byte_rate);
	printf("  - Block Align     = %d\n\r",
			(unsigned int)header->block_align);
	printf("  - Bits Per Sample = %d\n\r",
			(unsigned int)header->bits_per_sample);
	printf("  - Subchunk2 ID    = 0x%08X\n\r",
			(unsigned int)header->subchunk2_id);
	printf("  - Subchunk2 Size  = %u\n\r",
			(unsigned int)header->subchunk2_size);
}
