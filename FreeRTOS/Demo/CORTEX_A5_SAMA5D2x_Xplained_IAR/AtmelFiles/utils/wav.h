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

#ifndef WAV_H
#define WAV_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <stdbool.h>
#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** Standard WAV file header information. */
struct _wav_header {
	/** Contains the letters "RIFF" in ASCII form. */
	uint32_t chunk_id;
	/** Size of the rest of the chunk following this number. */
	uint32_t chunk_size;
	/** Contains the letters "WAVE". */
	uint32_t format;
	/** Contains the letters "fmt ". */
	uint32_t subchunk1_id;
	/** 16 for PCM.  This is the size of the rest of the Subchunk which follows this number. */
	uint32_t subchunk1_size;
	/** PCM = 1 (i.e. Linear quantization). Values other than 1 indicate some form of compression. */
	uint16_t audio_format;
	/** Mono = 1, Stereo = 2, etc. */
	uint16_t num_channels;
	/** 8000, 44100, etc. */
	uint32_t sample_rate;
	/** SampleRate * NumChannels * BitsPerSample/8 */
	uint32_t byte_rate;
	/** NumChannels * BitsPerSample/8 */
	uint16_t block_align;
	/** 8 bits = 8, 16 bits = 16, etc. */
	uint16_t bits_per_sample;
	/** Contains the letters "data". */
	uint32_t subchunk2_id;
	/** Number of bytes in the data. */
	uint32_t subchunk2_size;
};

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern bool wav_is_valid(const struct _wav_header *header);

extern void wav_display_info(const struct _wav_header *header);

#endif /* #ifndef WAV_H */
