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

#ifndef _SDMMC_PERIPH_H_
#define _SDMMC_PERIPH_H_

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#ifdef __cplusplus
extern "C" {
#endif

struct _SdmmcCommand;

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

/* This structure is private to the SDMMC Driver.
 * Allocate it but ignore its members. */
struct sdmmc_set
{
	uint32_t id;                  /* SDMMC peripheral ID (ID_SDMMCx) */
	Sdmmc *regs;                  /* set of SDMMC hardware registers */
	uint32_t tc_id;               /* Timer/Counter peripheral ID (ID_TCx) */
	TcChannel *timer;             /* set of TC channel hardware registers */
	uint32_t *table;              /* ADMA descriptor table, or NULL when DMA
                                       * is not used */
	uint32_t table_size;          /* Max size of the ADMA descriptor table,
                                       * in lines */
	bool use_polling;             /* polling mode */
	bool use_set_blk_cnt;         /* implicit SET_BLOCK_COUNT command */

	uint16_t blk_size;            /* max data block size, in bytes */
	uint32_t dev_freq;            /* frequency of clock provided to memory
				       * device, in Hz */
	volatile uint8_t state;
	struct _SdmmcCommand *cmd;    /* pointer to the command being processed */
	uint16_t blk_index;           /* count of data blocks tranferred already,
				       * in the context of the command and data
				       * transfer being executed */
	uint8_t resp_len;             /* size of the response, once retrieved,
				       * in the context of the command being
				       * executed, expressed in 32-bit words */
	bool expect_auto_end;         /* waiting for completion of Auto CMD12 */
};

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initialize the specified driver instance and the associated SDMMC 
 * peripheral.
 * \param set  Pointer to uninitialized driver instance data.
 * \param regs  Base address of registers of the SDMMC peripheral.
 * \param sdmmc_id  SDMMC peripheral ID (ID_SDMMCx).
 * \param tc_id  TC peripheral ID (ID_TCx).
 * \note The application shall have enabled the clock assigned to this
 * Timer/Counter peripheral.
 * \param tc_ch  TC channel number, within the Timer/Counter module designated
 * by tc_id. Every instance of the SDMMC Driver requires a Timer/Counter channel
 * for its exclusive usage.
 * \param dma_buf  Buffer allocated by the application, required when DMA is
 * used. This is where the DMA descriptor table will be set up. The larger
 * the buffer is, the greater throughput we achieve. Up to 4 KiB. Shall be
 * word-aligned. NULL to have the CPU read/write data, word by word.
 * \param dma_buf_size  Size of the dma_buf buffer, in words.
 * \return true if successful, false if a parameter is assigned an unsupported
 * value.
 */
bool sdmmc_initialize(struct sdmmc_set *set, Sdmmc *regs, uint32_t sdmmc_id,
    uint32_t tc_id, uint32_t tc_ch, uint32_t *dma_buf, uint32_t dma_buf_size);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _SDMMC_PERIPH_H_ */
