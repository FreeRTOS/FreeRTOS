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

/**
 * \file
 *
 * Interface of ILI9488 driver.
 *
 */

#ifndef _ILI9488_DMA_H_
#define _ILI9488_DMA_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"
#include <stdint.h>

/*------------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/
/** An unspecified error has occurred.*/
#define ILI9488_ERROR_DMA_ALLOCATE_CHANNEL          1
#define ILI9488_ERROR_DMA_CONFIGURE                 2
#define ILI9488_ERROR_DMA_TRANSFER                  3
#define ILI9488_ERROR_DMA_SIZE                      4

#define ILI9488_SPI                                 SPI0
#define ILI9488_SPI_ID                              ID_SPI0

/* EBI BASE ADDRESS for SMC LCD */
#define ILI9488_BASE_ADDRESS        0x63000000

/*------------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

typedef struct _ILI9488_dma
{
	/** Pointer to DMA driver */
	sXdmad              *xdmaD;
	/** ili9488 Tx channel */
	uint32_t            ili9488DmaTxChannel;
	/** ili9488 Rx channel */
	uint32_t            ili9488DmaRxChannel;
	/** ili9488 Tx/Rx configure descriptor */
	sXdmadCfg           xdmadRxCfg,xdmadTxCfg;
	/** ili9488 dma interrupt */
	uint32_t            xdmaInt;
	/** Pointer to SPI Hardware registers */
	Spi*                pSpiHw ;
	/** SPI Id as defined in the product datasheet */
	uint8_t             spiId ;
}sIli9488Dma;

typedef struct _ILI9488_ctl
{
	/** ili9488 Command/Data mode */
	volatile uint32_t       cmdOrDataFlag;
	/** ili9488 Rx done */
	volatile uint32_t       rxDoneFlag;
	/** ili9488 Tx done */
	volatile uint32_t       txDoneFlag;
}sIli9488DmaCtl;

#endif /* #ifndef ILI9488_DMA */
