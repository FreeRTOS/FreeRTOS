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

/**
 * \file
 *
 * Interface for Serial Peripheral Interface (SPI) controller.
 *
 */

#ifndef _SPI_
#define _SPI_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

#define SPI_KEEP_CS_OW    (0)
#define SPI_RELEASE_CS_OW (1)

/*------------------------------------------------------------------------------ */

#ifdef __cplusplus
extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enables a SPI peripheral.
 *
 * \param spi  Pointer to an Spi instance.
 */
extern void spi_enable(Spi * spi);

/**
 * \brief Disables a SPI peripheral.
 *
 * \param spi  Pointer to an Spi instance.
 */
extern void spi_disable(Spi * spi);

/**
 * \brief Enables one or more interrupt sources of a SPI peripheral.
 *
 * \param spi  Pointer to an Spi instance.
 * \param dwSources Bitwise OR of selected interrupt sources.
 */
extern void spi_enable_it(Spi * spi, uint32_t dwSources);

/**
 * \brief Disables one or more interrupt sources of a SPI peripheral.
 *
 * \param spi  Pointer to an Spi instance.
 * \param dwSources Bitwise OR of selected interrupt sources.
 */
extern void spi_disable_it(Spi * spi, uint32_t dwSources);

/**
 * \brief Configures a SPI peripheral as specified. The configuration
 * can be computed
 * using several macros (see \ref spi_configuration_macros).
 *
 * \param spi  Pointer to an Spi instance.
 * \param dwConfiguration  Value of the SPI configuration register.
 */
extern void spi_configure(Spi * spi, uint32_t configuration);

/**
 * \brief Configures SPI Mode Register.
 *
 * \param spi  Pointer to an Spi instance.
 * \param dwConfiguration  Value of the SPI mode register.
 */
extern void spi_set_mode(Spi * spi, uint32_t dwConfiguration);

/**
 * \brief Configures SPI chip select.
 *
 * \param spi  Pointer to an Spi instance.
 * \param cS  Chip select of NPSCx.
 */
extern void spi_chip_select(Spi * spi, uint8_t cS);

/**
 * \brief Configures SPI to release last used CS line.
 *
 * \param spi  Pointer to an Spi instance.
 */
extern void spi_release_cs(Spi * spi);

/**
 * \brief Configures a chip select of a SPI peripheral.
 *
 * \param spi Pointer to an Spi instance.
 * \param cs Chip select to configure (0, 1, 2 or 3).
 * \param bitrate
 * \param delay_dlybs
 * \param delay_dlybct
 * \param spi_mode
 * \param release_on_last
 */
extern void spi_configure_cs(Spi * spi, uint32_t cs,uint32_t bitrate,
			     uint32_t delay_dlybs, uint32_t delay_dlybct,
			     uint32_t spi_mode, uint32_t release_on_last);

/**
 * \brief Configures a chip select active mode of a SPI peripheral.
 *
 * \param spi   Pointer to an Spi instance.
 * \param cs  Chip select to configure (0, 1, 2 or 3).
 * \param release_on_last CS controlled by last transfer.
 *                       spi_release_cs() is used to deactive CS.
 */
extern void spi_configure_cs_mode(Spi * spi, uint32_t cs,
				uint32_t release_on_last);

/**
 * \brief Reads one data from SPI peripheral with a dummy write.
 *
 * \param spi Pointer to an Spi instance.
 *
 * \return readed data.
 */

extern uint16_t spi_read(Spi * spi, uint8_t cs);

/**
 * \brief Sends data through a SPI peripheral consuming reads.
 *
 *
 * \param spi   Pointer to an Spi instance.
 * \param cs  Chip select of the component to address (0, 1, 2 or 3).
 * \param data  Word of data to send.
 */
extern void spi_write(Spi * spi, uint32_t cs, uint16_t data);
extern void spi_write_last(Spi * spi, uint32_t cs, uint16_t data);

/**
 * \brief Get the current status register of the given SPI peripheral.
 *
 * \note This resets the internal value of the status register, so further
 * read may yield different values.
 *
 * \param spi   Pointer to a Spi instance.
 * \return  SPI status register.
 */
extern uint32_t spi_get_status(Spi * spi);


/**
 * \brief Check if SPI transfer finish.
 *
 * \param spi  Pointer to an Spi instance.
 *
 * \return Returns 1 if there is no pending write operation on the SPI;
 * otherwise returns 0.
 */

extern uint32_t spi_is_finished(Spi * spi);

#ifdef CONFIG_HAVE_SPI_FIFO
extern void spi_fifo_configure(Spi* spi, uint8_t tx_thres,
			uint8_t rx_thres,
			uint32_t ready_modes);
extern void spi_fifo_disable(Spi* spi);

extern uint32_t spi_fifo_rx_size(Spi *spi);
extern uint32_t spi_fifo_tx_size(Spi *spi);

extern uint32_t spi_read_stream(Spi *spi, uint32_t chip_select,
				void *stream, uint32_t len);
extern uint32_t spi_write_stream(Spi *spi, uint32_t chip_select,
			  const void *stream, uint32_t len);
#endif

#ifdef __cplusplus
}
#endif
#endif  /* #ifndef _SPI_ */
