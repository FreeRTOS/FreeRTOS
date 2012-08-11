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
/// \dir
/// !Purpose
/// 
/// Definitions for SPI peripheral usage.
///
/// !Usage
///
/// -# Enable the SPI pins required by the application (see pio.h).
/// -# Configure the SPI using the SPI_Configure function. This enables the
///    peripheral clock. The mode register is loaded with the given value.
/// -# Configure all the necessary chip selects with SPI_ConfigureNPCS.
/// -# Enable the SPI by calling SPI_Enable.
/// -# Send/receive data using SPI_Write and SPI_Read. Note that SPI_Read
///    must be called after SPI_Write to retrieve the last value read.
/// -# Send/receive data using the PDC with the SPI_WriteBuffer and
///    SPI_ReadBuffer functions.
/// -# Disable the SPI by calling SPI_Disable.
//------------------------------------------------------------------------------

#ifndef SPI_H
#define SPI_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// \page "SPI configuration macros"
/// This page lists several macros which should be used when configuring a SPI
/// peripheral.
/// 
/// !Macros
/// - SPI_PCS
/// - SPI_SCBR
/// - SPI_DLYBS
/// - SPI_DLYBCT

/// Calculate the PCS field value given the chip select NPCS value
#define SPI_PCS(npcs)       ((~(1 << npcs) & 0xF) << 16)

/// Calculates the value of the CSR SCBR field given the baudrate and MCK.
#define SPI_SCBR(baudrate, masterClock) \
            ((unsigned int) (masterClock / baudrate) << 8)

/// Calculates the value of the CSR DLYBS field given the desired delay (in ns)
#define SPI_DLYBS(delay, masterClock) \
            ((unsigned int) (((masterClock / 1000000) * delay) / 1000) << 16)

/// Calculates the value of the CSR DLYBCT field given the desired delay (in ns)
#define SPI_DLYBCT(delay, masterClock) \
            ((unsigned int) (((masterClock / 1000000) * delay) / 32000) << 24)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
extern void SPI_Enable(AT91S_SPI *spi);
extern void SPI_Disable(AT91S_SPI *spi);
extern void SPI_Configure(AT91S_SPI *spi,
                                 unsigned int id,
                                 unsigned int configuration);
extern void SPI_ConfigureNPCS(AT91S_SPI *spi,
                                     unsigned int npcs,
                                     unsigned int configuration);
extern void SPI_Write(AT91S_SPI *spi, unsigned int npcs, unsigned short data);
extern unsigned char SPI_WriteBuffer(AT91S_SPI *spi,
                                            void *buffer,
                                            unsigned int length);

extern unsigned char SPI_IsFinished(AT91S_SPI *pSpi);

extern unsigned short SPI_Read(AT91S_SPI *spi);
extern unsigned char SPI_ReadBuffer(AT91S_SPI *spi,
                                           void *buffer,
                                           unsigned int length);

#endif //#ifndef SPI_H

