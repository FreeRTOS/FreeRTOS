/** @file reg_spi.h
 *   @brief SPI Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the SPI driver.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __REG_SPI_H__
#define __REG_SPI_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Spi Register Frame Definition */
/** @struct spiBase
 *   @brief SPI Register Definition
 *
 *   This structure is used to access the SPI module registers.
 */
/** @typedef spiBASE_t
 *   @brief SPI Register Frame Type Definition
 *
 *   This type is used to access the SPI Registers.
 */
typedef volatile struct spiBase
{
    uint32 GCR0;            /**< 0x0000: Global Control 0 */
    uint32 GCR1;            /**< 0x0004: Global Control 1 */
    uint32 INT0;            /**< 0x0008: Interrupt Register */
    uint32 LVL;             /**< 0x000C: Interrupt Level */
    uint32 FLG;             /**< 0x0010: Interrupt flags */
    uint32 PC0;             /**< 0x0014: Function Pin Enable */
    uint32 PC1;             /**< 0x0018: Pin Direction */
    uint32 PC2;             /**< 0x001C: Pin Input Latch */
    uint32 PC3;             /**< 0x0020: Pin Output Latch */
    uint32 PC4;             /**< 0x0024: Output Pin Set */
    uint32 PC5;             /**< 0x0028: Output Pin Clr */
    uint32 PC6;             /**< 0x002C: Open Drain Output Enable */
    uint32 PC7;             /**< 0x0030: Pullup/Pulldown Disable */
    uint32 PC8;             /**< 0x0034: Pullup/Pulldown Selection */
    uint32 DAT0;            /**< 0x0038: Transmit Data */
    uint32 DAT1;            /**< 0x003C: Transmit Data with Format and Chip Select */
    uint32 BUF;             /**< 0x0040: Receive Buffer */
    uint32 EMU;             /**< 0x0044: Emulation Receive Buffer */
    uint32 DELAY;           /**< 0x0048: Delays */
    uint32 DEF;             /**< 0x004C: Default Chip Select */
    uint32 FMT0;            /**< 0x0050: Data Format 0 */
    uint32 FMT1;            /**< 0x0054: Data Format 1 */
    uint32 FMT2;            /**< 0x0058: Data Format 2 */
    uint32 FMT3;            /**< 0x005C: Data Format 3 */
    uint32 INTVECT0;        /**< 0x0060: Interrupt Vector 0 */
    uint32 INTVECT1;        /**< 0x0064: Interrupt Vector 1 */
    uint32 RESERVED[ 51U ]; /**< 0x0068 to 0x0130: Reserved */
    uint32 IOLPKTSTCR;      /**< 0x0134: IO loopback */
} spiBASE_t;

/** @def spiREG1
 *   @brief SPI1 (MIBSPI - Compatibility Mode) Register Frame Pointer
 *
 *   This pointer is used by the SPI driver to access the spi module registers.
 */
#define spiREG1  ( ( spiBASE_t * ) 0xFFF7F400U )

/** @def spiPORT1
 *   @brief SPI1 (MIBSPI - Compatibility Mode) GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of SPI1
 *   (use the GIO drivers to access the port pins).
 */
#define spiPORT1 ( ( gioPORT_t * ) 0xFFF7F418U )

/** @def spiREG2
 *   @brief SPI2 Register Frame Pointer
 *
 *   This pointer is used by the SPI driver to access the spi module registers.
 */
#define spiREG2  ( ( spiBASE_t * ) 0xFFF7F600U )

/** @def spiPORT2
 *   @brief SPI2 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of SPI2
 *   (use the GIO drivers to access the port pins).
 */
#define spiPORT2 ( ( gioPORT_t * ) 0xFFF7F618U )

/** @def spiREG3
 *   @brief SPI3 (MIBSPI - Compatibility Mode) Register Frame Pointer
 *
 *   This pointer is used by the SPI driver to access the spi module registers.
 */
#define spiREG3  ( ( spiBASE_t * ) 0xFFF7F800U )

/** @def spiPORT3
 *   @brief SPI3 (MIBSPI - Compatibility Mode) GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of SPI3
 *   (use the GIO drivers to access the port pins).
 */
#define spiPORT3 ( ( gioPORT_t * ) 0xFFF7F818U )

/** @def spiREG4
 *   @brief SPI4 Register Frame Pointer
 *
 *   This pointer is used by the SPI driver to access the spi module registers.
 */
#define spiREG4  ( ( spiBASE_t * ) 0xFFF7FA00U )

/** @def spiPORT4
 *   @brief SPI4 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of SPI4
 *   (use the GIO drivers to access the port pins).
 */
#define spiPORT4 ( ( gioPORT_t * ) 0xFFF7FA18U )

/** @def spiREG5
 *   @brief SPI5 (MIBSPI - Compatibility Mode) Register Frame Pointer
 *
 *   This pointer is used by the SPI driver to access the spi module registers.
 */
#define spiREG5  ( ( spiBASE_t * ) 0xFFF7FC00U )

/** @def spiPORT5
 *   @brief SPI5 (MIBSPI - Compatibility Mode) GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of SPI5
 *   (use the GIO drivers to access the port pins).
 */
#define spiPORT5 ( ( gioPORT_t * ) 0xFFF7FC18U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
