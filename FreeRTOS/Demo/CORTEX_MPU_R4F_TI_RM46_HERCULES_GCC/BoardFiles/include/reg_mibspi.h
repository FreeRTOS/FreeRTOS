/** @file reg_mibspi.h
 *   @brief MIBSPI Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the MIBSPI driver.
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

#ifndef __REG_MIBSPI_H__
#define __REG_MIBSPI_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Mibspi Register Frame Definition */

/** @struct mibspiBase
 *   @brief MIBSPI Register Definition
 *
 *   This structure is used to access the MIBSPI module registers.
 */

/** @typedef mibspiBASE_t
 *   @brief MIBSPI Register Frame Type Definition
 *
 *   This type is used to access the MIBSPI Registers.
 */
typedef volatile struct mibspiBase
{
    uint32 GCR0;           /**< 0x0000: Global Control 0 */
    uint32 GCR1;           /**< 0x0004: Global Control 1 */
    uint32 INT0;           /**< 0x0008: Interrupt Register */
    uint32 LVL;            /**< 0x000C: Interrupt Level */
    uint32 FLG;            /**< 0x0010: Interrupt flags */
    uint32 PC0;            /**< 0x0014: Function Pin Enable */
    uint32 PC1;            /**< 0x0018: Pin Direction */
    uint32 PC2;            /**< 0x001C: Pin Input Latch */
    uint32 PC3;            /**< 0x0020: Pin Output Latch */
    uint32 PC4;            /**< 0x0024: Output Pin Set */
    uint32 PC5;            /**< 0x0028: Output Pin Clr */
    uint32 PC6;            /**< 0x002C: Open Drain Output Enable */
    uint32 PC7;            /**< 0x0030: Pullup/Pulldown Disable */
    uint32 PC8;            /**< 0x0034: Pullup/Pulldown Selection */
    uint32 DAT0;           /**< 0x0038: Transmit Data */
    uint32 DAT1;           /**< 0x003C: Transmit Data with Format and Chip Select */
    uint32 BUF;            /**< 0x0040: Receive Buffer */
    uint32 EMU;            /**< 0x0044: Emulation Receive Buffer */
    uint32 DELAY;          /**< 0x0048: Delays */
    uint32 DEF;            /**< 0x004C: Default Chip Select */
    uint32 FMT0;           /**< 0x0050: Data Format 0 */
    uint32 FMT1;           /**< 0x0054: Data Format 1 */
    uint32 FMT2;           /**< 0x0058: Data Format 2 */
    uint32 FMT3;           /**< 0x005C: Data Format 3 */
    uint32 INTVECT0;       /**< 0x0060: Interrupt Vector 0 */
    uint32 INTVECT1;       /**< 0x0064: Interrupt Vector 1 */
    uint32 SRSEL;          /**< 0x0068: Slew Rate Select */
    uint32 PMCTRL;         /**< 0x006C: Parallel Mode Control */
    uint32 MIBSPIE;        /**< 0x0070: Multi-buffer Mode Enable  */
    uint32 TGITENST;       /**< 0x0074: TG Interrupt Enable Set */
    uint32 TGITENCR;       /**< 0x0078: TG Interrupt Enable Clear */
    uint32 TGITLVST;       /**< 0x007C: Transfer Group Interrupt Level Set */
    uint32 TGITLVCR;       /**< 0x0080: Transfer Group Interrupt Level Clear */
    uint32 TGINTFLG;       /**< 0x0084: Transfer Group Interrupt Flag */
    uint32 rsvd1[ 2U ];    /**< 0x0088: Reserved */
    uint32 TICKCNT;        /**< 0x0090: Tick Counter */
    uint32 LTGPEND;        /**< 0x0090: Last TG End Pointer */
    uint32 TGCTRL[ 16U ];  /**< 0x0098 - 0x00D4: Transfer Group Control */
    uint32 DMACTRL[ 8U ];  /**< 0x00D8 - 0x00F4: DMA Control */
    uint32 DMACOUNT[ 8U ]; /**< 0x00F8 - 0x0114: DMA Count */
    uint32 DMACNTLEN;      /**< 0x0118 - 0x0114: DMA Control length */
    uint32 rsvd2;          /**< 0x011C: Reserved */
    uint32 UERRCTRL;   /**< 0x0120: Multi-buffer RAM Uncorrectable Parity Error Control */
    uint32 UERRSTAT;   /**< 0x0124: Multi-buffer RAM Uncorrectable Parity Error Status */
    uint32 UERRADDRRX; /**< 0x0128: RXRAM Uncorrectable Parity Error Address */
    uint32 UERRADDRTX; /**< 0x012C: TXRAM Uncorrectable Parity Error Address */
    uint32 RXOVRN_BUF_ADDR; /**< 0x0130: RXRAM Overrun Buffer Address */
    uint32 IOLPKTSTCR;      /**< 0x0134: IO loopback */
    uint32 EXT_PRESCALE1;   /**< 0x0138: */
    uint32 EXT_PRESCALE2;   /**< 0x013C: */
} mibspiBASE_t;

/** @def mibspiREG1
 *   @brief MIBSPI1 Register Frame Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi module registers.
 */
#define mibspiREG1  ( ( mibspiBASE_t * ) 0xFFF7F400U )

/** @def mibspiPORT1
 *   @brief MIBSPI1 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of MIBSPI1
 *   (use the GIO drivers to access the port pins).
 */
#define mibspiPORT1 ( ( gioPORT_t * ) 0xFFF7F418U )

/** @def mibspiREG3
 *   @brief MIBSPI3 Register Frame Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi module registers.
 */
#define mibspiREG3  ( ( mibspiBASE_t * ) 0xFFF7F800U )

/** @def mibspiPORT3
 *   @brief MIBSPI3 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of MIBSPI3
 *   (use the GIO drivers to access the port pins).
 */
#define mibspiPORT3 ( ( gioPORT_t * ) 0xFFF7F818U )

/** @def mibspiREG5
 *   @brief MIBSPI5 Register Frame Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi module registers.
 */
#define mibspiREG5  ( ( mibspiBASE_t * ) 0xFFF7FC00U )

/** @def mibspiPORT5
 *   @brief MIBSPI5 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of MIBSPI5
 *   (use the GIO drivers to access the port pins).
 */
#define mibspiPORT5 ( ( gioPORT_t * ) 0xFFF7FC18U )

/** @struct mibspiRamBase
 *   @brief MIBSPI Buffer RAM Definition
 *
 *   This structure is used to access the MIBSPI buffer memory.
 */

/** @typedef mibspiRAM_t
 *   @brief MIBSPI RAM Type Definition
 *
 *   This type is used to access the MIBSPI RAM.
 */
typedef volatile struct mibspiRamBase
{
    struct
    {
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
        uint16 data;    /**< tx buffer data    */
        uint16 control; /**< tx buffer control */
#else
        uint16 control; /**< tx buffer control */
        uint16 data;    /**< tx buffer data    */
#endif
    } tx[ 128 ];
    struct
    {
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
        uint16 data;  /**< rx buffer data  */
        uint16 flags; /**< rx buffer flags */
#else
        uint16 flags; /**< rx buffer flags */
        uint16 data;  /**< rx buffer data  */
#endif
    } rx[ 128 ];
} mibspiRAM_t;

/** @def mibspiRAM1
 *   @brief MIBSPI1 Buffer RAM Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi buffer memory.
 */
#define mibspiRAM1    ( ( mibspiRAM_t * ) 0xFF0E0000U )

/** @def mibspiRAM3
 *   @brief MIBSPI3 Buffer RAM Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi buffer memory.
 */
#define mibspiRAM3    ( ( mibspiRAM_t * ) 0xFF0C0000U )

/** @def mibspiRAM5
 *   @brief MIBSPI5 Buffer RAM Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi buffer memory.
 */
#define mibspiRAM5    ( ( mibspiRAM_t * ) 0xFF0A0000U )

/** @def mibspiPARRAM1
 *   @brief MIBSPI1 Buffer RAM PARITY Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi buffer memory.
 */
#define mibspiPARRAM1 ( *( volatile uint32 * ) ( 0xFF0E0000U + 0x00000400U ) )

/** @def mibspiPARRAM3
 *   @brief MIBSPI3 Buffer RAM PARITY Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi buffer memory.
 */
#define mibspiPARRAM3 ( *( volatile uint32 * ) ( 0xFF0C0000U + 0x00000400U ) )

/** @def mibspiPARRAM5
 *   @brief MIBSPI5 Buffer RAM PARITY Pointer
 *
 *   This pointer is used by the MIBSPI driver to access the mibspi buffer memory.
 */
#define mibspiPARRAM5 ( *( volatile uint32 * ) ( 0xFF0A0000U + 0x00000400U ) )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_MIBSPI_H__ */
