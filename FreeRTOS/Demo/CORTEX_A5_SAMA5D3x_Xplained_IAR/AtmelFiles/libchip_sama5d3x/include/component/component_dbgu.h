/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following condition is met:
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

#ifndef _SAMA5_DBGU_COMPONENT_
#define _SAMA5_DBGU_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Debug Unit */
/* ============================================================================= */
/** \addtogroup SAMA5_DBGU Debug Unit */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Dbgu hardware registers */
typedef struct {
  WoReg DBGU_CR;      /**< \brief (Dbgu Offset: 0x0000) Control Register */
  RwReg DBGU_MR;      /**< \brief (Dbgu Offset: 0x0004) Mode Register */
  WoReg DBGU_IER;     /**< \brief (Dbgu Offset: 0x0008) Interrupt Enable Register */
  WoReg DBGU_IDR;     /**< \brief (Dbgu Offset: 0x000C) Interrupt Disable Register */
  RoReg DBGU_IMR;     /**< \brief (Dbgu Offset: 0x0010) Interrupt Mask Register */
  RoReg DBGU_SR;      /**< \brief (Dbgu Offset: 0x0014) Status Register */
  RoReg DBGU_RHR;     /**< \brief (Dbgu Offset: 0x0018) Receive Holding Register */
  WoReg DBGU_THR;     /**< \brief (Dbgu Offset: 0x001C) Transmit Holding Register */
  RwReg DBGU_BRGR;    /**< \brief (Dbgu Offset: 0x0020) Baud Rate Generator Register */
  RoReg Reserved1[7];
  RoReg DBGU_CIDR;    /**< \brief (Dbgu Offset: 0x0040) Chip ID Register */
  RoReg DBGU_EXID;    /**< \brief (Dbgu Offset: 0x0044) Chip ID Extension Register */
  RwReg DBGU_FNR;     /**< \brief (Dbgu Offset: 0x0048) Force NTRST Register */
} Dbgu;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- DBGU_CR : (DBGU Offset: 0x0000) Control Register -------- */
#define DBGU_CR_RSTRX (0x1u << 2) /**< \brief (DBGU_CR) Reset Receiver */
#define DBGU_CR_RSTTX (0x1u << 3) /**< \brief (DBGU_CR) Reset Transmitter */
#define DBGU_CR_RXEN (0x1u << 4) /**< \brief (DBGU_CR) Receiver Enable */
#define DBGU_CR_RXDIS (0x1u << 5) /**< \brief (DBGU_CR) Receiver Disable */
#define DBGU_CR_TXEN (0x1u << 6) /**< \brief (DBGU_CR) Transmitter Enable */
#define DBGU_CR_TXDIS (0x1u << 7) /**< \brief (DBGU_CR) Transmitter Disable */
#define DBGU_CR_RSTSTA (0x1u << 8) /**< \brief (DBGU_CR) Reset Status Bits */
/* -------- DBGU_MR : (DBGU Offset: 0x0004) Mode Register -------- */
#define DBGU_MR_PAR_Pos 9
#define DBGU_MR_PAR_Msk (0x7u << DBGU_MR_PAR_Pos) /**< \brief (DBGU_MR) Parity Type */
#define   DBGU_MR_PAR_EVEN (0x0u << 9) /**< \brief (DBGU_MR) Even Parity */
#define   DBGU_MR_PAR_ODD (0x1u << 9) /**< \brief (DBGU_MR) Odd Parity */
#define   DBGU_MR_PAR_SPACE (0x2u << 9) /**< \brief (DBGU_MR) Space: Parity forced to 0 */
#define   DBGU_MR_PAR_MARK (0x3u << 9) /**< \brief (DBGU_MR) Mark: Parity forced to 1 */
#define   DBGU_MR_PAR_NONE (0x4u << 9) /**< \brief (DBGU_MR) No Parity */
#define DBGU_MR_CHMODE_Pos 14
#define DBGU_MR_CHMODE_Msk (0x3u << DBGU_MR_CHMODE_Pos) /**< \brief (DBGU_MR) Channel Mode */
#define   DBGU_MR_CHMODE_NORM (0x0u << 14) /**< \brief (DBGU_MR) Normal Mode */
#define   DBGU_MR_CHMODE_AUTO (0x1u << 14) /**< \brief (DBGU_MR) Automatic Echo */
#define   DBGU_MR_CHMODE_LOCLOOP (0x2u << 14) /**< \brief (DBGU_MR) Local Loopback */
#define   DBGU_MR_CHMODE_REMLOOP (0x3u << 14) /**< \brief (DBGU_MR) Remote Loopback */
/* -------- DBGU_IER : (DBGU Offset: 0x0008) Interrupt Enable Register -------- */
#define DBGU_IER_RXRDY (0x1u << 0) /**< \brief (DBGU_IER) Enable RXRDY Interrupt */
#define DBGU_IER_TXRDY (0x1u << 1) /**< \brief (DBGU_IER) Enable TXRDY Interrupt */
#define DBGU_IER_OVRE (0x1u << 5) /**< \brief (DBGU_IER) Enable Overrun Error Interrupt */
#define DBGU_IER_FRAME (0x1u << 6) /**< \brief (DBGU_IER) Enable Framing Error Interrupt */
#define DBGU_IER_PARE (0x1u << 7) /**< \brief (DBGU_IER) Enable Parity Error Interrupt */
#define DBGU_IER_TXEMPTY (0x1u << 9) /**< \brief (DBGU_IER) Enable TXEMPTY Interrupt */
#define DBGU_IER_COMMTX (0x1u << 30) /**< \brief (DBGU_IER) Enable COMMTX (from ARM) Interrupt */
#define DBGU_IER_COMMRX (0x1u << 31) /**< \brief (DBGU_IER) Enable COMMRX (from ARM) Interrupt */
/* -------- DBGU_IDR : (DBGU Offset: 0x000C) Interrupt Disable Register -------- */
#define DBGU_IDR_RXRDY (0x1u << 0) /**< \brief (DBGU_IDR) Disable RXRDY Interrupt */
#define DBGU_IDR_TXRDY (0x1u << 1) /**< \brief (DBGU_IDR) Disable TXRDY Interrupt */
#define DBGU_IDR_OVRE (0x1u << 5) /**< \brief (DBGU_IDR) Disable Overrun Error Interrupt */
#define DBGU_IDR_FRAME (0x1u << 6) /**< \brief (DBGU_IDR) Disable Framing Error Interrupt */
#define DBGU_IDR_PARE (0x1u << 7) /**< \brief (DBGU_IDR) Disable Parity Error Interrupt */
#define DBGU_IDR_TXEMPTY (0x1u << 9) /**< \brief (DBGU_IDR) Disable TXEMPTY Interrupt */
#define DBGU_IDR_COMMTX (0x1u << 30) /**< \brief (DBGU_IDR) Disable COMMTX (from ARM) Interrupt */
#define DBGU_IDR_COMMRX (0x1u << 31) /**< \brief (DBGU_IDR) Disable COMMRX (from ARM) Interrupt */
/* -------- DBGU_IMR : (DBGU Offset: 0x0010) Interrupt Mask Register -------- */
#define DBGU_IMR_RXRDY (0x1u << 0) /**< \brief (DBGU_IMR) Mask RXRDY Interrupt */
#define DBGU_IMR_TXRDY (0x1u << 1) /**< \brief (DBGU_IMR) Disable TXRDY Interrupt */
#define DBGU_IMR_OVRE (0x1u << 5) /**< \brief (DBGU_IMR) Mask Overrun Error Interrupt */
#define DBGU_IMR_FRAME (0x1u << 6) /**< \brief (DBGU_IMR) Mask Framing Error Interrupt */
#define DBGU_IMR_PARE (0x1u << 7) /**< \brief (DBGU_IMR) Mask Parity Error Interrupt */
#define DBGU_IMR_TXEMPTY (0x1u << 9) /**< \brief (DBGU_IMR) Mask TXEMPTY Interrupt */
#define DBGU_IMR_COMMTX (0x1u << 30) /**< \brief (DBGU_IMR) Mask COMMTX Interrupt */
#define DBGU_IMR_COMMRX (0x1u << 31) /**< \brief (DBGU_IMR) Mask COMMRX Interrupt */
/* -------- DBGU_SR : (DBGU Offset: 0x0014) Status Register -------- */
#define DBGU_SR_RXRDY (0x1u << 0) /**< \brief (DBGU_SR) Receiver Ready */
#define DBGU_SR_TXRDY (0x1u << 1) /**< \brief (DBGU_SR) Transmitter Ready */
#define DBGU_SR_OVRE (0x1u << 5) /**< \brief (DBGU_SR) Overrun Error */
#define DBGU_SR_FRAME (0x1u << 6) /**< \brief (DBGU_SR) Framing Error */
#define DBGU_SR_PARE (0x1u << 7) /**< \brief (DBGU_SR) Parity Error */
#define DBGU_SR_TXEMPTY (0x1u << 9) /**< \brief (DBGU_SR) Transmitter Empty */
#define DBGU_SR_COMMTX (0x1u << 30) /**< \brief (DBGU_SR) Debug Communication Channel Write Status */
#define DBGU_SR_COMMRX (0x1u << 31) /**< \brief (DBGU_SR) Debug Communication Channel Read Status */
/* -------- DBGU_RHR : (DBGU Offset: 0x0018) Receive Holding Register -------- */
#define DBGU_RHR_RXCHR_Pos 0
#define DBGU_RHR_RXCHR_Msk (0xffu << DBGU_RHR_RXCHR_Pos) /**< \brief (DBGU_RHR) Received Character */
/* -------- DBGU_THR : (DBGU Offset: 0x001C) Transmit Holding Register -------- */
#define DBGU_THR_TXCHR_Pos 0
#define DBGU_THR_TXCHR_Msk (0xffu << DBGU_THR_TXCHR_Pos) /**< \brief (DBGU_THR) Character to be Transmitted */
#define DBGU_THR_TXCHR(value) ((DBGU_THR_TXCHR_Msk & ((value) << DBGU_THR_TXCHR_Pos)))
/* -------- DBGU_BRGR : (DBGU Offset: 0x0020) Baud Rate Generator Register -------- */
#define DBGU_BRGR_CD_Pos 0
#define DBGU_BRGR_CD_Msk (0xffffu << DBGU_BRGR_CD_Pos) /**< \brief (DBGU_BRGR) Clock Divisor */
#define   DBGU_BRGR_CD_DISABLED (0x0u << 0) /**< \brief (DBGU_BRGR) DBGU Disabled */
#define   DBGU_BRGR_CD_MCK (0x1u << 0) /**< \brief (DBGU_BRGR) MCK */
/* -------- DBGU_CIDR : (DBGU Offset: 0x0040) Chip ID Register -------- */
#define DBGU_CIDR_VERSION_Pos 0
#define DBGU_CIDR_VERSION_Msk (0x1fu << DBGU_CIDR_VERSION_Pos) /**< \brief (DBGU_CIDR) Version of the Device */
#define DBGU_CIDR_EPROC_Pos 5
#define DBGU_CIDR_EPROC_Msk (0x7u << DBGU_CIDR_EPROC_Pos) /**< \brief (DBGU_CIDR) Embedded Processor */
#define   DBGU_CIDR_EPROC_ARM946ES (0x1u << 5) /**< \brief (DBGU_CIDR) ARM946ES */
#define   DBGU_CIDR_EPROC_ARM7TDMI (0x2u << 5) /**< \brief (DBGU_CIDR) ARM7TDMI */
#define   DBGU_CIDR_EPROC_CM3 (0x3u << 5) /**< \brief (DBGU_CIDR) Cortex-M3 */
#define   DBGU_CIDR_EPROC_ARM920T (0x4u << 5) /**< \brief (DBGU_CIDR) ARM920T */
#define   DBGU_CIDR_EPROC_ARM926EJS (0x5u << 5) /**< \brief (DBGU_CIDR) ARM926EJS */
#define   DBGU_CIDR_EPROC_CA5 (0x6u << 5) /**< \brief (DBGU_CIDR) Cortex-A5 */
#define DBGU_CIDR_NVPSIZ_Pos 8
#define DBGU_CIDR_NVPSIZ_Msk (0xfu << DBGU_CIDR_NVPSIZ_Pos) /**< \brief (DBGU_CIDR) Nonvolatile Program Memory Size */
#define   DBGU_CIDR_NVPSIZ_NONE (0x0u << 8) /**< \brief (DBGU_CIDR) None */
#define   DBGU_CIDR_NVPSIZ_8K (0x1u << 8) /**< \brief (DBGU_CIDR) 8K bytes */
#define   DBGU_CIDR_NVPSIZ_16K (0x2u << 8) /**< \brief (DBGU_CIDR) 16K bytes */
#define   DBGU_CIDR_NVPSIZ_32K (0x3u << 8) /**< \brief (DBGU_CIDR) 32K bytes */
#define   DBGU_CIDR_NVPSIZ_64K (0x5u << 8) /**< \brief (DBGU_CIDR) 64K bytes */
#define   DBGU_CIDR_NVPSIZ_128K (0x7u << 8) /**< \brief (DBGU_CIDR) 128K bytes */
#define   DBGU_CIDR_NVPSIZ_256K (0x9u << 8) /**< \brief (DBGU_CIDR) 256K bytes */
#define   DBGU_CIDR_NVPSIZ_512K (0xAu << 8) /**< \brief (DBGU_CIDR) 512K bytes */
#define   DBGU_CIDR_NVPSIZ_1024K (0xCu << 8) /**< \brief (DBGU_CIDR) 1024K bytes */
#define   DBGU_CIDR_NVPSIZ_2048K (0xEu << 8) /**< \brief (DBGU_CIDR) 2048K bytes */
#define DBGU_CIDR_NVPSIZ2_Pos 12
#define DBGU_CIDR_NVPSIZ2_Msk (0xfu << DBGU_CIDR_NVPSIZ2_Pos) /**< \brief (DBGU_CIDR)  */
#define   DBGU_CIDR_NVPSIZ2_NONE (0x0u << 12) /**< \brief (DBGU_CIDR) None */
#define   DBGU_CIDR_NVPSIZ2_8K (0x1u << 12) /**< \brief (DBGU_CIDR) 8K bytes */
#define   DBGU_CIDR_NVPSIZ2_16K (0x2u << 12) /**< \brief (DBGU_CIDR) 16K bytes */
#define   DBGU_CIDR_NVPSIZ2_32K (0x3u << 12) /**< \brief (DBGU_CIDR) 32K bytes */
#define   DBGU_CIDR_NVPSIZ2_64K (0x5u << 12) /**< \brief (DBGU_CIDR) 64K bytes */
#define   DBGU_CIDR_NVPSIZ2_128K (0x7u << 12) /**< \brief (DBGU_CIDR) 128K bytes */
#define   DBGU_CIDR_NVPSIZ2_256K (0x9u << 12) /**< \brief (DBGU_CIDR) 256K bytes */
#define   DBGU_CIDR_NVPSIZ2_512K (0xAu << 12) /**< \brief (DBGU_CIDR) 512K bytes */
#define   DBGU_CIDR_NVPSIZ2_1024K (0xCu << 12) /**< \brief (DBGU_CIDR) 1024K bytes */
#define   DBGU_CIDR_NVPSIZ2_2048K (0xEu << 12) /**< \brief (DBGU_CIDR) 2048K bytes */
#define DBGU_CIDR_SRAMSIZ_Pos 16
#define DBGU_CIDR_SRAMSIZ_Msk (0xfu << DBGU_CIDR_SRAMSIZ_Pos) /**< \brief (DBGU_CIDR) Internal SRAM Size */
#define   DBGU_CIDR_SRAMSIZ_1K (0x1u << 16) /**< \brief (DBGU_CIDR) 1K bytes */
#define   DBGU_CIDR_SRAMSIZ_2K (0x2u << 16) /**< \brief (DBGU_CIDR) 2K bytes */
#define   DBGU_CIDR_SRAMSIZ_6K (0x3u << 16) /**< \brief (DBGU_CIDR) 6K bytes */
#define   DBGU_CIDR_SRAMSIZ_112K (0x4u << 16) /**< \brief (DBGU_CIDR) 112K bytes */
#define   DBGU_CIDR_SRAMSIZ_4K (0x5u << 16) /**< \brief (DBGU_CIDR) 4K bytes */
#define   DBGU_CIDR_SRAMSIZ_80K (0x6u << 16) /**< \brief (DBGU_CIDR) 80K bytes */
#define   DBGU_CIDR_SRAMSIZ_160K (0x7u << 16) /**< \brief (DBGU_CIDR) 160K bytes */
#define   DBGU_CIDR_SRAMSIZ_8K (0x8u << 16) /**< \brief (DBGU_CIDR) 8K bytes */
#define   DBGU_CIDR_SRAMSIZ_16K (0x9u << 16) /**< \brief (DBGU_CIDR) 16K bytes */
#define   DBGU_CIDR_SRAMSIZ_32K (0xAu << 16) /**< \brief (DBGU_CIDR) 32K bytes */
#define   DBGU_CIDR_SRAMSIZ_64K (0xBu << 16) /**< \brief (DBGU_CIDR) 64K bytes */
#define   DBGU_CIDR_SRAMSIZ_128K (0xCu << 16) /**< \brief (DBGU_CIDR) 128K bytes */
#define   DBGU_CIDR_SRAMSIZ_256K (0xDu << 16) /**< \brief (DBGU_CIDR) 256K bytes */
#define   DBGU_CIDR_SRAMSIZ_96K (0xEu << 16) /**< \brief (DBGU_CIDR) 96K bytes */
#define   DBGU_CIDR_SRAMSIZ_512K (0xFu << 16) /**< \brief (DBGU_CIDR) 512K bytes */
#define DBGU_CIDR_ARCH_Pos 20
#define DBGU_CIDR_ARCH_Msk (0xffu << DBGU_CIDR_ARCH_Pos) /**< \brief (DBGU_CIDR) Architecture Identifier */
#define   DBGU_CIDR_ARCH_AT91SAM9xx (0x19u << 20) /**< \brief (DBGU_CIDR) AT91SAM9xx Series */
#define   DBGU_CIDR_ARCH_AT91SAM9XExx (0x29u << 20) /**< \brief (DBGU_CIDR) AT91SAM9XExx Series */
#define   DBGU_CIDR_ARCH_AT91x34 (0x34u << 20) /**< \brief (DBGU_CIDR) AT91x34 Series */
#define   DBGU_CIDR_ARCH_CAP7 (0x37u << 20) /**< \brief (DBGU_CIDR) CAP7 Series */
#define   DBGU_CIDR_ARCH_CAP9 (0x39u << 20) /**< \brief (DBGU_CIDR) CAP9 Series */
#define   DBGU_CIDR_ARCH_CAP11 (0x3Bu << 20) /**< \brief (DBGU_CIDR) CAP11 Series */
#define   DBGU_CIDR_ARCH_AT91x40 (0x40u << 20) /**< \brief (DBGU_CIDR) AT91x40 Series */
#define   DBGU_CIDR_ARCH_AT91x42 (0x42u << 20) /**< \brief (DBGU_CIDR) AT91x42 Series */
#define   DBGU_CIDR_ARCH_AT91x55 (0x55u << 20) /**< \brief (DBGU_CIDR) AT91x55 Series */
#define   DBGU_CIDR_ARCH_AT91SAM7Axx (0x60u << 20) /**< \brief (DBGU_CIDR) AT91SAM7Axx Series */
#define   DBGU_CIDR_ARCH_AT91SAM7AQxx (0x61u << 20) /**< \brief (DBGU_CIDR) AT91SAM7AQxx Series */
#define   DBGU_CIDR_ARCH_AT91x63 (0x63u << 20) /**< \brief (DBGU_CIDR) AT91x63 Series */
#define   DBGU_CIDR_ARCH_AT91SAM7Sxx (0x70u << 20) /**< \brief (DBGU_CIDR) AT91SAM7Sxx Series */
#define   DBGU_CIDR_ARCH_AT91SAM7XCxx (0x71u << 20) /**< \brief (DBGU_CIDR) AT91SAM7XCxx Series */
#define   DBGU_CIDR_ARCH_AT91SAM7SExx (0x72u << 20) /**< \brief (DBGU_CIDR) AT91SAM7SExx Series */
#define   DBGU_CIDR_ARCH_AT91SAM7Lxx (0x73u << 20) /**< \brief (DBGU_CIDR) AT91SAM7Lxx Series */
#define   DBGU_CIDR_ARCH_AT91SAM7Xxx (0x75u << 20) /**< \brief (DBGU_CIDR) AT91SAM7Xxx Series */
#define   DBGU_CIDR_ARCH_AT91SAM7SLxx (0x76u << 20) /**< \brief (DBGU_CIDR) AT91SAM7SLxx Series */
#define   DBGU_CIDR_ARCH_ATSAM3UxC (0x80u << 20) /**< \brief (DBGU_CIDR) ATSAM3UxC Series (100-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3UxE (0x81u << 20) /**< \brief (DBGU_CIDR) ATSAM3UxE Series (144-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3AxC (0x83u << 20) /**< \brief (DBGU_CIDR) ATSAM3AxC Series (100-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3XxC (0x84u << 20) /**< \brief (DBGU_CIDR) ATSAM3XxC Series (100-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3XxE (0x85u << 20) /**< \brief (DBGU_CIDR) ATSAM3XxE Series (144-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3XxG (0x86u << 20) /**< \brief (DBGU_CIDR) ATSAM3XxG Series (208/217-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3SxA (0x88u << 20) /**< \brief (DBGU_CIDR) ATSAM3SxA Series (48-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3SxB (0x89u << 20) /**< \brief (DBGU_CIDR) ATSAM3SxB Series (64-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3SxC (0x8Au << 20) /**< \brief (DBGU_CIDR) ATSAM3SxC Series (100-pin version) */
#define   DBGU_CIDR_ARCH_AT91x92 (0x92u << 20) /**< \brief (DBGU_CIDR) AT91x92 Series */
#define   DBGU_CIDR_ARCH_ATSAM3NxA (0x93u << 20) /**< \brief (DBGU_CIDR) ATSAM3NxA Series (48-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3NxB (0x94u << 20) /**< \brief (DBGU_CIDR) ATSAM3NxB Series (64-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3NxC (0x95u << 20) /**< \brief (DBGU_CIDR) ATSAM3NxC Series (100-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3SDxA (0x98u << 20) /**< \brief (DBGU_CIDR) ATSAM3SDxA Series (48-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3SDxB (0x99u << 20) /**< \brief (DBGU_CIDR) ATSAM3SDxB Series (64-pin version) */
#define   DBGU_CIDR_ARCH_ATSAM3SDxC (0x9Au << 20) /**< \brief (DBGU_CIDR) ATSAM3SDxC Series (100-pin version) */
#define   DBGU_CIDR_ARCH_AT75Cxx (0xF0u << 20) /**< \brief (DBGU_CIDR) AT75Cxx Series */
#define DBGU_CIDR_NVPTYP_Pos 28
#define DBGU_CIDR_NVPTYP_Msk (0x7u << DBGU_CIDR_NVPTYP_Pos) /**< \brief (DBGU_CIDR) Nonvolatile Program Memory Type */
#define   DBGU_CIDR_NVPTYP_ROM (0x0u << 28) /**< \brief (DBGU_CIDR) ROM */
#define   DBGU_CIDR_NVPTYP_ROMLESS (0x1u << 28) /**< \brief (DBGU_CIDR) ROMless or on-chip Flash */
#define   DBGU_CIDR_NVPTYP_FLASH (0x2u << 28) /**< \brief (DBGU_CIDR) Embedded Flash Memory */
#define   DBGU_CIDR_NVPTYP_ROM_FLASH (0x3u << 28) /**< \brief (DBGU_CIDR) ROM and Embedded Flash MemoryNVPSIZ is ROM size      NVPSIZ2 is Flash size */
#define   DBGU_CIDR_NVPTYP_SRAM (0x4u << 28) /**< \brief (DBGU_CIDR) SRAM emulating ROM */
#define DBGU_CIDR_EXT (0x1u << 31) /**< \brief (DBGU_CIDR) Extension Flag */
/* -------- DBGU_EXID : (DBGU Offset: 0x0044) Chip ID Extension Register -------- */
#define DBGU_EXID_EXID_Pos 0
#define DBGU_EXID_EXID_Msk (0xffffffffu << DBGU_EXID_EXID_Pos) /**< \brief (DBGU_EXID) Chip ID Extension */
/* -------- DBGU_FNR : (DBGU Offset: 0x0048) Force NTRST Register -------- */
#define DBGU_FNR_FNTRST (0x1u << 0) /**< \brief (DBGU_FNR) Force NTRST */

/*@}*/


#endif /* _SAMA5_DBGU_COMPONENT_ */
