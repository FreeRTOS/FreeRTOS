/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2015, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMA5D2_SPI_COMPONENT_
#define _SAMA5D2_SPI_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Serial Peripheral Interface */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SPI Serial Peripheral Interface */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Spi hardware registers */
typedef struct {
  __O  uint32_t SPI_CR;        /**< \brief (Spi Offset: 0x00) Control Register */
  __IO uint32_t SPI_MR;        /**< \brief (Spi Offset: 0x04) Mode Register */
  __I  uint32_t SPI_RDR;       /**< \brief (Spi Offset: 0x08) Receive Data Register */
  __O  uint32_t SPI_TDR;       /**< \brief (Spi Offset: 0x0C) Transmit Data Register */
  __I  uint32_t SPI_SR;        /**< \brief (Spi Offset: 0x10) Status Register */
  __O  uint32_t SPI_IER;       /**< \brief (Spi Offset: 0x14) Interrupt Enable Register */
  __O  uint32_t SPI_IDR;       /**< \brief (Spi Offset: 0x18) Interrupt Disable Register */
  __I  uint32_t SPI_IMR;       /**< \brief (Spi Offset: 0x1C) Interrupt Mask Register */
  __I  uint32_t Reserved1[4];
  __IO uint32_t SPI_CSR[4];    /**< \brief (Spi Offset: 0x30) Chip Select Register */
  __IO uint32_t SPI_FMR;       /**< \brief (Spi Offset: 0x40) FIFO Mode Register */
  __I  uint32_t SPI_FLR;       /**< \brief (Spi Offset: 0x44) FIFO Level Register */
  __I  uint32_t SPI_CMPR;      /**< \brief (Spi Offset: 0x48) Comparison Register */
  __I  uint32_t Reserved2[38];
  __IO uint32_t SPI_WPMR;      /**< \brief (Spi Offset: 0xE4) Write Protection Mode Register */
  __I  uint32_t SPI_WPSR;      /**< \brief (Spi Offset: 0xE8) Write Protection Status Register */
  __I  uint32_t Reserved3[4];
  __I  uint32_t SPI_VERSION;   /**< \brief (Spi Offset: 0xFC) Version Register */
} Spi;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SPI_CR : (SPI Offset: 0x00) Control Register -------- */
#define SPI_CR_SPIEN (0x1u << 0) /**< \brief (SPI_CR) SPI Enable */
#define SPI_CR_SPIDIS (0x1u << 1) /**< \brief (SPI_CR) SPI Disable */
#define SPI_CR_SWRST (0x1u << 7) /**< \brief (SPI_CR) SPI Software Reset */
#define SPI_CR_REQCLR (0x1u << 12) /**< \brief (SPI_CR) Request to Clear the Comparison Trigger */
#define SPI_CR_TXFCLR (0x1u << 16) /**< \brief (SPI_CR) Transmit FIFO Clear */
#define SPI_CR_RXFCLR (0x1u << 17) /**< \brief (SPI_CR) Receive FIFO Clear */
#define SPI_CR_LASTXFER (0x1u << 24) /**< \brief (SPI_CR) Last Transfer */
#define SPI_CR_FIFOEN (0x1u << 30) /**< \brief (SPI_CR) FIFO Enable */
#define SPI_CR_FIFODIS (0x1u << 31) /**< \brief (SPI_CR) FIFO Disable */
/* -------- SPI_MR : (SPI Offset: 0x04) Mode Register -------- */
#define SPI_MR_MSTR (0x1u << 0) /**< \brief (SPI_MR) Master/Slave Mode */
#define SPI_MR_PS (0x1u << 1) /**< \brief (SPI_MR) Peripheral Select */
#define SPI_MR_PCSDEC (0x1u << 2) /**< \brief (SPI_MR) Chip Select Decode */
#define SPI_MR_MODFDIS (0x1u << 4) /**< \brief (SPI_MR) Mode Fault Detection */
#define SPI_MR_WDRBT (0x1u << 5) /**< \brief (SPI_MR) Wait Data Read Before Transfer */
#define SPI_MR_LLB (0x1u << 7) /**< \brief (SPI_MR) Local Loopback Enable */
#define SPI_MR_CMPMODE (0x1u << 12) /**< \brief (SPI_MR) Comparison Mode */
#define   SPI_MR_CMPMODE_FLAG_ONLY (0x0u << 12) /**< \brief (SPI_MR) Any character is received and comparison function drives CMP flag. */
#define   SPI_MR_CMPMODE_START_CONDITION (0x1u << 12) /**< \brief (SPI_MR) Comparison condition must be met to start reception of all incoming characters until REQCLR is set. */
#define SPI_MR_PCS_Pos 16
#define SPI_MR_PCS_Msk (0xfu << SPI_MR_PCS_Pos) /**< \brief (SPI_MR) Peripheral Chip Select */
#define SPI_MR_PCS(value) ((SPI_MR_PCS_Msk & ((value) << SPI_MR_PCS_Pos)))
#define SPI_MR_DLYBCS_Pos 24
#define SPI_MR_DLYBCS_Msk (0xffu << SPI_MR_DLYBCS_Pos) /**< \brief (SPI_MR) Delay Between Chip Selects */
#define SPI_MR_DLYBCS(value) ((SPI_MR_DLYBCS_Msk & ((value) << SPI_MR_DLYBCS_Pos)))
/* -------- SPI_RDR : (SPI Offset: 0x08) Receive Data Register -------- */
#define SPI_RDR_RD_Pos 0
#define SPI_RDR_RD_Msk (0xffffu << SPI_RDR_RD_Pos) /**< \brief (SPI_RDR) Receive Data */
#define SPI_RDR_PCS_Pos 16
#define SPI_RDR_PCS_Msk (0xfu << SPI_RDR_PCS_Pos) /**< \brief (SPI_RDR) Peripheral Chip Select */
#define SPI_RDR_RD0_Pos 0
#define SPI_RDR_RD0_Msk (0xffu << SPI_RDR_RD0_Pos) /**< \brief (SPI_RDR) Receive Data */
#define SPI_RDR_RD1_Pos 8
#define SPI_RDR_RD1_Msk (0xffu << SPI_RDR_RD1_Pos) /**< \brief (SPI_RDR) Receive Data */
#define SPI_RDR_RD2_Pos 16
#define SPI_RDR_RD2_Msk (0xffu << SPI_RDR_RD2_Pos) /**< \brief (SPI_RDR) Receive Data */
#define SPI_RDR_RD3_Pos 24
#define SPI_RDR_RD3_Msk (0xffu << SPI_RDR_RD3_Pos) /**< \brief (SPI_RDR) Receive Data */
#define SPI_RDR_RD0_FIFO_MULTI_DATA_16_Pos 0
#define SPI_RDR_RD0_FIFO_MULTI_DATA_16_Msk (0xffffu << SPI_RDR_RD0_FIFO_MULTI_DATA_16_Pos) /**< \brief (SPI_RDR) Receive Data */
#define SPI_RDR_RD1_FIFO_MULTI_DATA_16_Pos 16
#define SPI_RDR_RD1_FIFO_MULTI_DATA_16_Msk (0xffffu << SPI_RDR_RD1_FIFO_MULTI_DATA_16_Pos) /**< \brief (SPI_RDR) Receive Data */
/* -------- SPI_TDR : (SPI Offset: 0x0C) Transmit Data Register -------- */
#define SPI_TDR_TD_Pos 0
#define SPI_TDR_TD_Msk (0xffffu << SPI_TDR_TD_Pos) /**< \brief (SPI_TDR) Transmit Data */
#define SPI_TDR_TD(value) ((SPI_TDR_TD_Msk & ((value) << SPI_TDR_TD_Pos)))
#define SPI_TDR_PCS_Pos 16
#define SPI_TDR_PCS_Msk (0xfu << SPI_TDR_PCS_Pos) /**< \brief (SPI_TDR) Peripheral Chip Select */
#define SPI_TDR_PCS(value) ((SPI_TDR_PCS_Msk & ((value) << SPI_TDR_PCS_Pos)))
#define SPI_TDR_LASTXFER (0x1u << 24) /**< \brief (SPI_TDR) Last Transfer */
#define SPI_TDR_TD0_Pos 0
#define SPI_TDR_TD0_Msk (0xffffu << SPI_TDR_TD0_Pos) /**< \brief (SPI_TDR) Transmit Data */
#define SPI_TDR_TD0(value) ((SPI_TDR_TD0_Msk & ((value) << SPI_TDR_TD0_Pos)))
#define SPI_TDR_TD1_Pos 16
#define SPI_TDR_TD1_Msk (0xffffu << SPI_TDR_TD1_Pos) /**< \brief (SPI_TDR) Transmit Data */
#define SPI_TDR_TD1(value) ((SPI_TDR_TD1_Msk & ((value) << SPI_TDR_TD1_Pos)))
/* -------- SPI_SR : (SPI Offset: 0x10) Status Register -------- */
#define SPI_SR_RDRF (0x1u << 0) /**< \brief (SPI_SR) Receive Data Register Full (cleared by reading SPI_RDR) */
#define SPI_SR_TDRE (0x1u << 1) /**< \brief (SPI_SR) Transmit Data Register Empty (cleared by writing SPI_TDR) */
#define SPI_SR_MODF (0x1u << 2) /**< \brief (SPI_SR) Mode Fault Error (cleared on read) */
#define SPI_SR_OVRES (0x1u << 3) /**< \brief (SPI_SR) Overrun Error Status (cleared on read) */
#define SPI_SR_NSSR (0x1u << 8) /**< \brief (SPI_SR) NSS Rising (cleared on read) */
#define SPI_SR_TXEMPTY (0x1u << 9) /**< \brief (SPI_SR) Transmission Registers Empty (cleared by writing SPI_TDR) */
#define SPI_SR_UNDES (0x1u << 10) /**< \brief (SPI_SR) Underrun Error Status (Slave mode only) (cleared on read) */
#define SPI_SR_CMP (0x1u << 11) /**< \brief (SPI_SR) Comparison Status (cleared on read) */
#define SPI_SR_SPIENS (0x1u << 16) /**< \brief (SPI_SR) SPI Enable Status */
#define SPI_SR_TXFEF (0x1u << 24) /**< \brief (SPI_SR) Transmit FIFO Empty Flag (cleared on read) */
#define SPI_SR_TXFFF (0x1u << 25) /**< \brief (SPI_SR) Transmit FIFO Full Flag (cleared on read) */
#define SPI_SR_TXFTHF (0x1u << 26) /**< \brief (SPI_SR) Transmit FIFO Threshold Flag (cleared on read) */
#define SPI_SR_RXFEF (0x1u << 27) /**< \brief (SPI_SR) Receive FIFO Empty Flag */
#define SPI_SR_RXFFF (0x1u << 28) /**< \brief (SPI_SR) Receive FIFO Full Flag */
#define SPI_SR_RXFTHF (0x1u << 29) /**< \brief (SPI_SR) Receive FIFO Threshold Flag */
#define SPI_SR_TXFPTEF (0x1u << 30) /**< \brief (SPI_SR) Transmit FIFO Pointer Error Flag */
#define SPI_SR_RXFPTEF (0x1u << 31) /**< \brief (SPI_SR) Receive FIFO Pointer Error Flag */
/* -------- SPI_IER : (SPI Offset: 0x14) Interrupt Enable Register -------- */
#define SPI_IER_RDRF (0x1u << 0) /**< \brief (SPI_IER) Receive Data Register Full Interrupt Enable */
#define SPI_IER_TDRE (0x1u << 1) /**< \brief (SPI_IER) SPI Transmit Data Register Empty Interrupt Enable */
#define SPI_IER_MODF (0x1u << 2) /**< \brief (SPI_IER) Mode Fault Error Interrupt Enable */
#define SPI_IER_OVRES (0x1u << 3) /**< \brief (SPI_IER) Overrun Error Interrupt Enable */
#define SPI_IER_NSSR (0x1u << 8) /**< \brief (SPI_IER) NSS Rising Interrupt Enable */
#define SPI_IER_TXEMPTY (0x1u << 9) /**< \brief (SPI_IER) Transmission Registers Empty Enable */
#define SPI_IER_UNDES (0x1u << 10) /**< \brief (SPI_IER) Underrun Error Interrupt Enable */
#define SPI_IER_CMP (0x1u << 11) /**< \brief (SPI_IER) Comparison Interrupt Enable */
#define SPI_IER_TXFEF (0x1u << 24) /**< \brief (SPI_IER) TXFEF Interrupt Enable */
#define SPI_IER_TXFFF (0x1u << 25) /**< \brief (SPI_IER) TXFFF Interrupt Enable */
#define SPI_IER_TXFTHF (0x1u << 26) /**< \brief (SPI_IER) TXFTHF Interrupt Enable */
#define SPI_IER_RXFEF (0x1u << 27) /**< \brief (SPI_IER) RXFEF Interrupt Enable */
#define SPI_IER_RXFFF (0x1u << 28) /**< \brief (SPI_IER) RXFFF Interrupt Enable */
#define SPI_IER_RXFTHF (0x1u << 29) /**< \brief (SPI_IER) RXFTHF Interrupt Enable */
#define SPI_IER_TXFPTEF (0x1u << 30) /**< \brief (SPI_IER) TXFPTEF Interrupt Enable */
#define SPI_IER_RXFPTEF (0x1u << 31) /**< \brief (SPI_IER) RXFPTEF Interrupt Enable */
/* -------- SPI_IDR : (SPI Offset: 0x18) Interrupt Disable Register -------- */
#define SPI_IDR_RDRF (0x1u << 0) /**< \brief (SPI_IDR) Receive Data Register Full Interrupt Disable */
#define SPI_IDR_TDRE (0x1u << 1) /**< \brief (SPI_IDR) SPI Transmit Data Register Empty Interrupt Disable */
#define SPI_IDR_MODF (0x1u << 2) /**< \brief (SPI_IDR) Mode Fault Error Interrupt Disable */
#define SPI_IDR_OVRES (0x1u << 3) /**< \brief (SPI_IDR) Overrun Error Interrupt Disable */
#define SPI_IDR_NSSR (0x1u << 8) /**< \brief (SPI_IDR) NSS Rising Interrupt Disable */
#define SPI_IDR_TXEMPTY (0x1u << 9) /**< \brief (SPI_IDR) Transmission Registers Empty Disable */
#define SPI_IDR_UNDES (0x1u << 10) /**< \brief (SPI_IDR) Underrun Error Interrupt Disable */
#define SPI_IDR_CMP (0x1u << 11) /**< \brief (SPI_IDR) Comparison Interrupt Disable */
#define SPI_IDR_TXFEF (0x1u << 24) /**< \brief (SPI_IDR) TXFEF Interrupt Disable */
#define SPI_IDR_TXFFF (0x1u << 25) /**< \brief (SPI_IDR) TXFFF Interrupt Disable */
#define SPI_IDR_TXFTHF (0x1u << 26) /**< \brief (SPI_IDR) TXFTHF Interrupt Disable */
#define SPI_IDR_RXFEF (0x1u << 27) /**< \brief (SPI_IDR) RXFEF Interrupt Disable */
#define SPI_IDR_RXFFF (0x1u << 28) /**< \brief (SPI_IDR) RXFFF Interrupt Disable */
#define SPI_IDR_RXFTHF (0x1u << 29) /**< \brief (SPI_IDR) RXFTHF Interrupt Disable */
#define SPI_IDR_TXFPTEF (0x1u << 30) /**< \brief (SPI_IDR) TXFPTEF Interrupt Disable */
#define SPI_IDR_RXFPTEF (0x1u << 31) /**< \brief (SPI_IDR) RXFPTEF Interrupt Disable */
/* -------- SPI_IMR : (SPI Offset: 0x1C) Interrupt Mask Register -------- */
#define SPI_IMR_RDRF (0x1u << 0) /**< \brief (SPI_IMR) Receive Data Register Full Interrupt Mask */
#define SPI_IMR_TDRE (0x1u << 1) /**< \brief (SPI_IMR) SPI Transmit Data Register Empty Interrupt Mask */
#define SPI_IMR_MODF (0x1u << 2) /**< \brief (SPI_IMR) Mode Fault Error Interrupt Mask */
#define SPI_IMR_OVRES (0x1u << 3) /**< \brief (SPI_IMR) Overrun Error Interrupt Mask */
#define SPI_IMR_NSSR (0x1u << 8) /**< \brief (SPI_IMR) NSS Rising Interrupt Mask */
#define SPI_IMR_TXEMPTY (0x1u << 9) /**< \brief (SPI_IMR) Transmission Registers Empty Mask */
#define SPI_IMR_UNDES (0x1u << 10) /**< \brief (SPI_IMR) Underrun Error Interrupt Mask */
#define SPI_IMR_CMP (0x1u << 11) /**< \brief (SPI_IMR) Comparison Interrupt Mask */
#define SPI_IMR_TXFEF (0x1u << 24) /**< \brief (SPI_IMR) TXFEF Interrupt Mask */
#define SPI_IMR_TXFFF (0x1u << 25) /**< \brief (SPI_IMR) TXFFF Interrupt Mask */
#define SPI_IMR_TXFTHF (0x1u << 26) /**< \brief (SPI_IMR) TXFTHF Interrupt Mask */
#define SPI_IMR_RXFEF (0x1u << 27) /**< \brief (SPI_IMR) RXFEF Interrupt Mask */
#define SPI_IMR_RXFFF (0x1u << 28) /**< \brief (SPI_IMR) RXFFF Interrupt Mask */
#define SPI_IMR_RXFTHF (0x1u << 29) /**< \brief (SPI_IMR) RXFTHF Interrupt Mask */
#define SPI_IMR_TXFPTEF (0x1u << 30) /**< \brief (SPI_IMR) TXFPTEF Interrupt Mask */
#define SPI_IMR_RXFPTEF (0x1u << 31) /**< \brief (SPI_IMR) RXFPTEF Interrupt Mask */
/* -------- SPI_CSR[4] : (SPI Offset: 0x30) Chip Select Register -------- */
#define SPI_CSR_CPOL (0x1u << 0) /**< \brief (SPI_CSR[4]) Clock Polarity */
#define SPI_CSR_NCPHA (0x1u << 1) /**< \brief (SPI_CSR[4]) Clock Phase */
#define SPI_CSR_CSNAAT (0x1u << 2) /**< \brief (SPI_CSR[4]) Chip Select Not Active After Transfer (Ignored if CSAAT = 1) */
#define SPI_CSR_CSAAT (0x1u << 3) /**< \brief (SPI_CSR[4]) Chip Select Active After Transfer */
#define SPI_CSR_BITS_Pos 4
#define SPI_CSR_BITS_Msk (0xfu << SPI_CSR_BITS_Pos) /**< \brief (SPI_CSR[4]) Bits Per Transfer */
#define SPI_CSR_BITS(value) ((SPI_CSR_BITS_Msk & ((value) << SPI_CSR_BITS_Pos)))
#define   SPI_CSR_BITS_8_BIT (0x0u << 4) /**< \brief (SPI_CSR[4]) 8 bits for transfer */
#define   SPI_CSR_BITS_9_BIT (0x1u << 4) /**< \brief (SPI_CSR[4]) 9 bits for transfer */
#define   SPI_CSR_BITS_10_BIT (0x2u << 4) /**< \brief (SPI_CSR[4]) 10 bits for transfer */
#define   SPI_CSR_BITS_11_BIT (0x3u << 4) /**< \brief (SPI_CSR[4]) 11 bits for transfer */
#define   SPI_CSR_BITS_12_BIT (0x4u << 4) /**< \brief (SPI_CSR[4]) 12 bits for transfer */
#define   SPI_CSR_BITS_13_BIT (0x5u << 4) /**< \brief (SPI_CSR[4]) 13 bits for transfer */
#define   SPI_CSR_BITS_14_BIT (0x6u << 4) /**< \brief (SPI_CSR[4]) 14 bits for transfer */
#define   SPI_CSR_BITS_15_BIT (0x7u << 4) /**< \brief (SPI_CSR[4]) 15 bits for transfer */
#define   SPI_CSR_BITS_16_BIT (0x8u << 4) /**< \brief (SPI_CSR[4]) 16 bits for transfer */
#define SPI_CSR_SCBR_Pos 8
#define SPI_CSR_SCBR_Msk (0xffu << SPI_CSR_SCBR_Pos) /**< \brief (SPI_CSR[4]) Serial Clock Bit Rate */
#define SPI_CSR_SCBR(value) ((SPI_CSR_SCBR_Msk & ((value) << SPI_CSR_SCBR_Pos)))
#define SPI_CSR_DLYBS_Pos 16
#define SPI_CSR_DLYBS_Msk (0xffu << SPI_CSR_DLYBS_Pos) /**< \brief (SPI_CSR[4]) Delay Before SPCK */
#define SPI_CSR_DLYBS(value) ((SPI_CSR_DLYBS_Msk & ((value) << SPI_CSR_DLYBS_Pos)))
#define SPI_CSR_DLYBCT_Pos 24
#define SPI_CSR_DLYBCT_Msk (0xffu << SPI_CSR_DLYBCT_Pos) /**< \brief (SPI_CSR[4]) Delay Between Consecutive Transfers */
#define SPI_CSR_DLYBCT(value) ((SPI_CSR_DLYBCT_Msk & ((value) << SPI_CSR_DLYBCT_Pos)))
/* -------- SPI_FMR : (SPI Offset: 0x40) FIFO Mode Register -------- */
#define SPI_FMR_TXRDYM_Pos 0
#define SPI_FMR_TXRDYM_Msk (0x3u << SPI_FMR_TXRDYM_Pos) /**< \brief (SPI_FMR) Transmitter Data Register Empty Mode */
#define SPI_FMR_TXRDYM(value) ((SPI_FMR_TXRDYM_Msk & ((value) << SPI_FMR_TXRDYM_Pos)))
#define   SPI_FMR_TXRDYM_ONE_DATA (0x0u << 0) /**< \brief (SPI_FMR) TDRE will be at level '1' when at least one data can be written in the Transmit FIFO. */
#define   SPI_FMR_TXRDYM_TWO_DATA (0x1u << 0) /**< \brief (SPI_FMR) TDRE will be at level '1' when at least two data can be written in the Transmit FIFO. */
#define   SPI_FMR_TXRDYM_FOUR_DATA (0x2u << 0) /**< \brief (SPI_FMR) TDRE will be at level '1' when at least four data can be written in the Transmit FIFO. */
#define SPI_FMR_RXRDYM_Pos 4
#define SPI_FMR_RXRDYM_Msk (0x3u << SPI_FMR_RXRDYM_Pos) /**< \brief (SPI_FMR) Receiver Data Register Full Mode */
#define SPI_FMR_RXRDYM(value) ((SPI_FMR_RXRDYM_Msk & ((value) << SPI_FMR_RXRDYM_Pos)))
#define   SPI_FMR_RXRDYM_ONE_DATA (0x0u << 4) /**< \brief (SPI_FMR) RDRF will be at level '1' when at least one unread data is in the Receive FIFO. */
#define   SPI_FMR_RXRDYM_TWO_DATA (0x1u << 4) /**< \brief (SPI_FMR) RDRF will be at level '1' when at least two unread data are in the Receive FIFO. */
#define   SPI_FMR_RXRDYM_FOUR_DATA (0x2u << 4) /**< \brief (SPI_FMR) RDRF will be at level '1' when at least four unread data are in the Receive FIFO. */
#define SPI_FMR_TXFTHRES_Pos 16
#define SPI_FMR_TXFTHRES_Msk (0x3fu << SPI_FMR_TXFTHRES_Pos) /**< \brief (SPI_FMR) Transmit FIFO Threshold */
#define SPI_FMR_TXFTHRES(value) ((SPI_FMR_TXFTHRES_Msk & ((value) << SPI_FMR_TXFTHRES_Pos)))
#define SPI_FMR_RXFTHRES_Pos 24
#define SPI_FMR_RXFTHRES_Msk (0x3fu << SPI_FMR_RXFTHRES_Pos) /**< \brief (SPI_FMR) Receive FIFO Threshold */
#define SPI_FMR_RXFTHRES(value) ((SPI_FMR_RXFTHRES_Msk & ((value) << SPI_FMR_RXFTHRES_Pos)))
/* -------- SPI_FLR : (SPI Offset: 0x44) FIFO Level Register -------- */
#define SPI_FLR_TXFL_Pos 0
#define SPI_FLR_TXFL_Msk (0x3fu << SPI_FLR_TXFL_Pos) /**< \brief (SPI_FLR) Transmit FIFO Level */
#define SPI_FLR_RXFL_Pos 16
#define SPI_FLR_RXFL_Msk (0x3fu << SPI_FLR_RXFL_Pos) /**< \brief (SPI_FLR) Receive FIFO Level */
/* -------- SPI_CMPR : (SPI Offset: 0x48) Comparison Register -------- */
#define SPI_CMPR_VAL1_Pos 0
#define SPI_CMPR_VAL1_Msk (0xffffu << SPI_CMPR_VAL1_Pos) /**< \brief (SPI_CMPR) First Comparison Value for Received Character */
#define SPI_CMPR_VAL2_Pos 16
#define SPI_CMPR_VAL2_Msk (0xffffu << SPI_CMPR_VAL2_Pos) /**< \brief (SPI_CMPR) Second Comparison Value for Received Character */
/* -------- SPI_WPMR : (SPI Offset: 0xE4) Write Protection Mode Register -------- */
#define SPI_WPMR_WPEN (0x1u << 0) /**< \brief (SPI_WPMR) Write Protection Enable */
#define SPI_WPMR_WPKEY_Pos 8
#define SPI_WPMR_WPKEY_Msk (0xffffffu << SPI_WPMR_WPKEY_Pos) /**< \brief (SPI_WPMR) Write Protection Key */
#define SPI_WPMR_WPKEY(value) ((SPI_WPMR_WPKEY_Msk & ((value) << SPI_WPMR_WPKEY_Pos)))
#define   SPI_WPMR_WPKEY_PASSWD (0x535049u << 8) /**< \brief (SPI_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0. */
/* -------- SPI_WPSR : (SPI Offset: 0xE8) Write Protection Status Register -------- */
#define SPI_WPSR_WPVS (0x1u << 0) /**< \brief (SPI_WPSR) Write Protection Violation Status */
#define SPI_WPSR_WPVSRC_Pos 8
#define SPI_WPSR_WPVSRC_Msk (0xffu << SPI_WPSR_WPVSRC_Pos) /**< \brief (SPI_WPSR) Write Protection Violation Source */
/* -------- SPI_VERSION : (SPI Offset: 0xFC) Version Register -------- */
#define SPI_VERSION_VERSION_Pos 0
#define SPI_VERSION_VERSION_Msk (0xfffu << SPI_VERSION_VERSION_Pos) /**< \brief (SPI_VERSION) Version of the Hardware Module */
#define SPI_VERSION_MFN_Pos 16
#define SPI_VERSION_MFN_Msk (0x7u << SPI_VERSION_MFN_Pos) /**< \brief (SPI_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_SPI_COMPONENT_ */
