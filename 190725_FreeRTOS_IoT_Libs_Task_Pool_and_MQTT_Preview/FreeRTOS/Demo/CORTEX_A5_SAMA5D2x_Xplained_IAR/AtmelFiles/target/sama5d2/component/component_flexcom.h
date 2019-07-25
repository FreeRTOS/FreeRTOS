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

#ifndef _SAMA5D2_FLEXCOM_COMPONENT_
#define _SAMA5D2_FLEXCOM_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Flexible Serial Communication */
/* ============================================================================= */
/** \addtogroup SAMA5D2_FLEXCOM Flexible Serial Communication */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))

/** \brief Usart hardware registers */
typedef struct {
	__O  uint32_t US_CR;       /**< \brief (Flexcom Offset: 0x200) USART Control Register */
	__IO uint32_t US_MR;       /**< \brief (Flexcom Offset: 0x204) USART Mode Register */
	__O  uint32_t US_IER;      /**< \brief (Flexcom Offset: 0x208) USART Interrupt Enable Register */
	__O  uint32_t US_IDR;      /**< \brief (Flexcom Offset: 0x20C) USART Interrupt Disable Register */
	__I  uint32_t US_IMR;      /**< \brief (Flexcom Offset: 0x210) USART Interrupt Mask Register */
	__I  uint32_t US_CSR;      /**< \brief (Flexcom Offset: 0x214) USART Channel Status Register */
	__I  uint32_t US_RHR;      /**< \brief (Flexcom Offset: 0x218) USART Receive Holding Register */
	__O  uint32_t US_THR;      /**< \brief (Flexcom Offset: 0x21C) USART Transmit Holding Register */
	__IO uint32_t US_BRGR;     /**< \brief (Flexcom Offset: 0x220) USART Baud Rate Generator Register */
	__IO uint32_t US_RTOR;     /**< \brief (Flexcom Offset: 0x224) USART Receiver Timeout Register */
	__IO uint32_t US_TTGR;     /**< \brief (Flexcom Offset: 0x228) USART Transmitter Timeguard Register */
	__I  uint32_t Reserved5[5];
	__IO uint32_t US_FIDI;     /**< \brief (Flexcom Offset: 0x240) USART FI DI Ratio Register */
	__I  uint32_t US_NER;      /**< \brief (Flexcom Offset: 0x244) USART Number of Errors Register */
	__I  uint32_t Reserved6[1];
	__IO uint32_t US_IF;       /**< \brief (Flexcom Offset: 0x24C) USART IrDA Filter Register */
	__IO uint32_t US_MAN;      /**< \brief (Flexcom Offset: 0x250) USART Manchester Configuration Register */
	__IO uint32_t US_LINMR;    /**< \brief (Flexcom Offset: 0x254) USART LIN Mode Register */
	__IO uint32_t US_LINIR;    /**< \brief (Flexcom Offset: 0x258) USART LIN Identifier Register */
	__I  uint32_t US_LINBRR;   /**< \brief (Flexcom Offset: 0x25C) USART LIN Baud Rate Register */
	__I  uint32_t Reserved7[12];
	__IO uint32_t US_CMPR;     /**< \brief (Flexcom Offset: 0x290) USART Comparison Register */
	__I  uint32_t Reserved8[3];
	__IO uint32_t US_FMR;      /**< \brief (Flexcom Offset: 0x2A0) USART FIFO Mode Register */
	__I  uint32_t US_FLR;      /**< \brief (Flexcom Offset: 0x2A4) USART FIFO Level Register */
	__O  uint32_t US_FIER;     /**< \brief (Flexcom Offset: 0x2A8) USART FIFO Interrupt Enable Register */
	__O  uint32_t US_FIDR;     /**< \brief (Flexcom Offset: 0x2AC) USART FIFO Interrupt Disable Register */
	__I  uint32_t US_FIMR;     /**< \brief (Flexcom Offset: 0x2B0) USART FIFO Interrupt Mask Register */
	__I  uint32_t US_FESR;     /**< \brief (Flexcom Offset: 0x2B4) USART FIFO Event Status Register */
	__I  uint32_t Reserved9[11];
	__IO uint32_t US_WPMR;     /**< \brief (Flexcom Offset: 0x2E4) USART Write Protection Mode Register */
	__I  uint32_t US_WPSR;     /**< \brief (Flexcom Offset: 0x2E8) USART Write Protection Status Register */
	__I  uint32_t Reserved10[4];
	__I  uint32_t US_VERSION;  /**< \brief (Flexcom Offset: 0x2FC) USART Version Register */
} Usart;

/** \brief Spi hardware registers */
typedef struct {
	__O  uint32_t SPI_CR;      /**< \brief (Flexcom Offset: 0x400) SPI Control Register */
	__IO uint32_t SPI_MR;      /**< \brief (Flexcom Offset: 0x404) SPI Mode Register */
	__I  uint32_t SPI_RDR;     /**< \brief (Flexcom Offset: 0x408) SPI Receive Data Register */
	__O  uint32_t SPI_TDR;     /**< \brief (Flexcom Offset: 0x40C) SPI Transmit Data Register */
	__I  uint32_t SPI_SR;      /**< \brief (Flexcom Offset: 0x410) SPI Status Register */
	__O  uint32_t SPI_IER;     /**< \brief (Flexcom Offset: 0x414) SPI Interrupt Enable Register */
	__O  uint32_t SPI_IDR;     /**< \brief (Flexcom Offset: 0x418) SPI Interrupt Disable Register */
	__I  uint32_t SPI_IMR;     /**< \brief (Flexcom Offset: 0x41C) SPI Interrupt Mask Register */
	__I  uint32_t Reserved1[4];
	__IO uint32_t SPI_CSR[2];  /**< \brief (Flexcom Offset: 0x430) SPI Chip Select Register */
	__I  uint32_t Reserved2[2];
	__IO uint32_t SPI_FMR;     /**< \brief (Flexcom Offset: 0x440) SPI FIFO Mode Register */
	__I  uint32_t SPI_FLR;     /**< \brief (Flexcom Offset: 0x444) SPI FIFO Level Register */
	__IO uint32_t SPI_CMPR;    /**< \brief (Flexcom Offset: 0x448) SPI Comparison Register */
	__I  uint32_t Reserved3[38];
	__IO uint32_t SPI_WPMR;    /**< \brief (Flexcom Offset: 0x4E4) SPI Write Protection Mode Register */
	__I  uint32_t SPI_WPSR;    /**< \brief (Flexcom Offset: 0x4E8) SPI Write Protection Status Register */
	__I  uint32_t Reserved4[4];
	__I  uint32_t SPI_VERSION; /**< \brief (Flexcom Offset: 0x4FC) SPI Version Register */
} Spi;

/** \brief Twi hardware registers */
typedef struct {
	__O  uint32_t TWI_CR;      /**< \brief (Flexcom Offset: 0x600) TWI Control Register */
	__IO uint32_t TWI_MMR;     /**< \brief (Flexcom Offset: 0x604) TWI Master Mode Register */
	__IO uint32_t TWI_SMR;     /**< \brief (Flexcom Offset: 0x608) TWI Slave Mode Register */
	__IO uint32_t TWI_IADR;    /**< \brief (Flexcom Offset: 0x60C) TWI Internal Address Register */
	__IO uint32_t TWI_CWGR;    /**< \brief (Flexcom Offset: 0x610) TWI Clock Waveform Generator Register */
	__I  uint32_t Reserved17[3];
	__I  uint32_t TWI_SR;      /**< \brief (Flexcom Offset: 0x620) TWI Status Register */
	__O  uint32_t TWI_IER;     /**< \brief (Flexcom Offset: 0x624) TWI Interrupt Enable Register */
	__O  uint32_t TWI_IDR;     /**< \brief (Flexcom Offset: 0x628) TWI Interrupt Disable Register */
	__I  uint32_t TWI_IMR;     /**< \brief (Flexcom Offset: 0x62C) TWI Interrupt Mask Register */
	__I  uint32_t TWI_RHR;     /**< \brief (Flexcom Offset: 0x630) TWI Receive Holding Register */
	__O  uint32_t TWI_THR;     /**< \brief (Flexcom Offset: 0x634) TWI Transmit Holding Register */
	__IO uint32_t TWI_SMBTR;   /**< \brief (Flexcom Offset: 0x638) TWI SMBus Timing Register */
	__I  uint32_t Reserved18[1];
	__IO uint32_t TWI_ACR;     /**< \brief (Flexcom Offset: 0x640) TWI Alternative Command Register */
	__IO uint32_t TWI_FILTR;   /**< \brief (Flexcom Offset: 0x644) TWI Filter Register */
	__I  uint32_t Reserved19[1];
	__IO uint32_t TWI_SWMR;    /**< \brief (Flexcom Offset: 0x64C) TWI SleepWalking Matching Register */
	__IO uint32_t TWI_FMR;     /**< \brief (Flexcom Offset: 0x650) TWI FIFO Mode Register */
	__I  uint32_t TWI_FLR;     /**< \brief (Flexcom Offset: 0x654) TWI FIFO Level Register */
	__I  uint32_t Reserved20[2];
	__I  uint32_t TWI_FSR;     /**< \brief (Flexcom Offset: 0x660) TWI FIFO Status Register */
	__O  uint32_t TWI_FIER;    /**< \brief (Flexcom Offset: 0x664) TWI FIFO Interrupt Enable Register */
	__O  uint32_t TWI_FIDR;    /**< \brief (Flexcom Offset: 0x668) TWI FIFO Interrupt Disable Register */
	__I  uint32_t TWI_FIMR;    /**< \brief (Flexcom Offset: 0x66C) TWI FIFO Interrupt Mask Register */
	__I  uint32_t Reserved21[24];
	__I  uint32_t TWI_DR;      /**< \brief (Flexcom Offset: 0x6D0) TWI Debug Register */
	__I  uint32_t Reserved22[4];
	__IO uint32_t TWI_WPMR;    /**< \brief (Flexcom Offset: 0x6E4) TWI Protection Mode Register */
	__I  uint32_t TWI_WPSR;    /**< \brief (Flexcom Offset: 0x6E8) TWI Protection Status Register */
	__I  uint32_t Reserved23[4];
	__I  uint32_t TWI_VER;     /**< \brief (Flexcom Offset: 0x6FC) TWI Version Register */
} Twi;

/** \brief Flexcom hardware registers */
typedef struct {
	__IO uint32_t FLEX_MR;          /**< \brief (Flexcom Offset: 0x000) FLEXCOM Mode Register */
	__I  uint32_t Reserved1[3];
	__I  uint32_t FLEX_RHR;         /**< \brief (Flexcom Offset: 0x010) FLEXCOM Receive Holding Register */
	__I  uint32_t Reserved2[3];
	__IO uint32_t FLEX_THR;         /**< \brief (Flexcom Offset: 0x020) FLEXCOM Transmit Holding Register */
	__I  uint32_t Reserved3[54];
	__I  uint32_t FLEX_VERSION;     /**< \brief (Flexcom Offset: 0x0FC) FLEXCOM Version Register */
	__I  uint32_t Reserved4[64];
	     Usart usart;
	__I  uint32_t Reserved11[64];
	     Spi spi;
	__I  uint32_t Reserved16[64];
	     Twi twi;
} Flexcom;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- FLEX_MR : (FLEXCOM Offset: 0x000) FLEXCOM Mode Register -------- */
#define FLEX_MR_OPMODE_Pos 0
#define FLEX_MR_OPMODE_Msk (0x3u << FLEX_MR_OPMODE_Pos) /**< \brief (FLEX_MR) FLEXCOM Operating Mode */
#define FLEX_MR_OPMODE(value) ((FLEX_MR_OPMODE_Msk & ((value) << FLEX_MR_OPMODE_Pos)))
#define   FLEX_MR_OPMODE_NO_COM (0x0u << 0) /**< \brief (FLEX_MR) No communication */
#define   FLEX_MR_OPMODE_USART (0x1u << 0) /**< \brief (FLEX_MR) All related UART related protocols are selected (RS232, RS485, IrDA, ISO7816, LIN,)All SPI/TWI related registers are not accessible and have no impact on IOs. */
#define   FLEX_MR_OPMODE_SPI (0x2u << 0) /**< \brief (FLEX_MR) SPI operating mode is selected.All USART/TWI related registers are not accessible and have no impact on IOs. */
#define   FLEX_MR_OPMODE_TWI (0x3u << 0) /**< \brief (FLEX_MR) All related TWI protocols are selected (TWI, SMBus). All USART/SPI related registers are not accessible and have no impact on IOs. */
/* -------- FLEX_RHR : (FLEXCOM Offset: 0x010) FLEXCOM Receive Holding Register -------- */
#define FLEX_RHR_RXDATA_Pos 0
#define FLEX_RHR_RXDATA_Msk (0xffffu << FLEX_RHR_RXDATA_Pos) /**< \brief (FLEX_RHR) Receive Data */
/* -------- FLEX_THR : (FLEXCOM Offset: 0x020) FLEXCOM Transmit Holding Register -------- */
#define FLEX_THR_TXDATA_Pos 0
#define FLEX_THR_TXDATA_Msk (0xffffu << FLEX_THR_TXDATA_Pos) /**< \brief (FLEX_THR) Transmit Data */
#define FLEX_THR_TXDATA(value) ((FLEX_THR_TXDATA_Msk & ((value) << FLEX_THR_TXDATA_Pos)))
/* -------- FLEX_VERSION : (FLEXCOM Offset: 0x0FC) FLEXCOM Version Register -------- */
#define FLEX_VERSION_VERSION_Pos 0
#define FLEX_VERSION_VERSION_Msk (0xfffu << FLEX_VERSION_VERSION_Pos) /**< \brief (FLEX_VERSION) Hardware Module Version */
#define FLEX_VERSION_MFN_Pos 16
#define FLEX_VERSION_MFN_Msk (0x7u << FLEX_VERSION_MFN_Pos) /**< \brief (FLEX_VERSION) Metal Fix Number */
/* -------- US_CR : (FLEXCOM Offset: 0x200) USART Control Register -------- */
#define US_CR_RSTRX (0x1u << 2) /**< \brief (US_CR) Reset Receiver */
#define US_CR_RSTTX (0x1u << 3) /**< \brief (US_CR) Reset Transmitter */
#define US_CR_RXEN (0x1u << 4) /**< \brief (US_CR) Receiver Enable */
#define US_CR_RXDIS (0x1u << 5) /**< \brief (US_CR) Receiver Disable */
#define US_CR_TXEN (0x1u << 6) /**< \brief (US_CR) Transmitter Enable */
#define US_CR_TXDIS (0x1u << 7) /**< \brief (US_CR) Transmitter Disable */
#define US_CR_RSTSTA (0x1u << 8) /**< \brief (US_CR) Reset Status Bits */
#define US_CR_STTBRK (0x1u << 9) /**< \brief (US_CR) Start Break */
#define US_CR_STPBRK (0x1u << 10) /**< \brief (US_CR) Stop Break */
#define US_CR_STTTO (0x1u << 11) /**< \brief (US_CR) Clear TIMEOUT Flag and Start Time-out After Next Character Received */
#define US_CR_SENDA (0x1u << 12) /**< \brief (US_CR) Send Address */
#define US_CR_RSTIT (0x1u << 13) /**< \brief (US_CR) Reset Iterations */
#define US_CR_RSTNACK (0x1u << 14) /**< \brief (US_CR) Reset Non Acknowledge */
#define US_CR_RETTO (0x1u << 15) /**< \brief (US_CR) Start Time-out Immediately */
#define US_CR_RTSEN (0x1u << 18) /**< \brief (US_CR) Request to Send Enable */
#define US_CR_RTSDIS (0x1u << 19) /**< \brief (US_CR) Request to Send Disable */
#define US_CR_LINABT (0x1u << 20) /**< \brief (US_CR) Abort LIN Transmission */
#define US_CR_LINWKUP (0x1u << 21) /**< \brief (US_CR) Send LIN Wake-up Signal */
#define US_CR_TXFCLR (0x1u << 24) /**< \brief (US_CR) Transmit FIFO Clear */
#define US_CR_RXFCLR (0x1u << 25) /**< \brief (US_CR) Receive FIFO Clear */
#define US_CR_TXFLCLR (0x1u << 26) /**< \brief (US_CR) Transmit FIFO Lock CLEAR */
#define US_CR_REQCLR (0x1u << 28) /**< \brief (US_CR) Request to Clear the Comparison Trigger */
#define US_CR_FIFOEN (0x1u << 30) /**< \brief (US_CR) FIFO Enable */
#define US_CR_FIFODIS (0x1u << 31) /**< \brief (US_CR) FIFO Disable */
/* -------- US_MR : (FLEXCOM Offset: 0x204) USART Mode Register -------- */
#define US_MR_USART_MODE_Pos 0
#define US_MR_USART_MODE_Msk (0xfu << US_MR_USART_MODE_Pos) /**< \brief (US_MR) USART Mode of Operation */
#define US_MR_USART_MODE(value) ((US_MR_USART_MODE_Msk & ((value) << US_MR_USART_MODE_Pos)))
#define   US_MR_USART_MODE_NORMAL (0x0u << 0) /**< \brief (US_MR) Normal mode */
#define   US_MR_USART_MODE_RS485 (0x1u << 0) /**< \brief (US_MR) RS485 */
#define   US_MR_USART_MODE_HW_HANDSHAKING (0x2u << 0) /**< \brief (US_MR) Hardware Handshaking */
#define   US_MR_USART_MODE_IS07816_T_0 (0x4u << 0) /**< \brief (US_MR) IS07816 Protocol: T = 0 */
#define   US_MR_USART_MODE_IS07816_T_1 (0x6u << 0) /**< \brief (US_MR) IS07816 Protocol: T = 1 */
#define   US_MR_USART_MODE_IRDA (0x8u << 0) /**< \brief (US_MR) IrDA */
#define   US_MR_USART_MODE_LIN_MASTER (0xAu << 0) /**< \brief (US_MR) LIN master */
#define   US_MR_USART_MODE_LIN_SLAVE (0xBu << 0) /**< \brief (US_MR) LIN Slave */
#define US_MR_USCLKS_Pos 4
#define US_MR_USCLKS_Msk (0x3u << US_MR_USCLKS_Pos) /**< \brief (US_MR) Clock Selection */
#define US_MR_USCLKS(value) ((US_MR_USCLKS_Msk & ((value) << US_MR_USCLKS_Pos)))
#define   US_MR_USCLKS_MCK (0x0u << 4) /**< \brief (US_MR) Peripheral clock is selected */
#define   US_MR_USCLKS_DIV (0x1u << 4) /**< \brief (US_MR) Peripheral clock divided (DIV = 8) is selected */
#define   US_MR_USCLKS_PMC_PCK (0x2u << 4) /**< \brief (US_MR) PMC programmable clock is selected. If the SCK pin is driven (CLKO = 1), the CD field must be greater than 1. */
#define   US_MR_USCLKS_SCK (0x3u << 4) /**< \brief (US_MR) External pin SCK is selected */
#define US_MR_CHRL_Pos 6
#define US_MR_CHRL_Msk (0x3u << US_MR_CHRL_Pos) /**< \brief (US_MR) Character Length */
#define US_MR_CHRL(value) ((US_MR_CHRL_Msk & ((value) << US_MR_CHRL_Pos)))
#define   US_MR_CHRL_5_BIT (0x0u << 6) /**< \brief (US_MR) Character length is 5 bits */
#define   US_MR_CHRL_6_BIT (0x1u << 6) /**< \brief (US_MR) Character length is 6 bits */
#define   US_MR_CHRL_7_BIT (0x2u << 6) /**< \brief (US_MR) Character length is 7 bits */
#define   US_MR_CHRL_8_BIT (0x3u << 6) /**< \brief (US_MR) Character length is 8 bits */
#define US_MR_SYNC (0x1u << 8) /**< \brief (US_MR) Synchronous Mode Select */
#define US_MR_PAR_Pos 9
#define US_MR_PAR_Msk (0x7u << US_MR_PAR_Pos) /**< \brief (US_MR) Parity Type */
#define US_MR_PAR(value) ((US_MR_PAR_Msk & ((value) << US_MR_PAR_Pos)))
#define   US_MR_PAR_EVEN (0x0u << 9) /**< \brief (US_MR) Even parity */
#define   US_MR_PAR_ODD (0x1u << 9) /**< \brief (US_MR) Odd parity */
#define   US_MR_PAR_SPACE (0x2u << 9) /**< \brief (US_MR) Parity forced to 0 (Space) */
#define   US_MR_PAR_MARK (0x3u << 9) /**< \brief (US_MR) Parity forced to 1 (Mark) */
#define   US_MR_PAR_NO (0x4u << 9) /**< \brief (US_MR) No parity */
#define   US_MR_PAR_MULTIDROP (0x6u << 9) /**< \brief (US_MR) Multidrop mode */
#define US_MR_NBSTOP_Pos 12
#define US_MR_NBSTOP_Msk (0x3u << US_MR_NBSTOP_Pos) /**< \brief (US_MR) Number of Stop Bits */
#define US_MR_NBSTOP(value) ((US_MR_NBSTOP_Msk & ((value) << US_MR_NBSTOP_Pos)))
#define   US_MR_NBSTOP_1_BIT (0x0u << 12) /**< \brief (US_MR) 1 stop bit */
#define   US_MR_NBSTOP_1_5_BIT (0x1u << 12) /**< \brief (US_MR) 1.5 stop bit (SYNC = 0) or reserved (SYNC = 1) */
#define   US_MR_NBSTOP_2_BIT (0x2u << 12) /**< \brief (US_MR) 2 stop bits */
#define US_MR_CHMODE_Pos 14
#define US_MR_CHMODE_Msk (0x3u << US_MR_CHMODE_Pos) /**< \brief (US_MR) Channel Mode */
#define US_MR_CHMODE(value) ((US_MR_CHMODE_Msk & ((value) << US_MR_CHMODE_Pos)))
#define   US_MR_CHMODE_NORMAL (0x0u << 14) /**< \brief (US_MR) Normal mode */
#define   US_MR_CHMODE_AUTOMATIC (0x1u << 14) /**< \brief (US_MR) Automatic Echo. Receiver input is connected to the TXD pin. */
#define   US_MR_CHMODE_LOCAL_LOOPBACK (0x2u << 14) /**< \brief (US_MR) Local Loopback. Transmitter output is connected to the Receiver Input. */
#define   US_MR_CHMODE_REMOTE_LOOPBACK (0x3u << 14) /**< \brief (US_MR) Remote Loopback. RXD pin is internally connected to the TXD pin. */
#define US_MR_MSBF (0x1u << 16) /**< \brief (US_MR) Bit Order */
#define US_MR_MODE9 (0x1u << 17) /**< \brief (US_MR) 9-bit Character Length */
#define US_MR_CLKO (0x1u << 18) /**< \brief (US_MR) Clock Output Select */
#define US_MR_OVER (0x1u << 19) /**< \brief (US_MR) Oversampling Mode */
#define US_MR_INACK (0x1u << 20) /**< \brief (US_MR) Inhibit Non Acknowledge */
#define US_MR_DSNACK (0x1u << 21) /**< \brief (US_MR) Disable Successive NACK */
#define US_MR_VAR_SYNC (0x1u << 22) /**< \brief (US_MR) Variable Synchronization of Command/Data Sync Start Frame Delimiter */
#define US_MR_INVDATA (0x1u << 23) /**< \brief (US_MR) Inverted Data */
#define US_MR_MAX_ITERATION_Pos 24
#define US_MR_MAX_ITERATION_Msk (0x7u << US_MR_MAX_ITERATION_Pos) /**< \brief (US_MR) Maximum Number of Automatic Iteration */
#define US_MR_MAX_ITERATION(value) ((US_MR_MAX_ITERATION_Msk & ((value) << US_MR_MAX_ITERATION_Pos)))
#define US_MR_FILTER (0x1u << 28) /**< \brief (US_MR) Receive Line Filter */
#define US_MR_MAN (0x1u << 29) /**< \brief (US_MR) Manchester Encoder/Decoder Enable */
#define US_MR_MODSYNC (0x1u << 30) /**< \brief (US_MR) Manchester Synchronization Mode */
#define US_MR_ONEBIT (0x1u << 31) /**< \brief (US_MR) Start Frame Delimiter Selector */
/* -------- US_IER : (FLEXCOM Offset: 0x208) USART Interrupt Enable Register -------- */
#define US_IER_RXRDY (0x1u << 0) /**< \brief (US_IER) RXRDY Interrupt Enable */
#define US_IER_TXRDY (0x1u << 1) /**< \brief (US_IER) TXRDY Interrupt Enable */
#define US_IER_RXBRK (0x1u << 2) /**< \brief (US_IER) Receiver Break Interrupt Enable */
#define US_IER_OVRE (0x1u << 5) /**< \brief (US_IER) Overrun Error Interrupt Enable */
#define US_IER_FRAME (0x1u << 6) /**< \brief (US_IER) Framing Error Interrupt Enable */
#define US_IER_PARE (0x1u << 7) /**< \brief (US_IER) Parity Error Interrupt Enable */
#define US_IER_TIMEOUT (0x1u << 8) /**< \brief (US_IER) Timeout Interrupt Enable */
#define US_IER_TXEMPTY (0x1u << 9) /**< \brief (US_IER) TXEMPTY Interrupt Enable */
#define US_IER_ITER (0x1u << 10) /**< \brief (US_IER) Max number of Repetitions Reached Interrupt Enable */
#define US_IER_NACK (0x1u << 13) /**< \brief (US_IER) Non Acknowledge Interrupt Enable */
#define US_IER_CTSIC (0x1u << 19) /**< \brief (US_IER) Clear to Send Input Change Interrupt Enable */
#define US_IER_CMP (0x1u << 22) /**< \brief (US_IER) Comparison Interrupt Enable */
#define US_IER_MANE (0x1u << 24) /**< \brief (US_IER) Manchester Error Interrupt Enable */
#define US_IER_LINBK (0x1u << 13) /**< \brief (US_IER) LIN Break Sent or LIN Break Received Interrupt Enable */
#define US_IER_LINID (0x1u << 14) /**< \brief (US_IER) LIN Identifier Sent or LIN Identifier Received Interrupt Enable */
#define US_IER_LINTC (0x1u << 15) /**< \brief (US_IER) LIN Transfer Completed Interrupt Enable */
#define US_IER_LINBE (0x1u << 25) /**< \brief (US_IER) LIN Bus Error Interrupt Enable */
#define US_IER_LINISFE (0x1u << 26) /**< \brief (US_IER) LIN Inconsistent Synch Field Error Interrupt Enable */
#define US_IER_LINIPE (0x1u << 27) /**< \brief (US_IER) LIN Identifier Parity Interrupt Enable */
#define US_IER_LINCE (0x1u << 28) /**< \brief (US_IER) LIN Checksum Error Interrupt Enable */
#define US_IER_LINSNRE (0x1u << 29) /**< \brief (US_IER) LIN Slave Not Responding Error Interrupt Enable */
#define US_IER_LINSTE (0x1u << 30) /**< \brief (US_IER) LIN Synch Tolerance Error Interrupt Enable */
#define US_IER_LINHTE (0x1u << 31) /**< \brief (US_IER) LIN Header Timeout Error Interrupt Enable */
/* -------- US_IDR : (FLEXCOM Offset: 0x20C) USART Interrupt Disable Register -------- */
#define US_IDR_RXRDY (0x1u << 0) /**< \brief (US_IDR) RXRDY Interrupt Disable */
#define US_IDR_TXRDY (0x1u << 1) /**< \brief (US_IDR) TXRDY Interrupt Disable */
#define US_IDR_RXBRK (0x1u << 2) /**< \brief (US_IDR) Receiver Break Interrupt Disable */
#define US_IDR_OVRE (0x1u << 5) /**< \brief (US_IDR) Overrun Error Interrupt Enable */
#define US_IDR_FRAME (0x1u << 6) /**< \brief (US_IDR) Framing Error Interrupt Disable */
#define US_IDR_PARE (0x1u << 7) /**< \brief (US_IDR) Parity Error Interrupt Disable */
#define US_IDR_TIMEOUT (0x1u << 8) /**< \brief (US_IDR) Timeout Interrupt Disable */
#define US_IDR_TXEMPTY (0x1u << 9) /**< \brief (US_IDR) TXEMPTY Interrupt Disable */
#define US_IDR_ITER (0x1u << 10) /**< \brief (US_IDR) Max Number of Repetitions Reached Interrupt Disable */
#define US_IDR_NACK (0x1u << 13) /**< \brief (US_IDR) Non Acknowledge Interrupt Disable */
#define US_IDR_CTSIC (0x1u << 19) /**< \brief (US_IDR) Clear to Send Input Change Interrupt Disable */
#define US_IDR_CMP (0x1u << 22) /**< \brief (US_IDR) Comparison Interrupt Disable */
#define US_IDR_MANE (0x1u << 24) /**< \brief (US_IDR) Manchester Error Interrupt Disable */
#define US_IDR_LINBK (0x1u << 13) /**< \brief (US_IDR) LIN Break Sent or LIN Break Received Interrupt Disable */
#define US_IDR_LINID (0x1u << 14) /**< \brief (US_IDR) LIN Identifier Sent or LIN Identifier Received Interrupt Disable */
#define US_IDR_LINTC (0x1u << 15) /**< \brief (US_IDR) LIN Transfer Completed Interrupt Disable */
#define US_IDR_LINBE (0x1u << 25) /**< \brief (US_IDR) LIN Bus Error Interrupt Disable */
#define US_IDR_LINISFE (0x1u << 26) /**< \brief (US_IDR) LIN Inconsistent Synch Field Error Interrupt Disable */
#define US_IDR_LINIPE (0x1u << 27) /**< \brief (US_IDR) LIN Identifier Parity Interrupt Disable */
#define US_IDR_LINCE (0x1u << 28) /**< \brief (US_IDR) LIN Checksum Error Interrupt Disable */
#define US_IDR_LINSNRE (0x1u << 29) /**< \brief (US_IDR) LIN Slave Not Responding Error Interrupt Disable */
#define US_IDR_LINSTE (0x1u << 30) /**< \brief (US_IDR) LIN Synch Tolerance Error Interrupt Disable */
#define US_IDR_LINHTE (0x1u << 31) /**< \brief (US_IDR) LIN Header Timeout Error Interrupt Disable */
/* -------- US_IMR : (FLEXCOM Offset: 0x210) USART Interrupt Mask Register -------- */
#define US_IMR_RXRDY (0x1u << 0) /**< \brief (US_IMR) RXRDY Interrupt Mask */
#define US_IMR_TXRDY (0x1u << 1) /**< \brief (US_IMR) TXRDY Interrupt Mask */
#define US_IMR_RXBRK (0x1u << 2) /**< \brief (US_IMR) Receiver Break Interrupt Mask */
#define US_IMR_OVRE (0x1u << 5) /**< \brief (US_IMR) Overrun Error Interrupt Mask */
#define US_IMR_FRAME (0x1u << 6) /**< \brief (US_IMR) Framing Error Interrupt Mask */
#define US_IMR_PARE (0x1u << 7) /**< \brief (US_IMR) Parity Error Interrupt Mask */
#define US_IMR_TIMEOUT (0x1u << 8) /**< \brief (US_IMR) Timeout Interrupt Mask */
#define US_IMR_TXEMPTY (0x1u << 9) /**< \brief (US_IMR) TXEMPTY Interrupt Mask */
#define US_IMR_ITER (0x1u << 10) /**< \brief (US_IMR) Max Number of Repetitions Reached Interrupt Mask */
#define US_IMR_NACK (0x1u << 13) /**< \brief (US_IMR) Non Acknowledge Interrupt Mask */
#define US_IMR_CTSIC (0x1u << 19) /**< \brief (US_IMR) Clear to Send Input Change Interrupt Mask */
#define US_IMR_CMP (0x1u << 22) /**< \brief (US_IMR) Comparison Interrupt Mask */
#define US_IMR_MANE (0x1u << 24) /**< \brief (US_IMR) Manchester Error Interrupt Mask */
#define US_IMR_LINBK (0x1u << 13) /**< \brief (US_IMR) LIN Break Sent or LIN Break Received Interrupt Mask */
#define US_IMR_LINID (0x1u << 14) /**< \brief (US_IMR) LIN Identifier Sent or LIN Identifier Received Interrupt Mask */
#define US_IMR_LINTC (0x1u << 15) /**< \brief (US_IMR) LIN Transfer Completed Interrupt Mask */
#define US_IMR_LINBE (0x1u << 25) /**< \brief (US_IMR) LIN Bus Error Interrupt Mask */
#define US_IMR_LINISFE (0x1u << 26) /**< \brief (US_IMR) LIN Inconsistent Synch Field Error Interrupt Mask */
#define US_IMR_LINIPE (0x1u << 27) /**< \brief (US_IMR) LIN Identifier Parity Interrupt Mask */
#define US_IMR_LINCE (0x1u << 28) /**< \brief (US_IMR) LIN Checksum Error Interrupt Mask */
#define US_IMR_LINSNRE (0x1u << 29) /**< \brief (US_IMR) LIN Slave Not Responding Error Interrupt Mask */
#define US_IMR_LINSTE (0x1u << 30) /**< \brief (US_IMR) LIN Synch Tolerance Error Interrupt Mask */
#define US_IMR_LINHTE (0x1u << 31) /**< \brief (US_IMR) LIN Header Timeout Error Interrupt Mask */
/* -------- US_CSR : (FLEXCOM Offset: 0x214) USART Channel Status Register -------- */
#define US_CSR_RXRDY (0x1u << 0) /**< \brief (US_CSR) Receiver Ready (cleared by reading US_RHR) */
#define US_CSR_TXRDY (0x1u << 1) /**< \brief (US_CSR) Transmitter Ready (cleared by writing US_THR) */
#define US_CSR_RXBRK (0x1u << 2) /**< \brief (US_CSR) Break Received/End of Break */
#define US_CSR_OVRE (0x1u << 5) /**< \brief (US_CSR) Overrun Error */
#define US_CSR_FRAME (0x1u << 6) /**< \brief (US_CSR) Framing Error */
#define US_CSR_PARE (0x1u << 7) /**< \brief (US_CSR) Parity Error */
#define US_CSR_TIMEOUT (0x1u << 8) /**< \brief (US_CSR) Receiver Timeout */
#define US_CSR_TXEMPTY (0x1u << 9) /**< \brief (US_CSR) Transmitter Empty (cleared by writing US_THR) */
#define US_CSR_ITER (0x1u << 10) /**< \brief (US_CSR) Max Number of Repetitions Reached */
#define US_CSR_NACK (0x1u << 13) /**< \brief (US_CSR) Non Acknowledge Interrupt */
#define US_CSR_CTSIC (0x1u << 19) /**< \brief (US_CSR) Clear to Send Input Change Flag */
#define US_CSR_CMP (0x1u << 22) /**< \brief (US_CSR) Comparison Status */
#define US_CSR_CTS (0x1u << 23) /**< \brief (US_CSR) Image of CTS Input */
#define US_CSR_MANE (0x1u << 24) /**< \brief (US_CSR) Manchester Error */
#define US_CSR_LINBK (0x1u << 13) /**< \brief (US_CSR) LIN Break Sent or LIN Break Received */
#define US_CSR_LINID (0x1u << 14) /**< \brief (US_CSR) LIN Identifier Sent or LIN Identifier Received */
#define US_CSR_LINTC (0x1u << 15) /**< \brief (US_CSR) LIN Transfer Completed */
#define US_CSR_LINBLS (0x1u << 23) /**< \brief (US_CSR) LIN Bus Line Status */
#define US_CSR_LINBE (0x1u << 25) /**< \brief (US_CSR) LIN Bit Error */
#define US_CSR_LINISFE (0x1u << 26) /**< \brief (US_CSR) LIN Inconsistent Synch Field Error */
#define US_CSR_LINIPE (0x1u << 27) /**< \brief (US_CSR) LIN Identifier Parity Error */
#define US_CSR_LINCE (0x1u << 28) /**< \brief (US_CSR) LIN Checksum Error */
#define US_CSR_LINSNRE (0x1u << 29) /**< \brief (US_CSR) LIN Slave Not Responding Error */
#define US_CSR_LINSTE (0x1u << 30) /**< \brief (US_CSR) LIN Synch Tolerance Error */
#define US_CSR_LINHTE (0x1u << 31) /**< \brief (US_CSR) LIN Header Timeout Error */
/* -------- US_RHR : (FLEXCOM Offset: 0x218) USART Receive Holding Register -------- */
#define US_RHR_RXCHR_Pos 0
#define US_RHR_RXCHR_Msk (0x1ffu << US_RHR_RXCHR_Pos) /**< \brief (US_RHR) Received Character */
#define US_RHR_RXSYNH (0x1u << 15) /**< \brief (US_RHR) Received Sync */
#define US_RHR_RXCHR0_Pos 0
#define US_RHR_RXCHR0_Msk (0xffu << US_RHR_RXCHR0_Pos) /**< \brief (US_RHR) Received Character */
#define US_RHR_RXCHR1_Pos 8
#define US_RHR_RXCHR1_Msk (0xffu << US_RHR_RXCHR1_Pos) /**< \brief (US_RHR) Received Character */
#define US_RHR_RXCHR2_Pos 16
#define US_RHR_RXCHR2_Msk (0xffu << US_RHR_RXCHR2_Pos) /**< \brief (US_RHR) Received Character */
#define US_RHR_RXCHR3_Pos 24
#define US_RHR_RXCHR3_Msk (0xffu << US_RHR_RXCHR3_Pos) /**< \brief (US_RHR) Received Character */
/* -------- US_THR : (FLEXCOM Offset: 0x21C) USART Transmit Holding Register -------- */
#define US_THR_TXCHR_Pos 0
#define US_THR_TXCHR_Msk (0x1ffu << US_THR_TXCHR_Pos) /**< \brief (US_THR) Character to be Transmitted */
#define US_THR_TXCHR(value) ((US_THR_TXCHR_Msk & ((value) << US_THR_TXCHR_Pos)))
#define US_THR_TXSYNH (0x1u << 15) /**< \brief (US_THR) Sync Field to be Transmitted */
#define US_THR_TXCHR0_Pos 0
#define US_THR_TXCHR0_Msk (0xffu << US_THR_TXCHR0_Pos) /**< \brief (US_THR) Character to be Transmitted */
#define US_THR_TXCHR0(value) ((US_THR_TXCHR0_Msk & ((value) << US_THR_TXCHR0_Pos)))
#define US_THR_TXCHR1_Pos 8
#define US_THR_TXCHR1_Msk (0xffu << US_THR_TXCHR1_Pos) /**< \brief (US_THR) Character to be Transmitted */
#define US_THR_TXCHR1(value) ((US_THR_TXCHR1_Msk & ((value) << US_THR_TXCHR1_Pos)))
#define US_THR_TXCHR2_Pos 16
#define US_THR_TXCHR2_Msk (0xffu << US_THR_TXCHR2_Pos) /**< \brief (US_THR) Character to be Transmitted */
#define US_THR_TXCHR2(value) ((US_THR_TXCHR2_Msk & ((value) << US_THR_TXCHR2_Pos)))
#define US_THR_TXCHR3_Pos 24
#define US_THR_TXCHR3_Msk (0xffu << US_THR_TXCHR3_Pos) /**< \brief (US_THR) Character to be Transmitted */
#define US_THR_TXCHR3(value) ((US_THR_TXCHR3_Msk & ((value) << US_THR_TXCHR3_Pos)))
/* -------- US_BRGR : (FLEXCOM Offset: 0x220) USART Baud Rate Generator Register -------- */
#define US_BRGR_CD_Pos 0
#define US_BRGR_CD_Msk (0xffffu << US_BRGR_CD_Pos) /**< \brief (US_BRGR) Clock Divider */
#define US_BRGR_CD(value) ((US_BRGR_CD_Msk & ((value) << US_BRGR_CD_Pos)))
#define US_BRGR_FP_Pos 16
#define US_BRGR_FP_Msk (0x7u << US_BRGR_FP_Pos) /**< \brief (US_BRGR) Fractional Part */
#define US_BRGR_FP(value) ((US_BRGR_FP_Msk & ((value) << US_BRGR_FP_Pos)))
/* -------- US_RTOR : (FLEXCOM Offset: 0x224) USART Receiver Timeout Register -------- */
#define US_RTOR_TO_Pos 0
#define US_RTOR_TO_Msk (0x1ffffu << US_RTOR_TO_Pos) /**< \brief (US_RTOR) Timeout Value */
#define US_RTOR_TO(value) ((US_RTOR_TO_Msk & ((value) << US_RTOR_TO_Pos)))
/* -------- US_TTGR : (FLEXCOM Offset: 0x228) USART Transmitter Timeguard Register -------- */
#define US_TTGR_TG_Pos 0
#define US_TTGR_TG_Msk (0xffu << US_TTGR_TG_Pos) /**< \brief (US_TTGR) Timeguard Value */
#define US_TTGR_TG(value) ((US_TTGR_TG_Msk & ((value) << US_TTGR_TG_Pos)))
/* -------- US_FIDI : (FLEXCOM Offset: 0x240) USART FI DI Ratio Register -------- */
#define US_FIDI_FI_DI_RATIO_Pos 0
#define US_FIDI_FI_DI_RATIO_Msk (0xffffu << US_FIDI_FI_DI_RATIO_Pos) /**< \brief (US_FIDI) FI Over DI Ratio Value */
#define US_FIDI_FI_DI_RATIO(value) ((US_FIDI_FI_DI_RATIO_Msk & ((value) << US_FIDI_FI_DI_RATIO_Pos)))
/* -------- US_NER : (FLEXCOM Offset: 0x244) USART Number of Errors Register -------- */
#define US_NER_NB_ERRORS_Pos 0
#define US_NER_NB_ERRORS_Msk (0xffu << US_NER_NB_ERRORS_Pos) /**< \brief (US_NER) Number of Errors */
/* -------- US_IF : (FLEXCOM Offset: 0x24C) USART IrDA Filter Register -------- */
#define US_IF_IRDA_FILTER_Pos 0
#define US_IF_IRDA_FILTER_Msk (0xffu << US_IF_IRDA_FILTER_Pos) /**< \brief (US_IF) IrDA Filter */
#define US_IF_IRDA_FILTER(value) ((US_IF_IRDA_FILTER_Msk & ((value) << US_IF_IRDA_FILTER_Pos)))
/* -------- US_MAN : (FLEXCOM Offset: 0x250) USART Manchester Configuration Register -------- */
#define US_MAN_TX_PL_Pos 0
#define US_MAN_TX_PL_Msk (0xfu << US_MAN_TX_PL_Pos) /**< \brief (US_MAN) Transmitter Preamble Length */
#define US_MAN_TX_PL(value) ((US_MAN_TX_PL_Msk & ((value) << US_MAN_TX_PL_Pos)))
#define US_MAN_TX_PP_Pos 8
#define US_MAN_TX_PP_Msk (0x3u << US_MAN_TX_PP_Pos) /**< \brief (US_MAN) Transmitter Preamble Pattern */
#define US_MAN_TX_PP(value) ((US_MAN_TX_PP_Msk & ((value) << US_MAN_TX_PP_Pos)))
#define   US_MAN_TX_PP_ALL_ONE (0x0u << 8) /**< \brief (US_MAN) The preamble is composed of '1's */
#define   US_MAN_TX_PP_ALL_ZERO (0x1u << 8) /**< \brief (US_MAN) The preamble is composed of '0's */
#define   US_MAN_TX_PP_ZERO_ONE (0x2u << 8) /**< \brief (US_MAN) The preamble is composed of '01's */
#define   US_MAN_TX_PP_ONE_ZERO (0x3u << 8) /**< \brief (US_MAN) The preamble is composed of '10's */
#define US_MAN_TX_MPOL (0x1u << 12) /**< \brief (US_MAN) Transmitter Manchester Polarity */
#define US_MAN_RX_PL_Pos 16
#define US_MAN_RX_PL_Msk (0xfu << US_MAN_RX_PL_Pos) /**< \brief (US_MAN) Receiver Preamble Length */
#define US_MAN_RX_PL(value) ((US_MAN_RX_PL_Msk & ((value) << US_MAN_RX_PL_Pos)))
#define US_MAN_RX_PP_Pos 24
#define US_MAN_RX_PP_Msk (0x3u << US_MAN_RX_PP_Pos) /**< \brief (US_MAN) Receiver Preamble Pattern detected */
#define US_MAN_RX_PP(value) ((US_MAN_RX_PP_Msk & ((value) << US_MAN_RX_PP_Pos)))
#define   US_MAN_RX_PP_ALL_ONE (0x0u << 24) /**< \brief (US_MAN) The preamble is composed of '1's */
#define   US_MAN_RX_PP_ALL_ZERO (0x1u << 24) /**< \brief (US_MAN) The preamble is composed of '0's */
#define   US_MAN_RX_PP_ZERO_ONE (0x2u << 24) /**< \brief (US_MAN) The preamble is composed of '01's */
#define   US_MAN_RX_PP_ONE_ZERO (0x3u << 24) /**< \brief (US_MAN) The preamble is composed of '10's */
#define US_MAN_RX_MPOL (0x1u << 28) /**< \brief (US_MAN) Receiver Manchester Polarity */
#define US_MAN_ONE (0x1u << 29) /**< \brief (US_MAN) Must Be Set to 1 */
#define US_MAN_DRIFT (0x1u << 30) /**< \brief (US_MAN) Drift Compensation */
#define US_MAN_RXIDLEV (0x1u << 31) /**< \brief (US_MAN) Receiver Idle Value */
/* -------- US_LINMR : (FLEXCOM Offset: 0x254) USART LIN Mode Register -------- */
#define US_LINMR_NACT_Pos 0
#define US_LINMR_NACT_Msk (0x3u << US_LINMR_NACT_Pos) /**< \brief (US_LINMR) LIN Node Action */
#define US_LINMR_NACT(value) ((US_LINMR_NACT_Msk & ((value) << US_LINMR_NACT_Pos)))
#define   US_LINMR_NACT_PUBLISH (0x0u << 0) /**< \brief (US_LINMR) The USART transmits the response. */
#define   US_LINMR_NACT_SUBSCRIBE (0x1u << 0) /**< \brief (US_LINMR) The USART receives the response. */
#define   US_LINMR_NACT_IGNORE (0x2u << 0) /**< \brief (US_LINMR) The USART does not transmit and does not receive the response. */
#define US_LINMR_PARDIS (0x1u << 2) /**< \brief (US_LINMR) Parity Disable */
#define US_LINMR_CHKDIS (0x1u << 3) /**< \brief (US_LINMR) Checksum Disable */
#define US_LINMR_CHKTYP (0x1u << 4) /**< \brief (US_LINMR) Checksum Type */
#define US_LINMR_DLM (0x1u << 5) /**< \brief (US_LINMR) Data Length Mode */
#define US_LINMR_FSDIS (0x1u << 6) /**< \brief (US_LINMR) Frame Slot Mode Disable */
#define US_LINMR_WKUPTYP (0x1u << 7) /**< \brief (US_LINMR) Wake-up Signal Type */
#define US_LINMR_DLC_Pos 8
#define US_LINMR_DLC_Msk (0xffu << US_LINMR_DLC_Pos) /**< \brief (US_LINMR) Data Length Control */
#define US_LINMR_DLC(value) ((US_LINMR_DLC_Msk & ((value) << US_LINMR_DLC_Pos)))
#define US_LINMR_PDCM (0x1u << 16) /**< \brief (US_LINMR) DMAC Mode */
#define US_LINMR_SYNCDIS (0x1u << 17) /**< \brief (US_LINMR) Synchronization Disable */
/* -------- US_LINIR : (FLEXCOM Offset: 0x258) USART LIN Identifier Register -------- */
#define US_LINIR_IDCHR_Pos 0
#define US_LINIR_IDCHR_Msk (0xffu << US_LINIR_IDCHR_Pos) /**< \brief (US_LINIR) Identifier Character */
#define US_LINIR_IDCHR(value) ((US_LINIR_IDCHR_Msk & ((value) << US_LINIR_IDCHR_Pos)))
/* -------- US_LINBRR : (FLEXCOM Offset: 0x25C) USART LIN Baud Rate Register -------- */
#define US_LINBRR_LINCD_Pos 0
#define US_LINBRR_LINCD_Msk (0xffffu << US_LINBRR_LINCD_Pos) /**< \brief (US_LINBRR) Clock Divider after Synchronization */
#define US_LINBRR_LINFP_Pos 16
#define US_LINBRR_LINFP_Msk (0x7u << US_LINBRR_LINFP_Pos) /**< \brief (US_LINBRR) Fractional Part after Synchronization */
/* -------- US_CMPR : (FLEXCOM Offset: 0x290) USART Comparison Register -------- */
#define US_CMPR_VAL1_Pos 0
#define US_CMPR_VAL1_Msk (0x1ffu << US_CMPR_VAL1_Pos) /**< \brief (US_CMPR) First Comparison Value for Received Character */
#define US_CMPR_VAL1(value) ((US_CMPR_VAL1_Msk & ((value) << US_CMPR_VAL1_Pos)))
#define US_CMPR_CMPMODE (0x1u << 12) /**< \brief (US_CMPR) Comparison Mode */
#define   US_CMPR_CMPMODE_FLAG_ONLY (0x0u << 12) /**< \brief (US_CMPR) Any character is received and comparison function drives CMP flag. */
#define   US_CMPR_CMPMODE_START_CONDITION (0x1u << 12) /**< \brief (US_CMPR) Comparison condition must be met to start reception. */
#define US_CMPR_CMPPAR (0x1u << 14) /**< \brief (US_CMPR) Compare Parity */
#define US_CMPR_VAL2_Pos 16
#define US_CMPR_VAL2_Msk (0x1ffu << US_CMPR_VAL2_Pos) /**< \brief (US_CMPR) Second Comparison Value for Received Character */
#define US_CMPR_VAL2(value) ((US_CMPR_VAL2_Msk & ((value) << US_CMPR_VAL2_Pos)))
/* -------- US_FMR : (FLEXCOM Offset: 0x2A0) USART FIFO Mode Register -------- */
#define US_FMR_TXRDYM_Pos 0
#define US_FMR_TXRDYM_Msk (0x3u << US_FMR_TXRDYM_Pos) /**< \brief (US_FMR) Transmitter Ready Mode */
#define US_FMR_TXRDYM(value) ((US_FMR_TXRDYM_Msk & ((value) << US_FMR_TXRDYM_Pos)))
#define   US_FMR_TXRDYM_ONE_DATA (0x0u << 0) /**< \brief (US_FMR) TXRDY will be at level '1' when at least one data can be written in the Transmit FIFO */
#define   US_FMR_TXRDYM_TWO_DATA (0x1u << 0) /**< \brief (US_FMR) TXRDY will be at level '1' when at least two data can be written in the Transmit FIFO */
#define   US_FMR_TXRDYM_FOUR_DATA (0x2u << 0) /**< \brief (US_FMR) TXRDY will be at level '1' when at least four data can be written in the Transmit FIFO */
#define US_FMR_RXRDYM_Pos 4
#define US_FMR_RXRDYM_Msk (0x3u << US_FMR_RXRDYM_Pos) /**< \brief (US_FMR) Receiver Ready Mode */
#define US_FMR_RXRDYM(value) ((US_FMR_RXRDYM_Msk & ((value) << US_FMR_RXRDYM_Pos)))
#define   US_FMR_RXRDYM_ONE_DATA (0x0u << 4) /**< \brief (US_FMR) RXRDY will be at level '1' when at least one unread data is in the Receive FIFO */
#define   US_FMR_RXRDYM_TWO_DATA (0x1u << 4) /**< \brief (US_FMR) RXRDY will be at level '1' when at least two unread data are in the Receive FIFO */
#define   US_FMR_RXRDYM_FOUR_DATA (0x2u << 4) /**< \brief (US_FMR) RXRDY will be at level '1' when at least four unread data are in the Receive FIFO */
#define US_FMR_FRTSC (0x1u << 7) /**< \brief (US_FMR) FIFO RTS pin Control enable (Hardware Handshaking mode only) */
#define US_FMR_TXFTHRES_Pos 8
#define US_FMR_TXFTHRES_Msk (0x3fu << US_FMR_TXFTHRES_Pos) /**< \brief (US_FMR) Transmit FIFO Threshold */
#define US_FMR_TXFTHRES(value) ((US_FMR_TXFTHRES_Msk & ((value) << US_FMR_TXFTHRES_Pos)))
#define US_FMR_RXFTHRES_Pos 16
#define US_FMR_RXFTHRES_Msk (0x3fu << US_FMR_RXFTHRES_Pos) /**< \brief (US_FMR) Receive FIFO Threshold */
#define US_FMR_RXFTHRES(value) ((US_FMR_RXFTHRES_Msk & ((value) << US_FMR_RXFTHRES_Pos)))
#define US_FMR_RXFTHRES2_Pos 24
#define US_FMR_RXFTHRES2_Msk (0x3fu << US_FMR_RXFTHRES2_Pos) /**< \brief (US_FMR) Receive FIFO Threshold 2 */
#define US_FMR_RXFTHRES2(value) ((US_FMR_RXFTHRES2_Msk & ((value) << US_FMR_RXFTHRES2_Pos)))
/* -------- US_FLR : (FLEXCOM Offset: 0x2A4) USART FIFO Level Register -------- */
#define US_FLR_TXFL_Pos 0
#define US_FLR_TXFL_Msk (0x3fu << US_FLR_TXFL_Pos) /**< \brief (US_FLR) Transmit FIFO Level */
#define US_FLR_RXFL_Pos 16
#define US_FLR_RXFL_Msk (0x3fu << US_FLR_RXFL_Pos) /**< \brief (US_FLR) Receive FIFO Level */
/* -------- US_FIER : (FLEXCOM Offset: 0x2A8) USART FIFO Interrupt Enable Register -------- */
#define US_FIER_TXFEF (0x1u << 0) /**< \brief (US_FIER) TXFEF Interrupt Enable */
#define US_FIER_TXFFF (0x1u << 1) /**< \brief (US_FIER) TXFFF Interrupt Enable */
#define US_FIER_TXFTHF (0x1u << 2) /**< \brief (US_FIER) TXFTHF Interrupt Enable */
#define US_FIER_RXFEF (0x1u << 3) /**< \brief (US_FIER) RXFEF Interrupt Enable */
#define US_FIER_RXFFF (0x1u << 4) /**< \brief (US_FIER) RXFFF Interrupt Enable */
#define US_FIER_RXFTHF (0x1u << 5) /**< \brief (US_FIER) RXFTHF Interrupt Enable */
#define US_FIER_TXFPTEF (0x1u << 6) /**< \brief (US_FIER) TXFPTEF Interrupt Enable */
#define US_FIER_RXFPTEF (0x1u << 7) /**< \brief (US_FIER) RXFPTEF Interrupt Enable */
#define US_FIER_RXFTHF2 (0x1u << 9) /**< \brief (US_FIER) RXFTHF2 Interrupt Enable */
/* -------- US_FIDR : (FLEXCOM Offset: 0x2AC) USART FIFO Interrupt Disable Register -------- */
#define US_FIDR_TXFEF (0x1u << 0) /**< \brief (US_FIDR) TXFEF Interrupt Disable */
#define US_FIDR_TXFFF (0x1u << 1) /**< \brief (US_FIDR) TXFFF Interrupt Disable */
#define US_FIDR_TXFTHF (0x1u << 2) /**< \brief (US_FIDR) TXFTHF Interrupt Disable */
#define US_FIDR_RXFEF (0x1u << 3) /**< \brief (US_FIDR) RXFEF Interrupt Disable */
#define US_FIDR_RXFFF (0x1u << 4) /**< \brief (US_FIDR) RXFFF Interrupt Disable */
#define US_FIDR_RXFTHF (0x1u << 5) /**< \brief (US_FIDR) RXFTHF Interrupt Disable */
#define US_FIDR_TXFPTEF (0x1u << 6) /**< \brief (US_FIDR) TXFPTEF Interrupt Disable */
#define US_FIDR_RXFPTEF (0x1u << 7) /**< \brief (US_FIDR) RXFPTEF Interrupt Disable */
#define US_FIDR_RXFTHF2 (0x1u << 9) /**< \brief (US_FIDR) RXFTHF2 Interrupt Disable */
/* -------- US_FIMR : (FLEXCOM Offset: 0x2B0) USART FIFO Interrupt Mask Register -------- */
#define US_FIMR_TXFEF (0x1u << 0) /**< \brief (US_FIMR) TXFEF Interrupt Mask */
#define US_FIMR_TXFFF (0x1u << 1) /**< \brief (US_FIMR) TXFFF Interrupt Mask */
#define US_FIMR_TXFTHF (0x1u << 2) /**< \brief (US_FIMR) TXFTHF Interrupt Mask */
#define US_FIMR_RXFEF (0x1u << 3) /**< \brief (US_FIMR) RXFEF Interrupt Mask */
#define US_FIMR_RXFFF (0x1u << 4) /**< \brief (US_FIMR) RXFFF Interrupt Mask */
#define US_FIMR_RXFTHF (0x1u << 5) /**< \brief (US_FIMR) RXFTHF Interrupt Mask */
#define US_FIMR_TXFPTEF (0x1u << 6) /**< \brief (US_FIMR) TXFPTEF Interrupt Mask */
#define US_FIMR_RXFPTEF (0x1u << 7) /**< \brief (US_FIMR) RXFPTEF Interrupt Mask */
#define US_FIMR_RXFTHF2 (0x1u << 9) /**< \brief (US_FIMR) RXFTHF2 Interrupt Mask */
/* -------- US_FESR : (FLEXCOM Offset: 0x2B4) USART FIFO Event Status Register -------- */
#define US_FESR_TXFEF (0x1u << 0) /**< \brief (US_FESR) Transmit FIFO Empty Flag (cleared by writing RSTSTA bit in US_CR) */
#define US_FESR_TXFFF (0x1u << 1) /**< \brief (US_FESR) Transmit FIFO Full Flag (cleared by writing RSTSTA bit in US_CR) */
#define US_FESR_TXFTHF (0x1u << 2) /**< \brief (US_FESR) Transmit FIFO Threshold Flag (cleared by writing RSTSTA bit in US_CR) */
#define US_FESR_RXFEF (0x1u << 3) /**< \brief (US_FESR) Receive FIFO Empty Flag (cleared by writing RSTSTA bit in US_CR) */
#define US_FESR_RXFFF (0x1u << 4) /**< \brief (US_FESR) Receive FIFO Full Flag (cleared by writing RSTSTA bit in US_CR) */
#define US_FESR_RXFTHF (0x1u << 5) /**< \brief (US_FESR) Receive FIFO Threshold Flag (cleared by writing RSTSTA bit in US_CR) */
#define US_FESR_TXFPTEF (0x1u << 6) /**< \brief (US_FESR) Transmit FIFO Pointer Error Flag */
#define US_FESR_RXFPTEF (0x1u << 7) /**< \brief (US_FESR) Receive FIFO Pointer Error Flag */
#define US_FESR_TXFLOCK (0x1u << 8) /**< \brief (US_FESR) Transmit FIFO Lock */
#define US_FESR_RXFTHF2 (0x1u << 9) /**< \brief (US_FESR) Receive FIFO Threshold Flag 2 (cleared by writing RSTSTA bit in US_CR) */
/* -------- US_WPMR : (FLEXCOM Offset: 0x2E4) USART Write Protection Mode Register -------- */
#define US_WPMR_WPEN (0x1u << 0) /**< \brief (US_WPMR) Write Protection Enable */
#define US_WPMR_WPKEY_Pos 8
#define US_WPMR_WPKEY_Msk (0xffffffu << US_WPMR_WPKEY_Pos) /**< \brief (US_WPMR) Write Protection Key */
#define US_WPMR_WPKEY(value) ((US_WPMR_WPKEY_Msk & ((value) << US_WPMR_WPKEY_Pos)))
#define   US_WPMR_WPKEY_PASSWD (0x555341u << 8) /**< \brief (US_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit. Always reads as 0. */
/* -------- US_WPSR : (FLEXCOM Offset: 0x2E8) USART Write Protection Status Register -------- */
#define US_WPSR_WPVS (0x1u << 0) /**< \brief (US_WPSR) Write Protection Violation Status */
#define US_WPSR_WPVSRC_Pos 8
#define US_WPSR_WPVSRC_Msk (0xffffu << US_WPSR_WPVSRC_Pos) /**< \brief (US_WPSR) Write Protection Violation Source */
/* -------- US_VERSION : (FLEXCOM Offset: 0x2FC) USART Version Register -------- */
#define US_VERSION_VERSION_Pos 0
#define US_VERSION_VERSION_Msk (0xfffu << US_VERSION_VERSION_Pos) /**< \brief (US_VERSION) Hardware Module Version */
#define US_VERSION_MFN_Pos 16
#define US_VERSION_MFN_Msk (0x7u << US_VERSION_MFN_Pos) /**< \brief (US_VERSION) Metal Fix Number */
/* -------- SPI_CR : (FLEXCOM Offset: 0x400) SPI Control Register -------- */
#define SPI_CR_SPIEN (0x1u << 0) /**< \brief (SPI_CR) SPI Enable */
#define SPI_CR_SPIDIS (0x1u << 1) /**< \brief (SPI_CR) SPI Disable */
#define SPI_CR_SWRST (0x1u << 7) /**< \brief (SPI_CR) SPI Software Reset */
#define SPI_CR_REQCLR (0x1u << 12) /**< \brief (SPI_CR) Request to Clear the Comparison Trigger */
#define SPI_CR_TXFCLR (0x1u << 16) /**< \brief (SPI_CR) Transmit FIFO Clear */
#define SPI_CR_RXFCLR (0x1u << 17) /**< \brief (SPI_CR) Receive FIFO Clear */
#define SPI_CR_LASTXFER (0x1u << 24) /**< \brief (SPI_CR) Last Transfer */
#define SPI_CR_FIFOEN (0x1u << 30) /**< \brief (SPI_CR) FIFO Enable */
#define SPI_CR_FIFODIS (0x1u << 31) /**< \brief (SPI_CR) FIFO Disable */
/* -------- SPI_MR : (FLEXCOM Offset: 0x404) SPI Mode Register -------- */
#define SPI_MR_MSTR (0x1u << 0) /**< \brief (SPI_MR) Master/Slave Mode */
#define SPI_MR_PS (0x1u << 1) /**< \brief (SPI_MR) Peripheral Select */
#define SPI_MR_PCSDEC (0x1u << 2) /**< \brief (SPI_MR) Chip Select Decode */
#define SPI_MR_BRSRCCLK (0x1u << 3) /**< \brief (SPI_MR) Bit Rate Source Clock */
#define   SPI_MR_BRSRCCLK_PERIPH_CLK (0x0u << 3) /**< \brief (SPI_MR) The peripheral clock is the source clock for the bit rate generation. */
#define   SPI_MR_BRSRCCLK_PMC_PCK (0x1u << 3) /**< \brief (SPI_MR) PMC PCKx is the source clock for the bit rate generation, thus the bit rate can be independent of the core/peripheral clock. */
#define SPI_MR_MODFDIS (0x1u << 4) /**< \brief (SPI_MR) Mode Fault Detection */
#define SPI_MR_WDRBT (0x1u << 5) /**< \brief (SPI_MR) Wait Data Read Before Transfer */
#define SPI_MR_LLB (0x1u << 7) /**< \brief (SPI_MR) Local Loopback Enable */
#define SPI_MR_CMPMODE (0x1u << 12) /**< \brief (SPI_MR) Comparison Mode */
#define   SPI_MR_CMPMODE_FLAG_ONLY (0x0u << 12) /**< \brief (SPI_MR) Any character is received and comparison function drives CMP flag. */
#define   SPI_MR_CMPMODE_START_CONDITION (0x1u << 12) /**< \brief (SPI_MR) Comparison condition must be met to start reception of all incoming characters until REQCLR is set. */
#define SPI_MR_PCS_Pos 16
#define SPI_MR_PCS_Msk (0xFu << SPI_MR_PCS_Pos) /**< \brief (SPI_MR) Peripheral Chip Select */
#define SPI_MR_PCS(value) ((SPI_MR_PCS_Msk & ((value) << SPI_MR_PCS_Pos)))
#define SPI_MR_DLYBCS_Pos 24
#define SPI_MR_DLYBCS_Msk (0xffu << SPI_MR_DLYBCS_Pos) /**< \brief (SPI_MR) Delay Between Chip Selects */
#define SPI_MR_DLYBCS(value) ((SPI_MR_DLYBCS_Msk & ((value) << SPI_MR_DLYBCS_Pos)))
/* -------- SPI_RDR : (FLEXCOM Offset: 0x408) SPI Receive Data Register -------- */
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
/* -------- SPI_TDR : (FLEXCOM Offset: 0x40C) SPI Transmit Data Register -------- */
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
/* -------- SPI_SR : (FLEXCOM Offset: 0x410) SPI Status Register -------- */
#define SPI_SR_RDRF (0x1u << 0) /**< \brief (SPI_SR) Receive Data Register Full (cleared by reading SPI_RDR) */
#define SPI_SR_TDRE (0x1u << 1) /**< \brief (SPI_SR) Transmit Data Register Empty (cleared by writing SPI_TDR) */
#define SPI_SR_MODF (0x1u << 2) /**< \brief (SPI_SR) Mode Fault Error (cleared on read) */
#define SPI_SR_OVRES (0x1u << 3) /**< \brief (SPI_SR) Overrun Error Status (cleared on read) */
#define SPI_SR_NSSR (0x1u << 8) /**< \brief (SPI_SR) NSS Rising (cleared on read) */
#define SPI_SR_TXEMPTY (0x1u << 9) /**< \brief (SPI_SR) Transmission Registers Empty (cleared by writing SPI_TDR) */
#define SPI_SR_UNDES (0x1u << 10) /**< \brief (SPI_SR) Underrun Error Status (Slave mode Only) (cleared on read) */
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
/* -------- SPI_IER : (FLEXCOM Offset: 0x414) SPI Interrupt Enable Register -------- */
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
/* -------- SPI_IDR : (FLEXCOM Offset: 0x418) SPI Interrupt Disable Register -------- */
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
/* -------- SPI_IMR : (FLEXCOM Offset: 0x41C) SPI Interrupt Mask Register -------- */
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
/* -------- SPI_CSR[2] : (FLEXCOM Offset: 0x430) SPI Chip Select Register -------- */
#define SPI_CSR_CPOL (0x1u << 0) /**< \brief (SPI_CSR[2]) Clock Polarity */
#define SPI_CSR_NCPHA (0x1u << 1) /**< \brief (SPI_CSR[2]) Clock Phase */
#define SPI_CSR_CSNAAT (0x1u << 2) /**< \brief (SPI_CSR[2]) Chip Select Not Active After Transfer (Ignored if CSAAT = 1) */
#define SPI_CSR_CSAAT (0x1u << 3) /**< \brief (SPI_CSR[2]) Chip Select Active After Transfer */
#define SPI_CSR_BITS_Pos 4
#define SPI_CSR_BITS_Msk (0xfu << SPI_CSR_BITS_Pos) /**< \brief (SPI_CSR[2]) Bits Per Transfer */
#define SPI_CSR_BITS(value) ((SPI_CSR_BITS_Msk & ((value) << SPI_CSR_BITS_Pos)))
#define   SPI_CSR_BITS_8_BIT (0x0u << 4) /**< \brief (SPI_CSR[2]) 8 bits for transfer */
#define   SPI_CSR_BITS_9_BIT (0x1u << 4) /**< \brief (SPI_CSR[2]) 9 bits for transfer */
#define   SPI_CSR_BITS_10_BIT (0x2u << 4) /**< \brief (SPI_CSR[2]) 10 bits for transfer */
#define   SPI_CSR_BITS_11_BIT (0x3u << 4) /**< \brief (SPI_CSR[2]) 11 bits for transfer */
#define   SPI_CSR_BITS_12_BIT (0x4u << 4) /**< \brief (SPI_CSR[2]) 12 bits for transfer */
#define   SPI_CSR_BITS_13_BIT (0x5u << 4) /**< \brief (SPI_CSR[2]) 13 bits for transfer */
#define   SPI_CSR_BITS_14_BIT (0x6u << 4) /**< \brief (SPI_CSR[2]) 14 bits for transfer */
#define   SPI_CSR_BITS_15_BIT (0x7u << 4) /**< \brief (SPI_CSR[2]) 15 bits for transfer */
#define   SPI_CSR_BITS_16_BIT (0x8u << 4) /**< \brief (SPI_CSR[2]) 16 bits for transfer */
#define SPI_CSR_SCBR_Pos 8
#define SPI_CSR_SCBR_Msk (0xffu << SPI_CSR_SCBR_Pos) /**< \brief (SPI_CSR[2]) Serial Clock Bit Rate */
#define SPI_CSR_SCBR(value) ((SPI_CSR_SCBR_Msk & ((value) << SPI_CSR_SCBR_Pos)))
#define SPI_CSR_DLYBS_Pos 16
#define SPI_CSR_DLYBS_Msk (0xffu << SPI_CSR_DLYBS_Pos) /**< \brief (SPI_CSR[2]) Delay Before SPCK */
#define SPI_CSR_DLYBS(value) ((SPI_CSR_DLYBS_Msk & ((value) << SPI_CSR_DLYBS_Pos)))
#define SPI_CSR_DLYBCT_Pos 24
#define SPI_CSR_DLYBCT_Msk (0xffu << SPI_CSR_DLYBCT_Pos) /**< \brief (SPI_CSR[2]) Delay Between Consecutive Transfers */
#define SPI_CSR_DLYBCT(value) ((SPI_CSR_DLYBCT_Msk & ((value) << SPI_CSR_DLYBCT_Pos)))
/* -------- SPI_FMR : (FLEXCOM Offset: 0x440) SPI FIFO Mode Register -------- */
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
/* -------- SPI_FLR : (FLEXCOM Offset: 0x444) SPI FIFO Level Register -------- */
#define SPI_FLR_TXFL_Pos 0
#define SPI_FLR_TXFL_Msk (0x3fu << SPI_FLR_TXFL_Pos) /**< \brief (SPI_FLR) Transmit FIFO Level */
#define SPI_FLR_RXFL_Pos 16
#define SPI_FLR_RXFL_Msk (0x3fu << SPI_FLR_RXFL_Pos) /**< \brief (SPI_FLR) Receive FIFO Level */
/* -------- SPI_CMPR : (FLEXCOM Offset: 0x448) SPI Comparison Register -------- */
#define SPI_CMPR_VAL1_Pos 0
#define SPI_CMPR_VAL1_Msk (0xffffu << SPI_CMPR_VAL1_Pos) /**< \brief (SPI_CMPR) First Comparison Value for Received Character */
#define SPI_CMPR_VAL1(value) ((SPI_CMPR_VAL1_Msk & ((value) << SPI_CMPR_VAL1_Pos)))
#define SPI_CMPR_VAL2_Pos 16
#define SPI_CMPR_VAL2_Msk (0xffffu << SPI_CMPR_VAL2_Pos) /**< \brief (SPI_CMPR) Second Comparison Value for Received Character */
#define SPI_CMPR_VAL2(value) ((SPI_CMPR_VAL2_Msk & ((value) << SPI_CMPR_VAL2_Pos)))
/* -------- SPI_WPMR : (FLEXCOM Offset: 0x4E4) SPI Write Protection Mode Register -------- */
#define SPI_WPMR_WPEN (0x1u << 0) /**< \brief (SPI_WPMR) Write Protection Enable */
#define SPI_WPMR_WPKEY_Pos 8
#define SPI_WPMR_WPKEY_Msk (0xffffffu << SPI_WPMR_WPKEY_Pos) /**< \brief (SPI_WPMR) Write Protection Key */
#define SPI_WPMR_WPKEY(value) ((SPI_WPMR_WPKEY_Msk & ((value) << SPI_WPMR_WPKEY_Pos)))
#define   SPI_WPMR_WPKEY_PASSWD (0x535049u << 8) /**< \brief (SPI_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0 */
/* -------- SPI_WPSR : (FLEXCOM Offset: 0x4E8) SPI Write Protection Status Register -------- */
#define SPI_WPSR_WPVS (0x1u << 0) /**< \brief (SPI_WPSR) Write Protection Violation Status */
#define SPI_WPSR_WPVSRC_Pos 8
#define SPI_WPSR_WPVSRC_Msk (0xffu << SPI_WPSR_WPVSRC_Pos) /**< \brief (SPI_WPSR) Write Protection Violation Source */
/* -------- SPI_VERSION : (FLEXCOM Offset: 0x4FC) SPI Version Register -------- */
#define SPI_VERSION_VERSION_Pos 0
#define SPI_VERSION_VERSION_Msk (0xfffu << SPI_VERSION_VERSION_Pos) /**< \brief (SPI_VERSION) Version of the Hardware Module */
#define SPI_VERSION_MFN_Pos 16
#define SPI_VERSION_MFN_Msk (0x7u << SPI_VERSION_MFN_Pos) /**< \brief (SPI_VERSION) Metal Fix Number */
/* -------- TWI_CR : (FLEXCOM Offset: 0x600) TWI Control Register -------- */
#define TWI_CR_START (0x1u << 0) /**< \brief (TWI_CR) Send a START Condition */
#define TWI_CR_STOP (0x1u << 1) /**< \brief (TWI_CR) Send a STOP Condition */
#define TWI_CR_MSEN (0x1u << 2) /**< \brief (TWI_CR) TWI Master Mode Enabled */
#define TWI_CR_MSDIS (0x1u << 3) /**< \brief (TWI_CR) TWI Master Mode Disabled */
#define TWI_CR_SVEN (0x1u << 4) /**< \brief (TWI_CR) TWI Slave Mode Enabled */
#define TWI_CR_SVDIS (0x1u << 5) /**< \brief (TWI_CR) TWI Slave Mode Disabled */
#define TWI_CR_QUICK (0x1u << 6) /**< \brief (TWI_CR) SMBus Quick Command */
#define TWI_CR_SWRST (0x1u << 7) /**< \brief (TWI_CR) Software Reset */
#define TWI_CR_HSEN (0x1u << 8) /**< \brief (TWI_CR) TWI High-Speed Mode Enabled */
#define TWI_CR_HSDIS (0x1u << 9) /**< \brief (TWI_CR) TWI High-Speed Mode Disabled */
#define TWI_CR_SMBEN (0x1u << 10) /**< \brief (TWI_CR) SMBus Mode Enabled */
#define TWI_CR_SMBDIS (0x1u << 11) /**< \brief (TWI_CR) SMBus Mode Disabled */
#define TWI_CR_PECEN (0x1u << 12) /**< \brief (TWI_CR) Packet Error Checking Enable */
#define TWI_CR_PECDIS (0x1u << 13) /**< \brief (TWI_CR) Packet Error Checking Disable */
#define TWI_CR_PECRQ (0x1u << 14) /**< \brief (TWI_CR) PEC Request */
#define TWI_CR_CLEAR (0x1u << 15) /**< \brief (TWI_CR) Bus CLEAR Command */
#define TWI_CR_ACMEN (0x1u << 16) /**< \brief (TWI_CR) Alternative Command Mode Enable */
#define TWI_CR_ACMDIS (0x1u << 17) /**< \brief (TWI_CR) Alternative Command Mode Disable */
#define TWI_CR_THRCLR (0x1u << 24) /**< \brief (TWI_CR) Transmit Holding Register Clear */
#define TWI_CR_LOCKCLR (0x1u << 26) /**< \brief (TWI_CR) Lock Clear */
#define TWI_CR_FIFOEN (0x1u << 28) /**< \brief (TWI_CR) FIFO Enable */
#define TWI_CR_FIFODIS (0x1u << 29) /**< \brief (TWI_CR) FIFO Disable */
/* -------- TWI_MMR : (FLEXCOM Offset: 0x604) TWI Master Mode Register -------- */
#define TWI_MMR_IADRSZ_Pos 8
#define TWI_MMR_IADRSZ_Msk (0x3u << TWI_MMR_IADRSZ_Pos) /**< \brief (TWI_MMR) Internal Device Address Size */
#define TWI_MMR_IADRSZ(value) ((TWI_MMR_IADRSZ_Msk & ((value) << TWI_MMR_IADRSZ_Pos)))
#define   TWI_MMR_IADRSZ_NONE (0x0u << 8) /**< \brief (TWI_MMR) No internal device address */
#define   TWI_MMR_IADRSZ_1_BYTE (0x1u << 8) /**< \brief (TWI_MMR) One-byte internal device address */
#define   TWI_MMR_IADRSZ_2_BYTE (0x2u << 8) /**< \brief (TWI_MMR) Two-byte internal device address */
#define   TWI_MMR_IADRSZ_3_BYTE (0x3u << 8) /**< \brief (TWI_MMR) Three-byte internal device address */
#define TWI_MMR_MREAD (0x1u << 12) /**< \brief (TWI_MMR) Master Read Direction */
#define TWI_MMR_DADR_Pos 16
#define TWI_MMR_DADR_Msk (0x7fu << TWI_MMR_DADR_Pos) /**< \brief (TWI_MMR) Device Address */
#define TWI_MMR_DADR(value) ((TWI_MMR_DADR_Msk & ((value) << TWI_MMR_DADR_Pos)))
/* -------- TWI_SMR : (FLEXCOM Offset: 0x608) TWI Slave Mode Register -------- */
#define TWI_SMR_NACKEN (0x1u << 0) /**< \brief (TWI_SMR) Slave Receiver Data Phase NACK Enable */
#define TWI_SMR_SMDA (0x1u << 2) /**< \brief (TWI_SMR) SMBus Default Address */
#define TWI_SMR_SMHH (0x1u << 3) /**< \brief (TWI_SMR) SMBus Host Header */
#define TWI_SMR_SCLWSDIS (0x1u << 6) /**< \brief (TWI_SMR) Clock Wait State Disable */
#define TWI_SMR_MASK_Pos 8
#define TWI_SMR_MASK_Msk (0x7fu << TWI_SMR_MASK_Pos) /**< \brief (TWI_SMR) Slave Address Mask */
#define TWI_SMR_MASK(value) ((TWI_SMR_MASK_Msk & ((value) << TWI_SMR_MASK_Pos)))
#define TWI_SMR_SADR_Pos 16
#define TWI_SMR_SADR_Msk (0x7fu << TWI_SMR_SADR_Pos) /**< \brief (TWI_SMR) Slave Address */
#define TWI_SMR_SADR(value) ((TWI_SMR_SADR_Msk & ((value) << TWI_SMR_SADR_Pos)))
#define TWI_SMR_SADR1EN (0x1u << 28) /**< \brief (TWI_SMR) Slave Address 1 Enable */
#define TWI_SMR_SADR2EN (0x1u << 29) /**< \brief (TWI_SMR) Slave Address 2 Enable */
#define TWI_SMR_SADR3EN (0x1u << 30) /**< \brief (TWI_SMR) Slave Address 3 Enable */
#define TWI_SMR_DATAMEN (0x1u << 31) /**< \brief (TWI_SMR) Data Matching Enable */
/* -------- TWI_IADR : (FLEXCOM Offset: 0x60C) TWI Internal Address Register -------- */
#define TWI_IADR_IADR_Pos 0
#define TWI_IADR_IADR_Msk (0xffffffu << TWI_IADR_IADR_Pos) /**< \brief (TWI_IADR) Internal Address */
#define TWI_IADR_IADR(value) ((TWI_IADR_IADR_Msk & ((value) << TWI_IADR_IADR_Pos)))
/* -------- TWI_CWGR : (FLEXCOM Offset: 0x610) TWI Clock Waveform Generator Register -------- */
#define TWI_CWGR_CLDIV_Pos 0
#define TWI_CWGR_CLDIV_Msk (0xffu << TWI_CWGR_CLDIV_Pos) /**< \brief (TWI_CWGR) Clock Low Divider */
#define TWI_CWGR_CLDIV(value) ((TWI_CWGR_CLDIV_Msk & ((value) << TWI_CWGR_CLDIV_Pos)))
#define TWI_CWGR_CHDIV_Pos 8
#define TWI_CWGR_CHDIV_Msk (0xffu << TWI_CWGR_CHDIV_Pos) /**< \brief (TWI_CWGR) Clock High Divider */
#define TWI_CWGR_CHDIV(value) ((TWI_CWGR_CHDIV_Msk & ((value) << TWI_CWGR_CHDIV_Pos)))
#define TWI_CWGR_CKDIV_Pos 16
#define TWI_CWGR_CKDIV_Msk (0x7u << TWI_CWGR_CKDIV_Pos) /**< \brief (TWI_CWGR) Clock Divider */
#define TWI_CWGR_CKDIV(value) ((TWI_CWGR_CKDIV_Msk & ((value) << TWI_CWGR_CKDIV_Pos)))
#define TWI_CWGR_BRSRCCLK (0x1u << 20) /**< \brief (TWI_CWGR) Bit Rate Source Clock */
#define   TWI_CWGR_BRSRCCLK_PERIPH_CLK (0x0u << 20) /**< \brief (TWI_CWGR) The peripheral clock is the source clock for the bit rate generation. */
#define   TWI_CWGR_BRSRCCLK_PMC_PCK (0x1u << 20) /**< \brief (TWI_CWGR) PMC PCKx is the source clock for the bit rate generation, thus the bit rate can be independent of the core/peripheral clock. */
#define TWI_CWGR_HOLD_Pos 24
#define TWI_CWGR_HOLD_Msk (0x1fu << TWI_CWGR_HOLD_Pos) /**< \brief (TWI_CWGR) TWD Hold Time Versus TWCK Falling */
#define TWI_CWGR_HOLD(value) ((TWI_CWGR_HOLD_Msk & ((value) << TWI_CWGR_HOLD_Pos)))
/* -------- TWI_SR : (FLEXCOM Offset: 0x620) TWI Status Register -------- */
#define TWI_SR_TXCOMP (0x1u << 0) /**< \brief (TWI_SR) Transmission Completed (cleared by writing TWI_THR) */
#define TWI_SR_RXRDY (0x1u << 1) /**< \brief (TWI_SR) Receive Holding Register Ready (cleared when reading TWI_RHR) */
#define TWI_SR_TXRDY (0x1u << 2) /**< \brief (TWI_SR) Transmit Holding Register Ready (cleared by writing TWI_THR) */
#define TWI_SR_SVREAD (0x1u << 3) /**< \brief (TWI_SR) Slave Read */
#define TWI_SR_SVACC (0x1u << 4) /**< \brief (TWI_SR) Slave Access */
#define TWI_SR_GACC (0x1u << 5) /**< \brief (TWI_SR) General Call Access (cleared on read) */
#define TWI_SR_OVRE (0x1u << 6) /**< \brief (TWI_SR) Overrun Error (cleared on read) */
#define TWI_SR_UNRE (0x1u << 7) /**< \brief (TWI_SR) Underrun Error (cleared on read) */
#define TWI_SR_NACK (0x1u << 8) /**< \brief (TWI_SR) Not Acknowledged (cleared on read) */
#define TWI_SR_ARBLST (0x1u << 9) /**< \brief (TWI_SR) Arbitration Lost (cleared on read) */
#define TWI_SR_SCLWS (0x1u << 10) /**< \brief (TWI_SR) Clock Wait State */
#define TWI_SR_EOSACC (0x1u << 11) /**< \brief (TWI_SR) End Of Slave Access (cleared on read) */
#define TWI_SR_MCACK (0x1u << 16) /**< \brief (TWI_SR) Master Code Acknowledge (cleared on read) */
#define TWI_SR_TOUT (0x1u << 18) /**< \brief (TWI_SR) Timeout Error (cleared on read) */
#define TWI_SR_PECERR (0x1u << 19) /**< \brief (TWI_SR) PEC Error (cleared on read) */
#define TWI_SR_SMBDAM (0x1u << 20) /**< \brief (TWI_SR) SMBus Default Address Match (cleared on read) */
#define TWI_SR_SMBHHM (0x1u << 21) /**< \brief (TWI_SR) SMBus Host Header Address Match (cleared on read) */
#define TWI_SR_LOCK (0x1u << 23) /**< \brief (TWI_SR) TWI Lock Due to Frame Errors */
#define TWI_SR_SCL (0x1u << 24) /**< \brief (TWI_SR) SCL line value */
#define TWI_SR_SDA (0x1u << 25) /**< \brief (TWI_SR) SDA line value */
/* -------- TWI_IER : (FLEXCOM Offset: 0x624) TWI Interrupt Enable Register -------- */
#define TWI_IER_TXCOMP (0x1u << 0) /**< \brief (TWI_IER) Transmission Completed Interrupt Enable */
#define TWI_IER_RXRDY (0x1u << 1) /**< \brief (TWI_IER) Receive Holding Register Ready Interrupt Enable */
#define TWI_IER_TXRDY (0x1u << 2) /**< \brief (TWI_IER) Transmit Holding Register Ready Interrupt Enable */
#define TWI_IER_SVACC (0x1u << 4) /**< \brief (TWI_IER) Slave Access Interrupt Enable */
#define TWI_IER_GACC (0x1u << 5) /**< \brief (TWI_IER) General Call Access Interrupt Enable */
#define TWI_IER_OVRE (0x1u << 6) /**< \brief (TWI_IER) Overrun Error Interrupt Enable */
#define TWI_IER_UNRE (0x1u << 7) /**< \brief (TWI_IER) Underrun Error Interrupt Enable */
#define TWI_IER_NACK (0x1u << 8) /**< \brief (TWI_IER) Not Acknowledge Interrupt Enable */
#define TWI_IER_ARBLST (0x1u << 9) /**< \brief (TWI_IER) Arbitration Lost Interrupt Enable */
#define TWI_IER_SCL_WS (0x1u << 10) /**< \brief (TWI_IER) Clock Wait State Interrupt Enable */
#define TWI_IER_EOSACC (0x1u << 11) /**< \brief (TWI_IER) End Of Slave Access Interrupt Enable */
#define TWI_IER_ENDRX (0x1u << 12) /**< \brief (TWI_IER) End of Receive Buffer Interrupt Enable */
#define TWI_IER_ENDTX (0x1u << 13) /**< \brief (TWI_IER) End of Transmit Buffer Interrupt Enable */
#define TWI_IER_RXBUFF (0x1u << 14) /**< \brief (TWI_IER) Receive Buffer Full Interrupt Enable */
#define TWI_IER_TXBUFE (0x1u << 15) /**< \brief (TWI_IER) Transmit Buffer Empty Interrupt Enable */
#define TWI_IER_MCACK (0x1u << 16) /**< \brief (TWI_IER) Master Code Acknowledge Interrupt Enable */
#define TWI_IER_TOUT (0x1u << 18) /**< \brief (TWI_IER) Timeout Error Interrupt Enable */
#define TWI_IER_PECERR (0x1u << 19) /**< \brief (TWI_IER) PEC Error Interrupt Enable */
#define TWI_IER_SMBDAM (0x1u << 20) /**< \brief (TWI_IER) SMBus Default Address Match Interrupt Enable */
#define TWI_IER_SMBHHM (0x1u << 21) /**< \brief (TWI_IER) SMBus Host Header Address Match Interrupt Enable */
/* -------- TWI_IDR : (FLEXCOM Offset: 0x628) TWI Interrupt Disable Register -------- */
#define TWI_IDR_TXCOMP (0x1u << 0) /**< \brief (TWI_IDR) Transmission Completed Interrupt Disable */
#define TWI_IDR_RXRDY (0x1u << 1) /**< \brief (TWI_IDR) Receive Holding Register Ready Interrupt Disable */
#define TWI_IDR_TXRDY (0x1u << 2) /**< \brief (TWI_IDR) Transmit Holding Register Ready Interrupt Disable */
#define TWI_IDR_SVACC (0x1u << 4) /**< \brief (TWI_IDR) Slave Access Interrupt Disable */
#define TWI_IDR_GACC (0x1u << 5) /**< \brief (TWI_IDR) General Call Access Interrupt Disable */
#define TWI_IDR_OVRE (0x1u << 6) /**< \brief (TWI_IDR) Overrun Error Interrupt Disable */
#define TWI_IDR_UNRE (0x1u << 7) /**< \brief (TWI_IDR) Underrun Error Interrupt Disable */
#define TWI_IDR_NACK (0x1u << 8) /**< \brief (TWI_IDR) Not Acknowledge Interrupt Disable */
#define TWI_IDR_ARBLST (0x1u << 9) /**< \brief (TWI_IDR) Arbitration Lost Interrupt Disable */
#define TWI_IDR_SCL_WS (0x1u << 10) /**< \brief (TWI_IDR) Clock Wait State Interrupt Disable */
#define TWI_IDR_EOSACC (0x1u << 11) /**< \brief (TWI_IDR) End Of Slave Access Interrupt Disable */
#define TWI_IDR_ENDRX (0x1u << 12) /**< \brief (TWI_IDR) End of Receive Buffer Interrupt Disable */
#define TWI_IDR_ENDTX (0x1u << 13) /**< \brief (TWI_IDR) End of Transmit Buffer Interrupt Disable */
#define TWI_IDR_RXBUFF (0x1u << 14) /**< \brief (TWI_IDR) Receive Buffer Full Interrupt Disable */
#define TWI_IDR_TXBUFE (0x1u << 15) /**< \brief (TWI_IDR) Transmit Buffer Empty Interrupt Disable */
#define TWI_IDR_MCACK (0x1u << 16) /**< \brief (TWI_IDR) Master Code Acknowledge Interrupt Disable */
#define TWI_IDR_TOUT (0x1u << 18) /**< \brief (TWI_IDR) Timeout Error Interrupt Disable */
#define TWI_IDR_PECERR (0x1u << 19) /**< \brief (TWI_IDR) PEC Error Interrupt Disable */
#define TWI_IDR_SMBDAM (0x1u << 20) /**< \brief (TWI_IDR) SMBus Default Address Match Interrupt Disable */
#define TWI_IDR_SMBHHM (0x1u << 21) /**< \brief (TWI_IDR) SMBus Host Header Address Match Interrupt Disable */
/* -------- TWI_IMR : (FLEXCOM Offset: 0x62C) TWI Interrupt Mask Register -------- */
#define TWI_IMR_TXCOMP (0x1u << 0) /**< \brief (TWI_IMR) Transmission Completed Interrupt Mask */
#define TWI_IMR_RXRDY (0x1u << 1) /**< \brief (TWI_IMR) Receive Holding Register Ready Interrupt Mask */
#define TWI_IMR_TXRDY (0x1u << 2) /**< \brief (TWI_IMR) Transmit Holding Register Ready Interrupt Mask */
#define TWI_IMR_SVACC (0x1u << 4) /**< \brief (TWI_IMR) Slave Access Interrupt Mask */
#define TWI_IMR_GACC (0x1u << 5) /**< \brief (TWI_IMR) General Call Access Interrupt Mask */
#define TWI_IMR_OVRE (0x1u << 6) /**< \brief (TWI_IMR) Overrun Error Interrupt Mask */
#define TWI_IMR_UNRE (0x1u << 7) /**< \brief (TWI_IMR) Underrun Error Interrupt Mask */
#define TWI_IMR_NACK (0x1u << 8) /**< \brief (TWI_IMR) Not Acknowledge Interrupt Mask */
#define TWI_IMR_ARBLST (0x1u << 9) /**< \brief (TWI_IMR) Arbitration Lost Interrupt Mask */
#define TWI_IMR_SCL_WS (0x1u << 10) /**< \brief (TWI_IMR) Clock Wait State Interrupt Mask */
#define TWI_IMR_EOSACC (0x1u << 11) /**< \brief (TWI_IMR) End Of Slave Access Interrupt Mask */
#define TWI_IMR_ENDRX (0x1u << 12) /**< \brief (TWI_IMR) End of Receive Buffer Interrupt Mask */
#define TWI_IMR_ENDTX (0x1u << 13) /**< \brief (TWI_IMR) End of Transmit Buffer Interrupt Mask */
#define TWI_IMR_RXBUFF (0x1u << 14) /**< \brief (TWI_IMR) Receive Buffer Full Interrupt Mask */
#define TWI_IMR_TXBUFE (0x1u << 15) /**< \brief (TWI_IMR) Transmit Buffer Empty Interrupt Mask */
#define TWI_IMR_MCACK (0x1u << 16) /**< \brief (TWI_IMR) Master Code Acknowledge Interrupt Mask */
#define TWI_IMR_TOUT (0x1u << 18) /**< \brief (TWI_IMR) Timeout Error Interrupt Mask */
#define TWI_IMR_PECERR (0x1u << 19) /**< \brief (TWI_IMR) PEC Error Interrupt Mask */
#define TWI_IMR_SMBDAM (0x1u << 20) /**< \brief (TWI_IMR) SMBus Default Address Match Interrupt Mask */
#define TWI_IMR_SMBHHM (0x1u << 21) /**< \brief (TWI_IMR) SMBus Host Header Address Match Interrupt Mask */
/* -------- TWI_RHR : (FLEXCOM Offset: 0x630) TWI Receive Holding Register -------- */
#define TWI_RHR_RXDATA_Pos 0
#define TWI_RHR_RXDATA_Msk (0xffu << TWI_RHR_RXDATA_Pos) /**< \brief (TWI_RHR) Master or Slave Receive Holding Data */
#define TWI_RHR_RXDATA0_Pos 0
#define TWI_RHR_RXDATA0_Msk (0xffu << TWI_RHR_RXDATA0_Pos) /**< \brief (TWI_RHR) Master or Slave Receive Holding Data 0 */
#define TWI_RHR_RXDATA1_Pos 8
#define TWI_RHR_RXDATA1_Msk (0xffu << TWI_RHR_RXDATA1_Pos) /**< \brief (TWI_RHR) Master or Slave Receive Holding Data 1 */
#define TWI_RHR_RXDATA2_Pos 16
#define TWI_RHR_RXDATA2_Msk (0xffu << TWI_RHR_RXDATA2_Pos) /**< \brief (TWI_RHR) Master or Slave Receive Holding Data 2 */
#define TWI_RHR_RXDATA3_Pos 24
#define TWI_RHR_RXDATA3_Msk (0xffu << TWI_RHR_RXDATA3_Pos) /**< \brief (TWI_RHR) Master or Slave Receive Holding Data 3 */
/* -------- TWI_THR : (FLEXCOM Offset: 0x634) TWI Transmit Holding Register -------- */
#define TWI_THR_TXDATA_Pos 0
#define TWI_THR_TXDATA_Msk (0xffu << TWI_THR_TXDATA_Pos) /**< \brief (TWI_THR) Master or Slave Transmit Holding Data */
#define TWI_THR_TXDATA(value) ((TWI_THR_TXDATA_Msk & ((value) << TWI_THR_TXDATA_Pos)))
#define TWI_THR_TXDATA0_Pos 0
#define TWI_THR_TXDATA0_Msk (0xffu << TWI_THR_TXDATA0_Pos) /**< \brief (TWI_THR) Master or Slave Transmit Holding Data 0 */
#define TWI_THR_TXDATA0(value) ((TWI_THR_TXDATA0_Msk & ((value) << TWI_THR_TXDATA0_Pos)))
#define TWI_THR_TXDATA1_Pos 8
#define TWI_THR_TXDATA1_Msk (0xffu << TWI_THR_TXDATA1_Pos) /**< \brief (TWI_THR) Master or Slave Transmit Holding Data 1 */
#define TWI_THR_TXDATA1(value) ((TWI_THR_TXDATA1_Msk & ((value) << TWI_THR_TXDATA1_Pos)))
#define TWI_THR_TXDATA2_Pos 16
#define TWI_THR_TXDATA2_Msk (0xffu << TWI_THR_TXDATA2_Pos) /**< \brief (TWI_THR) Master or Slave Transmit Holding Data 2 */
#define TWI_THR_TXDATA2(value) ((TWI_THR_TXDATA2_Msk & ((value) << TWI_THR_TXDATA2_Pos)))
#define TWI_THR_TXDATA3_Pos 24
#define TWI_THR_TXDATA3_Msk (0xffu << TWI_THR_TXDATA3_Pos) /**< \brief (TWI_THR) Master or Slave Transmit Holding Data 3 */
#define TWI_THR_TXDATA3(value) ((TWI_THR_TXDATA3_Msk & ((value) << TWI_THR_TXDATA3_Pos)))
/* -------- TWI_SMBTR : (FLEXCOM Offset: 0x638) TWI SMBus Timing Register -------- */
#define TWI_SMBTR_PRESC_Pos 0
#define TWI_SMBTR_PRESC_Msk (0xfu << TWI_SMBTR_PRESC_Pos) /**< \brief (TWI_SMBTR) SMBus Clock Prescaler */
#define TWI_SMBTR_PRESC(value) ((TWI_SMBTR_PRESC_Msk & ((value) << TWI_SMBTR_PRESC_Pos)))
#define TWI_SMBTR_TLOWS_Pos 8
#define TWI_SMBTR_TLOWS_Msk (0xffu << TWI_SMBTR_TLOWS_Pos) /**< \brief (TWI_SMBTR) Slave Clock Stretch Maximum Cycles */
#define TWI_SMBTR_TLOWS(value) ((TWI_SMBTR_TLOWS_Msk & ((value) << TWI_SMBTR_TLOWS_Pos)))
#define TWI_SMBTR_TLOWM_Pos 16
#define TWI_SMBTR_TLOWM_Msk (0xffu << TWI_SMBTR_TLOWM_Pos) /**< \brief (TWI_SMBTR) Master Clock Stretch Maximum Cycles */
#define TWI_SMBTR_TLOWM(value) ((TWI_SMBTR_TLOWM_Msk & ((value) << TWI_SMBTR_TLOWM_Pos)))
#define TWI_SMBTR_THMAX_Pos 24
#define TWI_SMBTR_THMAX_Msk (0xffu << TWI_SMBTR_THMAX_Pos) /**< \brief (TWI_SMBTR) Clock High Maximum Cycles */
#define TWI_SMBTR_THMAX(value) ((TWI_SMBTR_THMAX_Msk & ((value) << TWI_SMBTR_THMAX_Pos)))
/* -------- TWI_ACR : (FLEXCOM Offset: 0x640) TWI Alternative Command Register -------- */
#define TWI_ACR_DATAL_Pos 0
#define TWI_ACR_DATAL_Msk (0xffu << TWI_ACR_DATAL_Pos) /**< \brief (TWI_ACR) Data Length */
#define TWI_ACR_DATAL(value) ((TWI_ACR_DATAL_Msk & ((value) << TWI_ACR_DATAL_Pos)))
#define TWI_ACR_DIR (0x1u << 8) /**< \brief (TWI_ACR) Transfer Direction */
#define TWI_ACR_PEC (0x1u << 9) /**< \brief (TWI_ACR) PEC Request (SMBus Mode only) */
#define TWI_ACR_NDATAL_Pos 16
#define TWI_ACR_NDATAL_Msk (0xffu << TWI_ACR_NDATAL_Pos) /**< \brief (TWI_ACR) Next Data Length */
#define TWI_ACR_NDATAL(value) ((TWI_ACR_NDATAL_Msk & ((value) << TWI_ACR_NDATAL_Pos)))
#define TWI_ACR_NDIR (0x1u << 24) /**< \brief (TWI_ACR) Next Transfer Direction */
#define TWI_ACR_NPEC (0x1u << 25) /**< \brief (TWI_ACR) Next PEC Request (SMBus Mode only) */
/* -------- TWI_FILTR : (FLEXCOM Offset: 0x644) TWI Filter Register -------- */
#define TWI_FILTR_FILT (0x1u << 0) /**< \brief (TWI_FILTR) RX Digital Filter */
#define TWI_FILTR_PADFEN (0x1u << 1) /**< \brief (TWI_FILTR) PAD Filter Enable */
#define TWI_FILTR_PADFCFG (0x1u << 2) /**< \brief (TWI_FILTR) PAD Filter Config */
#define TWI_FILTR_THRES_Pos 8
#define TWI_FILTR_THRES_Msk (0x7u << TWI_FILTR_THRES_Pos) /**< \brief (TWI_FILTR) Digital Filter Threshold */
#define TWI_FILTR_THRES(value) ((TWI_FILTR_THRES_Msk & ((value) << TWI_FILTR_THRES_Pos)))
/* -------- TWI_SWMR : (FLEXCOM Offset: 0x64C) TWI SleepWalking Matching Register -------- */
#define TWI_SWMR_SADR1_Pos 0
#define TWI_SWMR_SADR1_Msk (0x7fu << TWI_SWMR_SADR1_Pos) /**< \brief (TWI_SWMR) Slave Address 1 */
#define TWI_SWMR_SADR1(value) ((TWI_SWMR_SADR1_Msk & ((value) << TWI_SWMR_SADR1_Pos)))
#define TWI_SWMR_SADR2_Pos 8
#define TWI_SWMR_SADR2_Msk (0x7fu << TWI_SWMR_SADR2_Pos) /**< \brief (TWI_SWMR) Slave Address 2 */
#define TWI_SWMR_SADR2(value) ((TWI_SWMR_SADR2_Msk & ((value) << TWI_SWMR_SADR2_Pos)))
#define TWI_SWMR_SADR3_Pos 16
#define TWI_SWMR_SADR3_Msk (0x7fu << TWI_SWMR_SADR3_Pos) /**< \brief (TWI_SWMR) Slave Address 3 */
#define TWI_SWMR_SADR3(value) ((TWI_SWMR_SADR3_Msk & ((value) << TWI_SWMR_SADR3_Pos)))
#define TWI_SWMR_DATAM_Pos 24
#define TWI_SWMR_DATAM_Msk (0xffu << TWI_SWMR_DATAM_Pos) /**< \brief (TWI_SWMR) Data Match */
#define TWI_SWMR_DATAM(value) ((TWI_SWMR_DATAM_Msk & ((value) << TWI_SWMR_DATAM_Pos)))
/* -------- TWI_FMR : (FLEXCOM Offset: 0x650) TWI FIFO Mode Register -------- */
#define TWI_FMR_TXRDYM_Pos 0
#define TWI_FMR_TXRDYM_Msk (0x3u << TWI_FMR_TXRDYM_Pos) /**< \brief (TWI_FMR) Transmitter Ready Mode */
#define TWI_FMR_TXRDYM(value) ((TWI_FMR_TXRDYM_Msk & ((value) << TWI_FMR_TXRDYM_Pos)))
#define   TWI_FMR_TXRDYM_ONE_DATA (0x0u << 0) /**< \brief (TWI_FMR) TXRDY will be at level '1' when at least one data can be written in the Transmit FIFO */
#define   TWI_FMR_TXRDYM_TWO_DATA (0x1u << 0) /**< \brief (TWI_FMR) TXRDY will be at level '1' when at least two data can be written in the Transmit FIFO */
#define   TWI_FMR_TXRDYM_FOUR_DATA (0x2u << 0) /**< \brief (TWI_FMR) TXRDY will be at level '1' when at least four data can be written in the Transmit FIFO */
#define TWI_FMR_RXRDYM_Pos 4
#define TWI_FMR_RXRDYM_Msk (0x3u << TWI_FMR_RXRDYM_Pos) /**< \brief (TWI_FMR) Receiver Ready Mode */
#define TWI_FMR_RXRDYM(value) ((TWI_FMR_RXRDYM_Msk & ((value) << TWI_FMR_RXRDYM_Pos)))
#define   TWI_FMR_RXRDYM_ONE_DATA (0x0u << 4) /**< \brief (TWI_FMR) RXRDY will be at level '1' when at least one unread data is in the Receive FIFO */
#define   TWI_FMR_RXRDYM_TWO_DATA (0x1u << 4) /**< \brief (TWI_FMR) RXRDY will be at level '1' when at least two unread data are in the Receive FIFO */
#define   TWI_FMR_RXRDYM_FOUR_DATA (0x2u << 4) /**< \brief (TWI_FMR) RXRDY will be at level '1' when at least four unread data are in the Receive FIFO */
#define TWI_FMR_TXFTHRES_Pos 16
#define TWI_FMR_TXFTHRES_Msk (0x3fu << TWI_FMR_TXFTHRES_Pos) /**< \brief (TWI_FMR) Transmit FIFO Threshold */
#define TWI_FMR_TXFTHRES(value) ((TWI_FMR_TXFTHRES_Msk & ((value) << TWI_FMR_TXFTHRES_Pos)))
#define TWI_FMR_RXFTHRES_Pos 24
#define TWI_FMR_RXFTHRES_Msk (0x3fu << TWI_FMR_RXFTHRES_Pos) /**< \brief (TWI_FMR) Receive FIFO Threshold */
#define TWI_FMR_RXFTHRES(value) ((TWI_FMR_RXFTHRES_Msk & ((value) << TWI_FMR_RXFTHRES_Pos)))
/* -------- TWI_FLR : (FLEXCOM Offset: 0x654) TWI FIFO Level Register -------- */
#define TWI_FLR_TXFL_Pos 0
#define TWI_FLR_TXFL_Msk (0x3fu << TWI_FLR_TXFL_Pos) /**< \brief (TWI_FLR) Transmit FIFO Level */
#define TWI_FLR_RXFL_Pos 16
#define TWI_FLR_RXFL_Msk (0x3fu << TWI_FLR_RXFL_Pos) /**< \brief (TWI_FLR) Receive FIFO Level */
/* -------- TWI_FSR : (FLEXCOM Offset: 0x660) TWI FIFO Status Register -------- */
#define TWI_FSR_TXFEF (0x1u << 0) /**< \brief (TWI_FSR) Transmit FIFO Empty Flag (cleared on read) */
#define TWI_FSR_TXFFF (0x1u << 1) /**< \brief (TWI_FSR) Transmit FIFO Full Flag (cleared on read) */
#define TWI_FSR_TXFTHF (0x1u << 2) /**< \brief (TWI_FSR) Transmit FIFO Threshold Flag (cleared on read) */
#define TWI_FSR_RXFEF (0x1u << 3) /**< \brief (TWI_FSR) Receive FIFO Empty Flag */
#define TWI_FSR_RXFFF (0x1u << 4) /**< \brief (TWI_FSR) Receive FIFO Full Flag */
#define TWI_FSR_RXFTHF (0x1u << 5) /**< \brief (TWI_FSR) Receive FIFO Threshold Flag */
#define TWI_FSR_TXFPTEF (0x1u << 6) /**< \brief (TWI_FSR) Transmit FIFO Pointer Error Flag */
#define TWI_FSR_RXFPTEF (0x1u << 7) /**< \brief (TWI_FSR) Receive FIFO Pointer Error Flag */
/* -------- TWI_FIER : (FLEXCOM Offset: 0x664) TWI FIFO Interrupt Enable Register -------- */
#define TWI_FIER_TXFEF (0x1u << 0) /**< \brief (TWI_FIER) TXFEF Interrupt Enable */
#define TWI_FIER_TXFFF (0x1u << 1) /**< \brief (TWI_FIER) TXFFF Interrupt Enable */
#define TWI_FIER_TXFTHF (0x1u << 2) /**< \brief (TWI_FIER) TXFTHF Interrupt Enable */
#define TWI_FIER_RXFEF (0x1u << 3) /**< \brief (TWI_FIER) RXFEF Interrupt Enable */
#define TWI_FIER_RXFFF (0x1u << 4) /**< \brief (TWI_FIER) RXFFF Interrupt Enable */
#define TWI_FIER_RXFTHF (0x1u << 5) /**< \brief (TWI_FIER) RXFTHF Interrupt Enable */
#define TWI_FIER_TXFPTEF (0x1u << 6) /**< \brief (TWI_FIER) TXFPTEF Interrupt Enable */
#define TWI_FIER_RXFPTEF (0x1u << 7) /**< \brief (TWI_FIER) RXFPTEF Interrupt Enable */
/* -------- TWI_FIDR : (FLEXCOM Offset: 0x668) TWI FIFO Interrupt Disable Register -------- */
#define TWI_FIDR_TXFEF (0x1u << 0) /**< \brief (TWI_FIDR) TXFEF Interrupt Disable */
#define TWI_FIDR_TXFFF (0x1u << 1) /**< \brief (TWI_FIDR) TXFFF Interrupt Disable */
#define TWI_FIDR_TXFTHF (0x1u << 2) /**< \brief (TWI_FIDR) TXFTHF Interrupt Disable */
#define TWI_FIDR_RXFEF (0x1u << 3) /**< \brief (TWI_FIDR) RXFEF Interrupt Disable */
#define TWI_FIDR_RXFFF (0x1u << 4) /**< \brief (TWI_FIDR) RXFFF Interrupt Disable */
#define TWI_FIDR_RXFTHF (0x1u << 5) /**< \brief (TWI_FIDR) RXFTHF Interrupt Disable */
#define TWI_FIDR_TXFPTEF (0x1u << 6) /**< \brief (TWI_FIDR) TXFPTEF Interrupt Disable */
#define TWI_FIDR_RXFPTEF (0x1u << 7) /**< \brief (TWI_FIDR) RXFPTEF Interrupt Disable */
/* -------- TWI_FIMR : (FLEXCOM Offset: 0x66C) TWI FIFO Interrupt Mask Register -------- */
#define TWI_FIMR_TXFEF (0x1u << 0) /**< \brief (TWI_FIMR) TXFEF Interrupt Mask */
#define TWI_FIMR_TXFFF (0x1u << 1) /**< \brief (TWI_FIMR) TXFFF Interrupt Mask */
#define TWI_FIMR_TXFTHF (0x1u << 2) /**< \brief (TWI_FIMR) TXFTHF Interrupt Mask */
#define TWI_FIMR_RXFEF (0x1u << 3) /**< \brief (TWI_FIMR) RXFEF Interrupt Mask */
#define TWI_FIMR_RXFFF (0x1u << 4) /**< \brief (TWI_FIMR) RXFFF Interrupt Mask */
#define TWI_FIMR_RXFTHF (0x1u << 5) /**< \brief (TWI_FIMR) RXFTHF Interrupt Mask */
#define TWI_FIMR_TXFPTEF (0x1u << 6) /**< \brief (TWI_FIMR) TXFPTEF Interrupt Mask */
#define TWI_FIMR_RXFPTEF (0x1u << 7) /**< \brief (TWI_FIMR) RXFPTEF Interrupt Mask */
/* -------- TWI_DR : (FLEXCOM Offset: 0x6D0) TWI Debug Register -------- */
#define TWI_DR_SWEN (0x1u << 0) /**< \brief (TWI_DR) SleepWalking Enable */
#define TWI_DR_CLKRQ (0x1u << 1) /**< \brief (TWI_DR) Clock Request */
#define TWI_DR_SWMATCH (0x1u << 2) /**< \brief (TWI_DR) SleepWalking Match */
#define TWI_DR_TRP (0x1u << 3) /**< \brief (TWI_DR) Transfer Pending */
/* -------- TWI_WPMR : (FLEXCOM Offset: 0x6E4) TWI Protection Mode Register -------- */
#define TWI_WPMR_WPEN (0x1u << 0) /**< \brief (TWI_WPMR) Write Protection Enable */
#define TWI_WPMR_WPKEY_Pos 8
#define TWI_WPMR_WPKEY_Msk (0xffffffu << TWI_WPMR_WPKEY_Pos) /**< \brief (TWI_WPMR) Write Protection Key */
#define TWI_WPMR_WPKEY(value) ((TWI_WPMR_WPKEY_Msk & ((value) << TWI_WPMR_WPKEY_Pos)))
#define   TWI_WPMR_WPKEY_PASSWD (0x545749u << 8) /**< \brief (TWI_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0 */
/* -------- TWI_WPSR : (FLEXCOM Offset: 0x6E8) TWI Protection Status Register -------- */
#define TWI_WPSR_WPVS (0x1u << 0) /**< \brief (TWI_WPSR) Write Protect Violation Status */
#define TWI_WPSR_WPVSRC_Pos 8
#define TWI_WPSR_WPVSRC_Msk (0xffffffu << TWI_WPSR_WPVSRC_Pos) /**< \brief (TWI_WPSR) Write Protection Violation Source */
/* -------- TWI_VER : (FLEXCOM Offset: 0x6FC) TWI Version Register -------- */
#define TWI_VER_VERSION_Pos 0
#define TWI_VER_VERSION_Msk (0xfffu << TWI_VER_VERSION_Pos) /**< \brief (TWI_VER) Version of the Hardware Module */
#define TWI_VER_MFN_Pos 16
#define TWI_VER_MFN_Msk (0x7u << TWI_VER_MFN_Pos) /**< \brief (TWI_VER) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_FLEXCOM_COMPONENT_ */
