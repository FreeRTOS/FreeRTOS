/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
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
/*                                                                              */

#ifndef _CHIP_H_
#define _CHIP_H_

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
#define __I  volatile	    /**< Defines 'read-only'  permissions */
#else
#define __I  volatile const /**< Defines 'read-only'  permissions */
#endif
#define   __O  volatile	      /**< Defines 'write-only' permissions */
#define   __IO volatile	      /**< Defines 'read/write' permissions */

/* ************************************************************************** */
/*   PERIPHERAL ID DEFINITIONS FOR SAMA5D2x */
/* ************************************************************************** */
/** \addtogroup SAMA5D2x_id Peripheral Ids Definitions */
/*@{*/

#define ID_SAIC_FIQ     ( 0) /**< \brief FIQ Interrupt ID (SAIC_FIQ) */
#define ID_ARM_PMU      ( 2) /**< \brief Performance Monitor Unit (PMU) (ARM_PMU) */
#define ID_PIT          ( 3) /**< \brief Periodic Interval Timer Interrupt (PIT) */
#define ID_WDT          ( 4) /**< \brief Watchdog timer Interrupt (WDT) */
#define ID_GMAC0        ( 5) /**< \brief Ethernet MAC (GMAC0) */
#define ID_XDMAC0       ( 6) /**< \brief DMA Controller 0 (XDMAC0) */
#define ID_XDMAC1       ( 7) /**< \brief DMA Controller 1 (XDMAC1) */
#define ID_ICM          ( 8) /**< \brief Integritry Check Monitor (ICM) */
#define ID_AES          ( 9) /**< \brief Advanced Enion Standard (AES) */
#define ID_AESB         (10) /**< \brief AES bridge (AESB) */
#define ID_TDES         (11) /**< \brief Triple Data Enion Standard (TDES) */
#define ID_SHA          (12) /**< \brief SHA Signature (SHA) */
#define ID_MPDDRC       (13) /**< \brief MPDDR controller (MPDDRC) */
#define ID_MATRIX1      (14) /**< \brief H32MX, 32-bit AHB Matrix (MATRIX1) */
#define ID_MATRIX0      (15) /**< \brief H64MX, 64-bit AHB Matrix (MATRIX0) */
#define ID_HSMC         (17) /**< \brief Multi-bit ECC Interrupt (HSMC) */
#define ID_PIOA         (18) /**< \brief Parallel I/O Controller (PIOA) */
#define ID_FLEXCOM0     (19) /**< \brief FLEXCOM 0 (FLEXCOM0) */
#define ID_USART0       (19) /**< \brief USART (USART0) from FLEXCOM0 */
#define ID_FCOMSPI0     (19) /**< \brief Serial Peripheral Interface (SPI0) from FLEXCOM0 */
#define ID_TWI0         (19) /**< \brief Two-Wire Interface (TWI0) from FLEXCOM0 */
#define ID_FLEXCOM1     (20) /**< \brief FLEXCOM 1 (FLEXCOM1) */
#define ID_USART1       (20) /**< \brief USART (USART1) from FLEXCOM1 */
#define ID_FCOMSPI1     (20) /**< \brief Serial Peripheral Interface (SPI1) from FLEXCOM1 */
#define ID_TWI1         (20) /**< \brief Two-Wire Interface (TWI1) from FLEXCOM1 */
#define ID_FLEXCOM2     (21) /**< \brief FLEXCOM 1 (FLEXCOM1) */
#define ID_USART2       (21) /**< \brief USART (USART1) from FLEXCOM1 */
#define ID_FCOMSPI2     (21) /**< \brief Serial Peripheral Interface (SPI1) from FLEXCOM1 */
#define ID_TWI2         (21) /**< \brief Two-Wire Interface (TWI1) from FLEXCOM1 */
#define ID_FLEXCOM3     (22) /**< \brief FLEXCOM 3 (FLEXCOM3) */
#define ID_USART3       (22) /**< \brief USART (USART3) from FLEXCOM3 */
#define ID_FCOMSPI3     (22) /**< \brief Serial Peripheral Interface (SPI3) from FLEXCOM3 */
#define ID_TWI3         (22) /**< \brief Two-Wire Interface (TWI3) from FLEXCOM3 */
#define ID_FLEXCOM4     (23) /**< \brief FLEXCOM 4 (FLEXCOM4) */
#define ID_USART4       (23) /**< \brief USART (USART4) from FLEXCOM4 */
#define ID_FCOMSPI4     (23) /**< \brief Serial Peripheral Interface (SPI4) from FLEXCOM4 */
#define ID_TWI4         (23) /**< \brief Two-Wire Interface (TWI4) from FLEXCOM4 */
#define ID_UART0        (24) /**< \brief UART 0 (UART0) */
#define ID_UART1        (25) /**< \brief UART 1 (UART1) */
#define ID_UART2        (26) /**< \brief UART 2 (UART2) */
#define ID_UART3        (27) /**< \brief UART 3 (UART3) */
#define ID_UART4        (28) /**< \brief UART 4 (UART4) */
#define ID_TWIHS0       (29) /**< \brief Two-Wire Interface 0 (TWIHS0) */
#define ID_TWIHS1       (30) /**< \brief Two-Wire Interface 1 (TWIHS1) */
#define ID_SDMMC0       (31) /**< \brief Secure Digital Multimedia Card Controller 0 (SDMMC0) */
#define ID_SDMMC1       (32) /**< \brief Secure Digital Multimedia Card Controller 1 (SDMMC1) */
#define ID_SPI0         (33) /**< \brief Serial Peripheral Interface 0 (SPI0) */
#define ID_SPI1         (34) /**< \brief Serial Peripheral Interface 1 (SPI1) */
#define ID_TC0          (35) /**< \brief Timer Counter 0 (ch. 0, 1, 2) (TC0) */
#define ID_TC1          (36) /**< \brief Timer Counter 1 (ch. 3, 4, 5) (TC1) */
#define ID_PWM          (38) /**< \brief Pulse Width Modulation Controller0 (ch. 0, 1, 2, 3) (PWM) */
#define ID_ADC          (40) /**< \brief Touch Screen ADC Controller (ADC) */
#define ID_UHPHS        (41) /**< \brief USB Host High Speed (UHPHS) */
#define ID_UDPHS        (42) /**< \brief USB Device High Speed (UDPHS) */
#define ID_SSC0         (43) /**< \brief Synchronous Serial Controller 0 (SSC0) */
#define ID_SSC1         (44) /**< \brief Synchronous Serial Controller 1 (SSC1) */
#define ID_LCDC         (45) /**< \brief LCD Controller (LCDC) */
#define ID_ISC          (46) /**< \brief Camera Interface (ISC) */
#define ID_TRNG         (47) /**< \brief True Random Number Generator (TRNG) */
#define ID_PDMIC        (48) /**< \brief Pulse Density Modulation Interface Controller (PDMIC) */
#define ID_AIC_IRQ      (49) /**< \brief IRQ Interrupt ID (AIC_IRQ) */
#define ID_SFC          (50) /**< \brief Fuse Controller (SFC) */
#define ID_SECURAM      (51) /**< \brief Secured RAM (SECURAM) */
#define ID_QSPI0        (52) /**< \brief QSPI 0 (QSPI0) */
#define ID_QSPI1        (53) /**< \brief QSPI 1 (QSPI1) */
#define ID_I2SC0        (54) /**< \brief Inter-IC Sound Controller 0 (I2SC0) */
#define ID_I2SC1        (55) /**< \brief Inter-IC Sound Controller 1 (I2SC1) */
#define ID_CAN0_INT0    (56) /**< \brief MCAN 0 Interrupt0 (CAN0_INT0) */
#define ID_CAN1_INT0    (57) /**< \brief MCAN 1 Interrupt0 (CAN1_INT0) */
#define ID_CLASSD       (59) /**< \brief Audio Class D amplifier (CLASSD) */
#define ID_SFR          (60) /**< \brief Special Function Register  (SFR) */
#define ID_SAIC         (61) /**< \brief Secured Advanced Interrupt Controller  (SAIC) */
#define ID_AIC          (62) /**< \brief Advanced Interrupt Controller  (AIC) */
#define ID_L2CC         (63) /**< \brief L2 Cache Controller (L2CC) */
#define ID_CAN0_INT1    (64) /**< \brief MCAN 0 Interrupt1 (CAN0_INT1) */
#define ID_CAN1_INT1    (65) /**< \brief MCAN 1 Interrupt1 (CAN1_INT1) */
#define ID_GMAC0_Q1     (66) /**< \brief GMAC Queue 1 Interrupt (GMAC0_Q1) */
#define ID_GMAC0_Q2     (67) /**< \brief GMAC Queue 2 Interrupt (GMAC0_Q2) */
#define ID_PIOB         (68) /**< \brief  (PIOB) */
#define ID_PIOC         (69) /**< \brief  (PIOC) */
#define ID_PIOD         (70) /**< \brief  (PIOD) */
#define ID_SDMMC0_TIMER (71) /**< \brief  (SDMMC0_TIMER) */
#define ID_SDMMC1_TIMER (72) /**< \brief  (SDMMC1_TIMER) */
#define ID_SYSC         (74) /**< \brief System Controller Interrupt, RTC, RSTC, PMC (SYSC) */
#define ID_ACC          (75) /**< \brief Analog Comparator (ACC) */
#define ID_RXLP         (76) /**< \brief Uart Low Power (RXLP) */
#define ID_CHIPID       (78) /**< \brief Chip ID (CHIPID) */

#define ID_PERIPH_COUNT (79) /**< \brief Number of peripheral IDs */

/*@}*/

/* ************************************************************************** */
/*   SLAVE MATRIX ID DEFINITIONS FOR SAMA5D2x */
/* ************************************************************************** */
/** \addtogroup SAMA5D2x_matrix Matrix Ids Definitions */
/*@{*/

#define H64MX_SLAVE_BRIDGE_H32MX    0    /**< Bridge from H64MX to H32MX */
#define H64MX_SLAVE_APB             1    /**< H64MX APB - User interfaces */
#define H64MX_SLAVE_SDMMC           1    /**< SDMMC0 - SDMMC1 */
#define H64MX_SLAVE_DDR_PORT0       2    /**< DDR Port 0 */
#define H64MX_SLAVE_DDR_PORT1       3    /**< DDR Port 1 */
#define H64MX_SLAVE_DDR_PORT2       4    /**< DDR Port 2 */
#define H64MX_SLAVE_DDR_PORT3       5    /**< DDR Port 3 */
#define H64MX_SLAVE_DDR_PORT4       6    /**< DDR Port 4 */
#define H64MX_SLAVE_DDR_PORT5       7    /**< DDR Port 5 */
#define H64MX_SLAVE_DDR_PORT6       8    /**< DDR Port 6 */
#define H64MX_SLAVE_DDR_PORT7       9    /**< DDR Port 7 */
#define H64MX_SLAVE_SRAM           10    /**< Internal SRAM 128K */
#define H64MX_SLAVE_L2C_SRAM       11    /**< Internal SRAM 128K (L2) */
#define H64MX_SLAVE_QSPI0          12    /**< QSPI0 */
#define H64MX_SLAVE_QSPI1          13    /**< QSPI1 */
#define H64MX_SLAVE_AESB           14    /**< AESB */

#define H32MX_SLAVE_BRIDGE_H64MX    0    /**< Bridge from H32MX to H64MX */
#define H32MX_SLAVE_APB0            1    /**< H32MX APB0 - User interfaces */
#define H32MX_SLAVE_APB1            2    /**< H32MX APB1 - User interfaces */
#define H32MX_SLAVE_EBI             3    /**< External Bus Interface CS0..CS3 */
#define H32MX_SLAVE_NFC_CMD         3    /**< NFC Command Register */
#define H32MX_SLAVE_NFC_SRAM        4    /**< NFC SRAM */
#define H32MX_SLAVE_USB             5    /**< USB */

/*@}*/

/* ************************************************************************** */
/*   PMECC DEFINITIONS FOR SAMA5D2x */
/* ************************************************************************** */
/** \addtogroup SAMA5D2x_pmecc PMECC Definitions */
/*@{*/

/** defines the maximum value of the error correcting capability */
#define PMECC_NB_ERROR_MAX (25)

/** Address of Galois Field Table 512 mapping in ROM. */
#define GALOIS_TABLE_512_ROM_MAPPING (0x40000)

/** Address of Galois Field Table 1024 mapping in ROM. */
#define GALOIS_TABLE_1024_ROM_MAPPING (0x48000)

/*@}*/

/* ************************************************************************** */
/* INCLUDE FOR SAMA5D2x */
/* ************************************************************************** */

#if defined(CONFIG_SOC_SAMA5D21)
  #include "sama5d21.h"
#elif defined(CONFIG_SOC_SAMA5D22)
  #include "sama5d22.h"
#elif defined(CONFIG_SOC_SAMA5D23)
  #include "sama5d23.h"
#elif defined(CONFIG_SOC_SAMA5D24)
  #include "sama5d24.h"
#elif defined(CONFIG_SOC_SAMA5D26)
  #include "sama5d26.h"
#elif defined(CONFIG_SOC_SAMA5D27)
  #include "sama5d27.h"
#elif defined(CONFIG_SOC_SAMA5D28)
  #include "sama5d28.h"
#else
  #error Library does not support the specified device.
#endif

#include "chip_pins.h"

/** Size of Cortex-A5 L1 cache line */
#define L1_CACHE_WORDS (8u)
#define L1_CACHE_BYTES (32u)

/** FLEXCOM USART FIFO depth */
#define FLEXCOM_USART_FIFO_DEPTH (32u)

/** FLEXCOM SPI FIFO depth */
#define FLEXCOM_SPI_FIFO_DEPTH (32u)

/** SPI FIFO depth */
#define SPI_FIFO_DEPTH (16u)

/** TWI FIFO depth */
#define TWI_FIFO_DEPTH (16u)

/** Frequency of the on-chip slow clock oscillator */
#define SLOW_CLOCK_INT_OSC 32000

/** Frequency of the on-chip main clock oscillator */
#define MAIN_CLOCK_INT_OSC 12000000

/** AIC redirection unlock key */
#define AICREDIR_KEY 0x5B6C0E26u

/** Indicates chip has an UDP High Speed. */
#define CHIP_USB_UDPHS

/** Indicates chip has an internal pull-up. */
#define CHIP_USB_PULLUP_INTERNAL

/** Number of USB endpoints */
#define CHIP_USB_ENDPOINTS 16

/** Endpoints max paxcket size */
#define CHIP_USB_ENDPOINT_MAXPACKETSIZE(ep) \
   ((ep == 0) ? 64 : 1024)

/** Endpoints Number of Bank */
#define CHIP_USB_ENDPOINT_BANKS(ep) \
   ((ep == 0) ? 1 : ((ep == 1) ? 3 : ((ep == 2) ? 3 : 2)))

/** Endpoints DMA support */
#define CHIP_USB_ENDPOINT_HAS_DMA(ep) \
    ((ep == 0) ? false : ((ep < 7) ? true : false ))

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \brief retrieve Flexcom base address from its ID
 * \return Flexcom base address on success, 0 otherwise
 */
extern Flexcom* get_flexcom_addr_from_id(const uint32_t id);

/**
 * \brief retrieve TWI ID from its base address
 * \return TWI ID on success, ID_PERIPH_COUNT otherwise
 */
extern uint32_t get_twi_id_from_addr(const Twi* addr);

/**
 * \brief retrieve TWI base address from its ID
 * \return TWI base address on success, 0 otherwise
 */
extern Twi* get_twi_addr_from_id(const uint32_t id);

/**
 *
 */
extern uint32_t get_spi_id_from_addr(const Spi* addr);

extern Spi* get_spi_addr_from_id(const uint32_t id);

extern uint32_t get_uart_id_from_addr(const Uart* addr);

extern uint32_t get_usart_id_from_addr(const Usart* addr);

/**
 * \brief retrieve Timer/Counter ID from its base address
 * \return TC ID on success, ID_PERIPH_COUNT otherwise
 */
extern uint32_t get_tc_id_from_addr(const Tc* addr);

/**
 * \brief retrieve Timer/Counter base address from its ID
 * \return TC base address on success, 0 otherwise
 */
extern Tc* get_tc_addr_from_id(const uint32_t id);

/**
 * \brief retrieve QSPI ID from its base address
 * \return QSPI ID on success, ID_PERIPH_COUNT otherwise
 */
uint32_t get_qspi_id_from_addr(const Qspi* addr);

/**
 * \brief retrieve QSPI memory start from its base address
 * \return QSPI memory start on success, NULL otherwise
 */
void *get_qspi_mem_from_addr(const Qspi* addr);

/**
 * \brief retrieve GMAC ID from its base address
 * \return GMAC ID on success, ID_PERIPH_COUNT otherwise
 */
uint32_t get_gmac_id_from_addr(const Gmac* addr);

/** \brief Returns the matrix on which the given peripheral is connected
 *
 * \param id the Peripheral ID
 * \return a pointer to the Matrix instance
 */
extern Matrix* get_peripheral_matrix(uint32_t id);

/** \brief Returns the clock divider for the given peripheral
 *
 * \param id the Peripheral ID
 * \return the clock divider for the peripheral
 */
extern uint32_t get_peripheral_clock_divider(uint32_t id);

/** \brief Returns the XDMAC interface number for a given peripheral
 *
 * \param id the Peripheral ID
 * \param xdmac the XDMAC controller instance
 * \param transmit a boolean, true for transmit, false for receive
 * \return the XDMAC interface number or 0xff if none
 */
extern uint8_t get_peripheral_xdma_channel(uint32_t id, Xdmac *xdmac,
					   bool transmit);

/** \brief Checks if a peripheral is usable with a XDMAC controller
 *
 * \param id the Peripheral ID
 * \param xdmac the XDMAC controller instance
 * \return true if the peripheral is usable on the given XDMAC controller,
 * false otherwise
 */
extern bool is_peripheral_on_xdma_controller(uint32_t id, Xdmac *xdmac);

/** \brief Retrive peripheral FIFO size from its base address
 *
 * \param addr the Peripheral base addr
 * \return Size in number of data of the peripherals FIFO if
 * available, negative value otherwise.
 */
extern int32_t get_peripheral_fifo_depth(void* addr);

#ifdef __cplusplus
}
#endif

#endif /* _CHIP_H_ */
