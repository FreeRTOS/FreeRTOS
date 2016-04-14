/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "compiler.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

struct peripheral_xdma {
	uint32_t id;   /**< Peripheral ID */
	uint8_t  iftx; /**< DMA Interface for TX */
	uint8_t  ifrx; /**< DMA Interface for RX */
};

/*----------------------------------------------------------------------------
 *        Local constants
 *----------------------------------------------------------------------------*/

static uint8_t _h64_peripherals[] = {
	ID_ARM_PMU, /*  2: Performance Monitor Unit (PMU) (ARM_PMU) */
	ID_XDMAC0,  /*  6: DMA Controller 0 (XDMAC0) */
	ID_XDMAC1,  /*  7: DMA Controller 1 (XDMAC1) */
	ID_AES,     /*  9: Advanced Enion Standard (AES) */
	ID_AESB,    /* 10: AES bridge (AESB) */
	ID_SHA,     /* 12: SHA Signature (SHA) */
	ID_MPDDRC,  /* 13: MPDDR controller (MPDDRC) */
	ID_MATRIX0, /* 15: H64MX, 64-bit AHB Matrix (MATRIX0) */
	ID_SDMMC0,  /* 31: Secure Digital Multimedia Card Controller 0 (SDMMC0) */
	ID_SDMMC1,  /* 32: Secure Digital Multimedia Card Controller 1 (SDMMC1) */
	ID_LCDC,    /* 45: LCD Controller (LCDC) */
	ID_ISC,     /* 46: Camera Interface (ISC) */
	ID_QSPI0,   /* 52: QSPI 0 (QSPI0) */
	ID_QSPI1,   /* 53: QSPI 1 (QSPI1) */
	ID_L2CC,    /* 63: L2 Cache Controller (L2CC) */
};

static const struct peripheral_xdma _xdmac_peripherals[] = {
	{ ID_TWIHS0,      0,    1 },
	{ ID_TWIHS1,      2,    3 },
	{ ID_QSPI0,       4,    5 },
	{ ID_SPI0,        6,    7 },
	{ ID_SPI1,        8,    9 },
	{ ID_PWM,        10, 0xff },
	{ ID_FLEXCOM0,   11,   12 },
	{ ID_FLEXCOM1,   13,   14 },
	{ ID_FLEXCOM2,   15,   16 },
	{ ID_FLEXCOM3,   17,   18 },
	{ ID_FLEXCOM4,   19,   20 },
	{ ID_SSC0,       21,   22 },
	{ ID_SSC1,       23,   24 },
	{ ID_ADC,      0xff,   25 },
	{ ID_AES,        26,   27 },
	{ ID_TDES,       28,   29 },
	{ ID_SHA,        30, 0xff },
	{ ID_I2SC0,      31,   32 },
	{ ID_I2SC1,      33,   34 },
	{ ID_UART0,      35,   36 },
	{ ID_UART1,      37,   38 },
	{ ID_UART2,      39,   40 },
	{ ID_UART3,      41,   42 },
	{ ID_UART4,      43,   44 },
	{ ID_TC0,      0xff,   45 },
	{ ID_TC1,      0xff,   46 },
	{ ID_CLASSD,     47, 0xff },
	{ ID_QSPI0,      48,   49 },
	{ ID_PDMIC,    0xff,   50 },
};

/*----------------------------------------------------------------------------
 *        Private functions
 *----------------------------------------------------------------------------*/

static const struct peripheral_xdma *get_peripheral_xdma(uint32_t id, Xdmac *xdmac)
{
	unsigned int i;

	if (xdmac != XDMAC0 && xdmac != XDMAC1) {
		return NULL;
	}

	for (i = 0; i < ARRAY_SIZE(_xdmac_peripherals); i++) {
		if (_xdmac_peripherals[i].id == id) {
			return &_xdmac_peripherals[i];
		}
	}

	return NULL;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

Flexcom* get_flexcom_addr_from_id(const uint32_t id)
{
	if (id == ID_FLEXCOM0) return FLEXCOM0; /**< \brief FLEXCOM 0 (FLEXCOM0) */
#ifdef FLEXCOM1
	else if (id == ID_FLEXCOM1) return FLEXCOM1; /**< \brief FLEXCOM 1 (FLEXCOM1) */
#endif
#ifdef FLEXCOM2
	else if (id == ID_FLEXCOM2) return FLEXCOM2; /**< \brief FLEXCOM 2 (FLEXCOM2) */
#endif
#ifdef FLEXCOM3
	else if (id == ID_FLEXCOM3) return FLEXCOM3; /**< \brief FLEXCOM 3 (FLEXCOM3) */
#endif
#ifdef FLEXCOM4
	else if (id == ID_FLEXCOM4) return FLEXCOM4; /**< \brief FLEXCOM 4 (FLEXCOM4) */
#endif
	else return (void*)0;
}

uint32_t get_twi_id_from_addr(const Twi* addr)
{
	if (addr == (void*)TWI0) return ID_FLEXCOM0; /**< \brief FLEXCOM 0 (FLEXCOM0) */
#ifdef TWI1
	else if (addr == (void*)TWI1) return ID_FLEXCOM1; /**< \brief FLEXCOM 1 (FLEXCOM1) */
#endif
#ifdef TWI2
	else if (addr == (void*)TWI2) return ID_FLEXCOM2; /**< \brief FLEXCOM 2 (FLEXCOM2) */
#endif
#ifdef TWI3
	else if (addr == (void*)TWI3) return ID_FLEXCOM3; /**< \brief FLEXCOM 3 (FLEXCOM3) */
#endif
#ifdef TWI4
	else if (addr == (void*)TWI4) return ID_FLEXCOM4; /**< \brief FLEXCOM 4 (FLEXCOM4) */
#endif
#ifdef TWIHS0
	else if (addr == (void*)TWIHS0) return ID_TWIHS0; /**< \brief TWIHS0 */
#endif
#ifdef TWIHS0
	else if (addr == (void*)TWIHS1) return ID_TWIHS1; /**< \brief TWIHS1 */
#endif
	else return ID_PERIPH_COUNT;
}

Twi* get_twi_addr_from_id(const uint32_t id)
{
	if (id == ID_FLEXCOM0) return TWI0; /**< \brief FLEXCOM 0 (FLEXCOM0) */
#ifdef TWI1
	else if (id == ID_FLEXCOM1) return TWI1; /**< \brief FLEXCOM 1 (FLEXCOM1) */
#endif
#ifdef TWI2
	else if (id == ID_FLEXCOM2) return TWI2; /**< \brief FLEXCOM 2 (FLEXCOM2) */
#endif
#ifdef TWI3
	else if (id == ID_FLEXCOM3) return TWI3; /**< \brief FLEXCOM 3 (FLEXCOM3) */
#endif
#ifdef TWI4
	else if (id == ID_FLEXCOM4) return TWI4; /**< \brief FLEXCOM 4 (FLEXCOM4) */
#endif
#ifdef TWIHS0
	else if (id == ID_TWIHS0) return (Twi*)TWIHS0; /**< \brief TWIHS0 */
#endif
#ifdef TWIHS1
	else if (id == ID_TWIHS1) return (Twi*)TWIHS1; /**< \brief TWIHS1 */
#endif
	else return (void*)0;
}

uint32_t get_spi_id_from_addr(const Spi* addr)
{
	if (addr == (void*)SPI0) return ID_SPI0;
#ifdef SPI1
	else if (addr == (void*)SPI1) return ID_SPI1;
#endif
#ifdef FCOMSPI0
	else if (addr == (void*)FCOMSPI0) return ID_FCOMSPI0;
#endif
#ifdef FCOMSPI1
	else if (addr == (void*)FCOMSPI1) return ID_FCOMSPI1;
#endif
#ifdef FCOMSPI2
	else if (addr == (void*)FCOMSPI2) return ID_FCOMSPI2;
#endif
#ifdef FCOMSPI3
	else if (addr == (void*)FCOMSPI3) return ID_FCOMSPI3;
#endif
#ifdef FCOMSPI4
	else if (addr == (void*)FCOMSPI4) return ID_FCOMSPI4;
#endif
	else return ID_PERIPH_COUNT;
}

Spi* get_spi_addr_from_id(const uint32_t id)
{
	if (id == ID_SPI0) return SPI0; /**< \brief SPI 0 (SPI0) */
#ifdef SPI1
	else if (id == ID_SPI1) return SPI1; /**< \brief SPI 1 (SPI1) */
#endif
#ifdef  FCOMSPI0
	else if (id == ID_FCOMSPI0) return FCOMSPI0; /**< \brief FLEXCOM SPI 0 (FCOMSPI0) */
#endif
#ifdef  FCOMSPI1
	else if (id == ID_FCOMSPI1) return FCOMSPI1; /**< \brief FLEXCOM SPI 1 (FCOMSPI1) */
#endif
#ifdef  FCOMSPI2
	else if (id == ID_FCOMSPI2) return FCOMSPI2; /**< \brief FLEXCOM SPI 1 (FCOMSPI1) */
#endif
#ifdef  FCOMSPI3
	else if (id == ID_FCOMSPI3) return FCOMSPI3; /**< \brief FLEXCOM SPI 3 (FCOMSPI3) */
#endif
#ifdef  FCOMSPI4
	else if (id == ID_FCOMSPI4) return FCOMSPI4; /**< \brief FLEXCOM SPI 4 (FCOMSPI4) */
#endif
	else return (void*)0;
}

uint32_t get_uart_id_from_addr(const Uart* addr)
{
	if (addr == (void*)UART0) return ID_UART0;
#ifdef UART1
	else if (addr == (void*)UART1) return ID_UART1;
#endif
#ifdef UART2
	else if (addr == (void*)UART2) return ID_UART2;
#endif
#ifdef UART3
	else if (addr == (void*)UART3) return ID_UART3;
#endif
#ifdef UART4
	else if (addr == (void*)UART4) return ID_UART4;
#endif
	else return ID_PERIPH_COUNT;
}

uint32_t get_usart_id_from_addr(const Usart* addr)
{
	if (addr == (void*)USART0) return ID_USART0;
#ifdef USART1
	else if (addr == (void*)USART1) return ID_USART1;
#endif
#ifdef USART2
	else if (addr == (void*)USART2) return ID_USART2;
#endif
#ifdef USART3
	else if (addr == (void*)USART3) return ID_USART3;
#endif
#ifdef USART4
	else if (addr == (void*)USART4) return ID_USART4;
#endif
	else return ID_PERIPH_COUNT;
}

uint32_t get_tc_id_from_addr(const Tc* addr)
{
	if (addr == TC0) return ID_TC0;
#ifdef TC1
	else if (addr == TC1) return ID_TC1;
#endif
	else return ID_PERIPH_COUNT;
}

Tc* get_tc_addr_from_id(const uint32_t id)
{
	if (id == ID_TC0) return TC0; /**< \brief Timer/Counter 0 (TC0) */
#ifdef TC1
	else if (id == ID_TC1) return TC1; /**< \brief Timer/Counter 1 (TC1) */
#endif
	else return (void*)0;
}

uint32_t get_qspi_id_from_addr(const Qspi* addr)
{
	if (addr == (void*)QSPI0) return ID_QSPI0;
	else if (addr == (void*)QSPI1) return ID_QSPI1;
	else return ID_PERIPH_COUNT;
}

void *get_qspi_mem_from_addr(const Qspi* addr)
{
	if (addr == (void*)QSPI0) return (void*)QSPIMEM0_ADDR;
	else if (addr == (void*)QSPI1) return (void*)QSPIMEM1_ADDR;
	else return NULL;
}

uint32_t get_gmac_id_from_addr(const Gmac* addr)
{
	if (addr == (void*)GMAC0) return ID_GMAC0;
	else return ID_PERIPH_COUNT;
}

Matrix* get_peripheral_matrix(uint32_t id)
{
	unsigned int i;

	for (i = 0; i < ARRAY_SIZE(_h64_peripherals); i++)
		if (_h64_peripherals[i] == id)
			return MATRIX0; // AHB 64-bit matrix
	return MATRIX1; // AHB 32-bit matrix
}

uint32_t get_peripheral_clock_divider(uint32_t id)
{
	Matrix* matrix = get_peripheral_matrix(id);

	if (matrix == MATRIX1) {
		if (PMC->PMC_MCKR & PMC_MCKR_H32MXDIV_H32MXDIV2)
			return 2;
		else
			return 1;
	}

	return 1;
}

uint8_t get_peripheral_xdma_channel(uint32_t id, Xdmac *xdmac, bool transmit)
{
	const struct peripheral_xdma *periph_xdma = get_peripheral_xdma(id, xdmac);
	if (periph_xdma) {
		return transmit ? periph_xdma->iftx : periph_xdma->ifrx;
	} else {
		return 0xff;
	}
}

bool is_peripheral_on_xdma_controller(uint32_t id, Xdmac *xdmac)
{
	return get_peripheral_xdma(id, xdmac) != NULL;
}

int32_t get_peripheral_fifo_depth(void* addr)
{
	uint32_t size = (uint32_t)-1;
	uint32_t tmp = (uint32_t)addr;
	switch (tmp) {
	case (uint32_t)USART0:
#ifdef USART1
	case (uint32_t)USART1:
#endif
#ifdef USART2
	case (uint32_t)USART2:
#endif
	case (uint32_t)USART3:
#ifdef USART3
	case (uint32_t)USART4:
#endif
		size = FLEXCOM_USART_FIFO_DEPTH;
		break;

	case (uint32_t)FCOMSPI0:
#ifdef FCOMSPI1
	case (uint32_t)FCOMSPI1:
#endif
#ifdef FCOMSPI2
	case (uint32_t)FCOMSPI2:
#endif
#ifdef FCOMSPI3
	case (uint32_t)FCOMSPI3:
#endif
#ifdef FCOMSPI4
	case (uint32_t)FCOMSPI4:
#endif
		size = FLEXCOM_SPI_FIFO_DEPTH;
		break;
	case (uint32_t)SPI0:
#ifdef SPI1
	case (uint32_t)SPI1:
#endif
		size = SPI_FIFO_DEPTH;
		break;
	case (uint32_t)TWI0:
#ifdef TWI1
	case (uint32_t)TWI1:
#endif
#ifdef TWI2
	case (uint32_t)TWI2:
#endif
#ifdef TWI3
	case (uint32_t)TWI3:
#endif
#ifdef TWI4
	case (uint32_t)TWI4:
#endif
#ifdef TWIHS0
	case (uint32_t)TWIHS0:
#endif
#ifdef TWIHS1
	case (uint32_t)TWIHS1:
#endif
		size = TWI_FIFO_DEPTH;
		break;
	default:
		size = (uint32_t)-1;
	}
	return size;
}
