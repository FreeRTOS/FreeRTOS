/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation

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
 */

#include "chip.h"

#define MATRIX_AXIMX	1
#define MATRIX_H64MX	2
#define MATRIX_H32MX	3

#define SECURITY_TYPE_AS	1
#define SECURITY_TYPE_NS	2
#define	SECURITY_TYPE_PS	3

struct peri_security {
	unsigned int	peri_id;
	unsigned int	matrix;
	unsigned int	security_type;
};

static const struct peri_security peri_security_array[] = {
	/* SAIC */
	{
		.peri_id = ID_FIQ,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* SYS */
	{
		.peri_id = ID_SYS,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* ARM */
	{
		.peri_id = ID_ARM,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* PIT */
	{
		.peri_id = ID_PIT,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* WDT */
	{
		.peri_id = ID_WDT,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* PIOD */
	{
		.peri_id = ID_PIOD,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* USART0 */
	{
		.peri_id = ID_USART0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* USART1 */
	{
		.peri_id = ID_USART1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* XDMAC0 */
	{
		.peri_id = ID_XDMAC0,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* ICM */
	{
		.peri_id = ID_ICM,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* PKCC */
	{
		.peri_id = ID_PKCC,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_AS,
	},	
	/* AES */
	{
		.peri_id = ID_AES,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* AESB */
	{
		.peri_id = ID_AESB,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* TDES */
	{
		.peri_id = ID_TDES,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* SHA */
	{
		.peri_id = ID_SHA,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* MPDDRC */
	{
		.peri_id = ID_MPDDRC,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* MATRIX1 */
	{
		.peri_id = ID_MATRIX1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* MATRIX0 */
	{
		.peri_id = ID_MATRIX0,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* VDEC */
	{
		.peri_id = ID_VDEC,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* HSMC */
	{
		.peri_id = ID_HSMC,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* PIOA*/
	{
		.peri_id = ID_PIOA,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* PIOB*/
	{
		.peri_id = ID_PIOB,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* PIOC*/
	{
		.peri_id = ID_PIOC,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* PIOE*/
	{
		.peri_id = ID_PIOE,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* UART0 */
	{
		.peri_id = ID_UART0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* UART1 */
	{
		.peri_id = ID_UART1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* USART2 */
	{
		.peri_id = ID_USART2,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* USART3 */
	{
		.peri_id = ID_USART3,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* USART4 */
	{
		.peri_id = ID_USART4,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TWI0 */
	{
		.peri_id = ID_TWI0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TWI1 */
	{
		.peri_id = ID_TWI1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TWI2 */
	{
		.peri_id = ID_TWI2,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* HSMCI0 */
	{
		.peri_id = ID_HSMCI0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* HSMCI1 */
	{
		.peri_id = ID_HSMCI1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* SPI0 */
	{
		.peri_id = ID_SPI0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* SPI1 */
	{
		.peri_id = ID_SPI1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* SPI2 */
	{
		.peri_id = ID_SPI2,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TC0 */
	{
		.peri_id = ID_TC0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TC1 */
	{
		.peri_id = ID_TC1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TC2 */
	{
		.peri_id = ID_TC2,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* PWM */
	{
		.peri_id = ID_PWM,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* ADC */
	{
		.peri_id = ID_ADC,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* DBGU */
	{
		.peri_id = ID_DBGU,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* UHPHS */
	{
		.peri_id = ID_UHPHS,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* UDPHS */
	{
		.peri_id = ID_UDPHS,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* SSC0 */
	{
		.peri_id = ID_SSC0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* SSC1 */
	{
		.peri_id = ID_SSC1,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* XDMAC1 */
	{
		.peri_id = ID_XDMAC1,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_NS,
	},
	/* LCDC */
	{
		.peri_id = ID_LCDC,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* ISI */
	{
		.peri_id = ID_ISI,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TRNG */
	{
		.peri_id = ID_TRNG,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* GMAC */
	{
		.peri_id = ID_GMAC0,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* IRQ */
	{
		.peri_id = ID_IRQ,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_NS,
	},
	/* SFC */
	{
		.peri_id = ID_SFC,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* SECURAM */
	{
		.peri_id = ID_SECURAM,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* SMD */
	{
		.peri_id = ID_SMD,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* TWI3 */
	{
		.peri_id = ID_TWI3,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_PS,
	},
	/* CATB */
	{
		.peri_id = ID_CATB,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* SFR */
	{
		.peri_id = ID_SFR,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* AIC */
	{
		.peri_id = ID_AIC,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_NS,
	},
	/* SAIC */
	{
		.peri_id = ID_SAIC,
		.matrix = MATRIX_H32MX,
		.security_type = SECURITY_TYPE_AS,
	},
	/* L2CC */
	{
		.peri_id = ID_L2CC,
		.matrix = MATRIX_H64MX,
		.security_type = SECURITY_TYPE_AS,
	},
};

void matrix_configure_slave_security(Matrix *matrix_base,
				unsigned int slave,
				unsigned int srtop_setting,
				unsigned int srsplit_setting,
				unsigned int ssr_setting)
{
        matrix_base->MATRIX_SSR[slave] = ssr_setting;
	matrix_base->MATRIX_SRTSR[slave] = srtop_setting;
	matrix_base->MATRIX_SASSR[slave] = srsplit_setting;
}



static struct peri_security *get_peri_security(unsigned int peri_id)
{
	unsigned int i;

	for (i = 0; i < ARRAY_SIZE(peri_security_array); i++) {
		if (peri_id == peri_security_array[i].peri_id)
			break;
	}

	return ((i == ARRAY_SIZE(peri_security_array))) ?
			NULL : (struct peri_security *)&peri_security_array[i];
}

static int matrix_set_peri_security(unsigned int matrix, unsigned peri_id)
{
	Matrix *base;
	uint32_t spselr;
	uint32_t idx;
	uint32_t bit;

	idx = peri_id / 32;
	if (idx > 3)
		return -1;

	bit = (0x01 << (peri_id % 32));
	if (matrix == MATRIX_H32MX)
		base = MATRIX1;
	else if (matrix == MATRIX_H64MX)
		base = MATRIX0;
	else
		return -1;

	spselr = base->MATRIX_SPSELR[idx];
	spselr |= bit;
	base->MATRIX_SPSELR[idx] =  spselr;

	return 0;
}

int matrix_configure_peri_security(unsigned int *peri_id_array,
					unsigned int size)
{
	unsigned int i;
	unsigned int *peri_id_p;
	unsigned int matrix;
	unsigned int peri_id;
	struct peri_security *periperal_sec;
	int ret;

	if ((peri_id_array == NULL) || (size == 0))
		return -1;

	peri_id_p = peri_id_array;
	for (i = 0; i < size; i++) {
		periperal_sec = get_peri_security(*peri_id_p);
		if (periperal_sec == NULL)
			return -1;

		if (periperal_sec->security_type != SECURITY_TYPE_PS)
			return -1;

		matrix = periperal_sec->matrix;
		peri_id = *peri_id_p;
		ret = matrix_set_peri_security(matrix, peri_id);
		if (ret)
			return -1;

		peri_id_p++;
	}

	return 0;
}

/*
 * is_peripheral_secure - tell if the peripheral is in secure mode
 * @periph_id: the peripheral id that is checked
 *
 * Check security of a particular peripheral by providing its ID.
 * Note that a wrong preripheral ID leads to the "true" return code.
 */
int is_peripheral_secure(unsigned int periph_id)
{
	struct peri_security *periperal_sec;
	uint32_t matrix;
	Matrix *base;
	uint32_t mask;
        
	if ((periph_id > ID_FIQ) && (periph_id < ID_PERIPH_COUNT)) {
		/* special cases here */
		if ((periph_id == ID_IRQ)
		 || (periph_id == ID_AIC)
		 || (periph_id == ID_XDMAC1))
			return 0;

		periperal_sec = get_peri_security(periph_id);
		if (periperal_sec == NULL)
			return -1;

		matrix = periperal_sec->matrix;
		if (matrix == MATRIX_H32MX)
			base = MATRIX1;
		else if (matrix == MATRIX_H64MX)
			base = MATRIX0;
		else
			return -1;

		mask = 1 << (periph_id % 32);
		if (base->MATRIX_SPSELR[periph_id / 32] & mask)
			return 0;

	}
	return 1;
}

int is_sys_clk_secure(unsigned int sys_mask)
{
	unsigned int periph_id = sys_mask_to_per_id(sys_mask);

	return is_peripheral_secure(periph_id);
}

int is_usb_hs_secure(void)
{
	return (is_peripheral_secure(ID_UHPHS)
		|| is_peripheral_secure(ID_UDPHS));
}

int is_usb_host_secure(void)
{
	return is_peripheral_secure(ID_UHPHS);
}

int is_switching_clock_forbiden(unsigned int periph_id, unsigned int is_on, unsigned int *silent)
{
	/* disable console clock : forbiden */
	if ((periph_id == ID_USART3) && (is_on == 0)) {
		/* keep it silent */
		*silent = 1;
		return 1;
	} else {
		return 0;
	}
}


static int matrix_configure_slave(void)
{
	unsigned int ddr_port;
	unsigned int ssr_setting, sasplit_setting, srtop_setting;

	/*
	 * Matrix 0 (H64MX)
	 */

	/* 0: Bridge from H64MX to AXIMX */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX0,
					H64MX_SLAVE_BRIDGE_TO_AXIMX,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 1: H64MX Peripheral Bridge: Non-Secure */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX0,
					H64MX_SLAVE_PERI_BRIDGE,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 2: Video Decoder 128K: Non-Secure */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX0,
					H64MX_SLAVE_VIDEO_DECODER,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 4 ~ 10 DDR2 Port1 ~ 7: Non-Secure */
	srtop_setting = MATRIX_SRTOP(0, MATRIX_SRTOP_VALUE_128M);
	sasplit_setting = (MATRIX_SASPLIT(0, MATRIX_SASPLIT_VALUE_128M)
				| MATRIX_SASPLIT(1, MATRIX_SASPLIT_VALUE_128M)
				| MATRIX_SASPLIT(2, MATRIX_SASPLIT_VALUE_128M)
				| MATRIX_SASPLIT(3, MATRIX_SASPLIT_VALUE_128M));
	ssr_setting = (MATRIX_LANSECH_NS(0)
			| MATRIX_LANSECH_NS(1)
			| MATRIX_LANSECH_NS(2)
			| MATRIX_LANSECH_NS(3)
			| MATRIX_RDNSECH_NS(0)
			| MATRIX_RDNSECH_NS(1)
			| MATRIX_RDNSECH_NS(2)
			| MATRIX_RDNSECH_NS(3)
			| MATRIX_WRNSECH_NS(0)
			| MATRIX_WRNSECH_NS(1)
			| MATRIX_WRNSECH_NS(2)
			| MATRIX_WRNSECH_NS(3));
	/* DDR port 0 not used from NWd */
	for (ddr_port = 1; ddr_port < 8; ddr_port++) {
		matrix_configure_slave_security(MATRIX0,
					(H64MX_SLAVE_DDR2_PORT_0 + ddr_port),
					srtop_setting,
					sasplit_setting,
					ssr_setting);
	}

	/* 11: Internal SRAM 128K
	 * TOP0 is set to 128K
	 * SPLIT0 is set to 64K
	 * LANSECH0 is set to 0, the low area of region 0 is the Securable one
	 * RDNSECH0 is set to 0, region 0 Securable area is secured for reads.
	 * WRNSECH0 is set to 0, region 0 Securable area is secured for writes
	 */
	srtop_setting = MATRIX_SRTOP(0, MATRIX_SRTOP_VALUE_128K);
	sasplit_setting = MATRIX_SASPLIT(0, MATRIX_SASPLIT_VALUE_64K);
	ssr_setting = (MATRIX_LANSECH_S(0)
			| MATRIX_RDNSECH_S(0)
			| MATRIX_WRNSECH_S(0));
	matrix_configure_slave_security(MATRIX0,
					H64MX_SLAVE_INTERNAL_SRAM,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 12:  Bridge from H64MX to H32MX: Non-Secure */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX0,
					H64MX_SLAVE_BRIDGE_TO_H32MX,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/*
	 * Matrix 1 (H32MX)
	 */

	/* 0: Bridge from H32MX to H64MX */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX1,
					H32MX_BRIDGE_TO_H64MX,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 1: H32MX Peripheral Bridge 0 */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX1,
					H32MX_PERI_BRIDGE_0,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 2: H32MX Peripheral Bridge 1 */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX1,
					H32MX_PERI_BRIDGE_1,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 3: External Bus Interface: Non-Secure */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX1,
					H32MX_EXTERNAL_EBI,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 4: NFC SRAM (4K): Non-Secure */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX1,
					H32MX_NFC_SRAM,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 5: DPHS RAM(1M), UHP OHCI (1M), UHP EHCI (1M): Non-Secure */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX1,
					H32MX_USB,
					srtop_setting,
					sasplit_setting,
					ssr_setting);

	/* 6: Soft Modem (1M): Non-Secure */
	srtop_setting = 0xffffffff;
	sasplit_setting = 0xffffffff;
	ssr_setting = 0xffffffff;
	matrix_configure_slave_security(MATRIX1,
					H32MX_SMD,
					srtop_setting,
					sasplit_setting,
					ssr_setting);
	return 0;
}

static unsigned int security_ps_peri_id[] = {
	ID_VDEC,
	ID_PIOA,
	ID_PIOB,
	ID_PIOC,
	ID_PIOE,
	ID_USART2,
	ID_USART3,
	ID_USART4,
	ID_TWI0,
	ID_TWI2,
	ID_HSMCI0,
	ID_HSMCI1,
	ID_TC0,
	ID_TC1,
	ID_UHPHS,
	ID_UDPHS,
	ID_LCDC,
	ID_GMAC0,
	ID_SPI0,
	ID_SPI1,
	ID_SMD,
};

static int matrix_config_periheral(void)
{
	unsigned int *peri_id = security_ps_peri_id;
	unsigned int array_size = sizeof(security_ps_peri_id) / sizeof(unsigned int);
	int ret;

	ret = matrix_configure_peri_security(peri_id, array_size);
	if (ret)
		return -1;

	return 0;
}

int matrix_init(void)
{
	int ret;

    /* Disable write protection */
    MATRIX0->MATRIX_WPMR = MATRIX_WPMR_WPKEY(MATRIX_KEY_VAL);
    MATRIX1->MATRIX_WPMR = MATRIX_WPMR_WPKEY(MATRIX_KEY_VAL);

	ret = matrix_configure_slave();
	if (ret)
		return -1;

	ret = matrix_config_periheral();
	if (ret)
		return -1;

	return 0;
}

