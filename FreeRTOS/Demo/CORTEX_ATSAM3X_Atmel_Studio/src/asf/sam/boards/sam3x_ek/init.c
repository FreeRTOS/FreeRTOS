/**
 * \file
 *
 * \brief SAM3X-EK board init.
 *
 * Copyright (c) 2011 - 2012 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#include "compiler.h"
#include "board.h"
#include "conf_board.h"
#include "gpio.h"

void board_init(void)
{
#ifndef CONF_BOARD_KEEP_WATCHDOG_AT_INIT
	/* Disable the watchdog */
	WDT->WDT_MR = WDT_MR_WDDIS;
#endif

	/* Configure Power LED */
	gpio_configure_pin(LED3_GPIO, LED3_FLAGS);
	gpio_set_pin_high(LED3_GPIO); /* Turned on by default */

	/* Configure User LED pins */
	gpio_configure_pin(LED0_GPIO, LED0_FLAGS);
	gpio_configure_pin(LED1_GPIO, LED1_FLAGS);
	gpio_configure_pin(LED2_GPIO, LED2_FLAGS);

	/* Configure Push Button pins */
	gpio_configure_pin(GPIO_PUSH_BUTTON_1, GPIO_PUSH_BUTTON_1_FLAGS);
	gpio_configure_pin(GPIO_PUSH_BUTTON_2, GPIO_PUSH_BUTTON_2_FLAGS);

#ifdef CONF_BOARD_UART_CONSOLE
	/* Configure UART pins */
	gpio_configure_group(PINS_UART_PIO, PINS_UART, PINS_UART_FLAGS);
#endif

	/* Configure ADC example pins */
#ifdef CONF_BOARD_ADC
	/* TC TIOA configuration */
	gpio_configure_pin(PIN_TC0_TIOA0,PIN_TC0_TIOA0_FLAGS);

	/* ADC Trigger configuration */
	gpio_configure_pin(PINS_ADC_TRIG, PINS_ADC_TRIG_FLAG);

	/* PWMH0 configuration */
	gpio_configure_pin(PIN_PWMC_PWMH0_TRIG, PIN_PWMC_PWMH0_TRIG_FLAG);
#endif

#ifdef CONF_BOARD_PWM_LED0
	/* Configure PWM LED0 pin */
	gpio_configure_pin(PIN_PWM_LED0_GPIO, PIN_PWM_LED0_FLAGS);
#endif

#ifdef CONF_BOARD_PWM_LED1
	/* Configure PWM LED1 pin */
	gpio_configure_pin(PIN_PWM_LED1_GPIO, PIN_PWM_LED1_FLAGS);
#endif

#ifdef CONF_BOARD_PWM_LED2
	/* Configure PWM LED2 pin */
	gpio_configure_pin(PIN_PWM_LED2_GPIO, PIN_PWM_LED2_FLAGS);
#endif

	/* Configure SPI0 pins */
#ifdef CONF_BOARD_SPI0
	gpio_configure_pin(SPI0_MISO_GPIO, SPI0_MISO_FLAGS);
	gpio_configure_pin(SPI0_MOSI_GPIO, SPI0_MOSI_FLAGS);
	gpio_configure_pin(SPI0_SPCK_GPIO, SPI0_SPCK_FLAGS);

	/**
	 * For NPCS 1, 2, and 3, different PINs can be used to access the same
	 * NPCS line.
	 * Depending on the application requirements, the default PIN may not be
	 * available.
	 * Hence a different PIN should be selected using the
	 * CONF_BOARD_SPI_NPCS_GPIO and
	 * CONF_BOARD_SPI_NPCS_FLAGS macros.
	 */

#   ifdef CONF_BOARD_SPI0_NPCS0
		gpio_configure_pin(SPI0_NPCS0_GPIO, SPI0_NPCS0_FLAGS);
#   endif

#   ifdef CONF_BOARD_SPI0_NPCS1
#       if defined(CONF_BOARD_SPI0_NPCS1_GPIO) && \
		defined(CONF_BOARD_SPI0_NPCS1_FLAGS)
			gpio_configure_pin(CONF_BOARD_SPI0_NPCS1_GPIO,
					CONF_BOARD_SPI0_NPCS1_FLAGS);
#       else
			gpio_configure_pin(SPI0_NPCS1_PA29_GPIO,
					SPI0_NPCS1_PA29_FLAGS);
#       endif
#   endif

#   ifdef CONF_BOARD_SPI0_NPCS2
#       if defined(CONF_BOARD_SPI0_NPCS2_GPIO) && \
		defined(CONF_BOARD_SPI0_NPCS2_FLAGS)
			gpio_configure_pin(CONF_BOARD_SPI0_NPCS2_GPIO,
					CONF_BOARD_SPI0_NPCS2_FLAGS);
#       else
			gpio_configure_pin(SPI0_NPCS2_PA30_GPIO,
					SPI0_NPCS2_PA30_FLAGS);
#       endif
#   endif

#   ifdef CONF_BOARD_SPI0_NPCS3
#       if defined(CONF_BOARD_SPI0_NPCS3_GPIO) && \
		defined(CONF_BOARD_SPI0_NPCS3_FLAGS)
			gpio_configure_pin(CONF_BOARD_SPI0_NPCS3_GPIO,
					CONF_BOARD_SPI0_NPCS3_FLAGS);
#       else
			gpio_configure_pin(SPI0_NPCS3_PA31_GPIO,
					SPI0_NPCS3_PA31_FLAGS);
#       endif
#   endif
#endif // #ifdef CONF_BOARD_SPI0

	/* Configure SPI1 pins */
#ifdef CONF_BOARD_SPI1
	gpio_configure_pin(SPI1_MISO_GPIO, SPI1_MISO_FLAGS);
	gpio_configure_pin(SPI1_MOSI_GPIO, SPI1_MOSI_FLAGS);
	gpio_configure_pin(SPI1_SPCK_GPIO, SPI1_SPCK_FLAGS);

#   ifdef CONF_BOARD_SPI1_NPCS0
		gpio_configure_pin(SPI1_NPCS0_GPIO, SPI1_NPCS0_FLAGS);
#   endif

#   ifdef CONF_BOARD_SPI1_NPCS1
		gpio_configure_pin(SPI1_NPCS1_GPIO, SPI1_NPCS1_FLAGS);
#   endif

#   ifdef CONF_BOARD_SPI1_NPCS2
		gpio_configure_pin(SPI1_NPCS2_GPIO, SPI1_NPCS2_FLAGS);
#   endif

#   ifdef CONF_BOARD_SPI1_NPCS3
		gpio_configure_pin(SPI1_NPCS3_GPIO, SPI1_NPCS3_FLAGS);
#   endif
#endif

#ifdef CONF_BOARD_TWI0
	gpio_configure_pin(TWI0_DATA_GPIO, TWI0_DATA_FLAGS);
	gpio_configure_pin(TWI0_CLK_GPIO, TWI0_CLK_FLAGS);
#endif

#ifdef CONF_BOARD_TWI1
	gpio_configure_pin(TWI1_DATA_GPIO, TWI1_DATA_FLAGS);
	gpio_configure_pin(TWI1_CLK_GPIO, TWI1_CLK_FLAGS);
#endif

#ifdef CONF_BOARD_USART_RXD
	/* Configure USART RXD pin */
	gpio_configure_pin(PIN_USART0_RXD_IDX, PIN_USART0_RXD_FLAGS);
#endif

#ifdef CONF_BOARD_USART_TXD
	/* Configure USART TXD pin */
	gpio_configure_pin(PIN_USART0_TXD_IDX, PIN_USART0_TXD_FLAGS);
#endif

#ifdef CONF_BOARD_USART_CTS
	/* Configure USART CTS pin */
	gpio_configure_pin(PIN_USART0_CTS_IDX, PIN_USART0_CTS_FLAGS);
#endif

#ifdef CONF_BOARD_USART_RTS
	/* Configure USART RTS pin */
	gpio_configure_pin(PIN_USART0_RTS_IDX, PIN_USART0_RTS_FLAGS);
#endif

#ifdef CONF_BOARD_USART_SCK
	/* Configure USART synchronous communication SCK pin */
	gpio_configure_pin(PIN_USART0_SCK_IDX, PIN_USART0_SCK_FLAGS);
#endif

#ifdef CONF_BOARD_ADM3312_EN
	/* Configure ADM3312 enable pin */
	gpio_configure_pin(PIN_USART0_EN_IDX, PIN_USART0_EN_FLAGS);
	gpio_set_pin_low(PIN_USART0_EN_IDX);
#endif

#ifdef CONF_BOARD_TFDU4300_SD
	/* Configure IrDA transceiver shutdown pin */
	gpio_configure_pin(PIN_IRDA_SD_IDX, PIN_IRDA_SD_FLAGS);
	gpio_set_pin_low(PIN_IRDA_SD_IDX);
#endif

#ifdef CONF_BOARD_ADM3485_RE
	/* Configure RS485 transceiver ADM3485 RE pin */
	gpio_configure_pin(PIN_RE_IDX, PIN_RE_FLAGS);
	gpio_set_pin_low(PIN_RE_IDX);
#endif

#ifdef CONF_BOARD_SMC_PSRAM
	gpio_configure_pin(PIN_EBI_DATA_BUS_D0, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D1, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D2, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D3, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D4, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D5, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D6, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D7, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D8, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D9, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D10, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D11, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D12, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D13, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D14, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D15, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_NRD, PIN_EBI_NRD_FLAGS);
	gpio_configure_pin(PIN_EBI_NWE, PIN_EBI_NWE_FLAGS);
	gpio_configure_pin(PIN_EBI_NCS0, PIN_EBI_NCS0_FLAGS);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_NBS0, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_NBS1, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A1, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A2, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A3, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A4, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A5, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A6, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A7, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A8, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A9, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A10, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A11, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A12, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A13, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A14, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A15, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A16, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A17, PIN_EBI_ADDR_BUS_FLAG1);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A18, PIN_EBI_ADDR_BUS_FLAG2);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A19, PIN_EBI_ADDR_BUS_FLAG2);
	gpio_configure_pin(PIN_EBI_ADDR_BUS_A20, PIN_EBI_ADDR_BUS_FLAG2);
#endif // #ifdef CONF_BOARD_SMC_PSRAM

#ifdef CONF_BOARD_HX8347A
	/* Configure LCD EBI pins */
	gpio_configure_pin(PIN_EBI_DATA_BUS_D0, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D1, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D2, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D3, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D4, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D5, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D6, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D7, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D8, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D9, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D10, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D11, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D12, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D13, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D14, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_DATA_BUS_D15, PIN_EBI_DATA_BUS_FLAGS);
	gpio_configure_pin(PIN_EBI_NRD, PIN_EBI_NRD_FLAGS);
	gpio_configure_pin(PIN_EBI_NWE, PIN_EBI_NWE_FLAGS);
	gpio_configure_pin(PIN_EBI_NCS2, PIN_EBI_NCS2_FLAGS);
	gpio_configure_pin(PIN_EBI_LCD_RS, PIN_EBI_LCD_RS_FLAGS);
#endif // #ifdef CONF_BOARD_HX8347A

#ifdef CONF_BOARD_AAT3194
	/* Configure Backlight control pin */
	gpio_configure_pin(BOARD_BACKLIGHT, BOARD_BACKLIGHT_FLAG);
#endif

#ifdef CONF_BOARD_USB_PORT
	/* Configure USB_ID (UOTGID) pin */
	gpio_configure_pin(USB_ID_GPIO, USB_ID_FLAGS);
	/* Configure USB_VBOF (UOTGVBOF) pin */
	gpio_configure_pin(USB_VBOF_GPIO, USB_VBOF_FLAGS);
	/* Configure FAULT detect pin */
	gpio_configure_pin(USB_OVERCURRENT_DETECT_GPIO,
			USB_OVERCURRENT_DETECT_FLAGS);
#endif

#ifdef CONF_BOARD_MMA7341L
	/* Configure MMA7341L mode set control pin */
	gpio_configure_pin(PIN_MMA7341L_MODE, PIN_MMA7341L_MODE_FLAG);
	/* Configure MMA7341L x,y,z axis output voltage pin */
	gpio_configure_pin(PIN_MMA7341L_X_AXIS, PIN_MMA7341L_X_AXIS_FLAG);
	gpio_configure_pin(PIN_MMA7341L_Y_AXIS, PIN_MMA7341L_Y_AXIS_FLAG);
	gpio_configure_pin(PIN_MMA7341L_Z_AXIS, PIN_MMA7341L_Z_AXIS_FLAG);
#endif

#ifdef CONF_BOARD_ISO7816_RST
	/* Configure ISO7816 card reset pin */
	gpio_configure_pin(PIN_ISO7816_RST_IDX, PIN_ISO7816_RST_FLAG);
#endif

#ifdef CONF_BOARD_ISO7816
	/* Configure ISO7816 interface TXD & SCK pin */
	gpio_configure_pin(PIN_USART0_TXD_IDX, PIN_USART0_TXD_FLAGS);
	gpio_configure_pin(PIN_USART0_SCK_IDX, PIN_USART0_SCK_FLAGS);
#endif

#ifdef CONF_BOARD_CAN0
	/* Configure the CAN0 TX and RX pins. */
	gpio_configure_pin(PIN_CAN0_RX_IDX, PIN_CAN0_RX_FLAGS);
	gpio_configure_pin(PIN_CAN0_TX_IDX, PIN_CAN0_TX_FLAGS);
	/* Configure the transiver0 RS & EN pins. */
	gpio_configure_pin(PIN_CAN0_TR_RS_IDX, PIN_CAN0_TR_RS_FLAGS);
	gpio_configure_pin(PIN_CAN0_TR_EN_IDX, PIN_CAN0_TR_EN_FLAGS);
#endif

#ifdef CONF_BOARD_CAN1
	/* Configure the CAN1 TX and RX pin. */
	gpio_configure_pin(PIN_CAN1_RX_IDX, PIN_CAN1_RX_FLAGS);
	gpio_configure_pin(PIN_CAN1_TX_IDX, PIN_CAN1_TX_FLAGS);
	/* Configure the transiver1 RS & EN pins. */
	gpio_configure_pin(PIN_CAN1_TR_RS_IDX, PIN_CAN1_TR_RS_FLAGS);
	gpio_configure_pin(PIN_CAN1_TR_EN_IDX, PIN_CAN1_TR_EN_FLAGS);
#endif

#ifdef CONF_BOARD_SDRAMC
	gpio_configure_pin(PIN_SDRAM_SDCKE, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDCS, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_RAS, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_CAS, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_BA0, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_BA1, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDWE, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_NBS0, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_NBS1, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA0, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA1, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA2, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA3, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA4, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA5, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA6, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA7, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA8, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA9, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA10, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA11, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA12, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA13, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA14, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_DATA15, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA0, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA1, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA2, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA3, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA4, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA5, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA6, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA7, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA8, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA9, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA10, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA11, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_SDA12, PIN_SDRAM_FLAGS);
	gpio_configure_pin(PIN_SDRAM_EN, PIN_SDRAM_EN_FLAGS);
#endif

#ifdef CONF_BOARD_EMAC
	gpio_configure_pin(PIN_EEMAC_EREFCK, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_ETX0, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_ETX1, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_ETXEN, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_ECRSDV, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_ERX0, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_ERX1, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_ERXER, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_EMDC, PIN_EMAC_FLAGS);
	gpio_configure_pin(PIN_EMAC_EMDIO, PIN_EMAC_FLAGS);
#endif

#ifdef CONF_BOARD_NAND
	gpio_configure_pin(PIN_EBI_NANDOE, PIN_EBI_NANDOE_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDWE, PIN_EBI_NANDWE_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDCLE, PIN_EBI_NANDCLE_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDALE, PIN_EBI_NANDALE_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_0, PIN_EBI_NANDIO_0_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_1, PIN_EBI_NANDIO_1_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_2, PIN_EBI_NANDIO_2_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_3, PIN_EBI_NANDIO_3_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_4, PIN_EBI_NANDIO_4_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_5, PIN_EBI_NANDIO_5_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_6, PIN_EBI_NANDIO_6_FLAGS);
	gpio_configure_pin(PIN_EBI_NANDIO_7, PIN_EBI_NANDIO_7_FLAGS);
	gpio_configure_pin(PIN_NF_CE_IDX, PIN_NF_CE_FLAGS);
	gpio_configure_pin(PIN_NF_RB_IDX, PIN_NF_RB_FLAGS);
#endif
}
