/**
 * \file
 *
 * \brief SAM4E-EK board init.
 *
 * Copyright (c) 2012 - 2013 Atmel Corporation. All rights reserved.
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
#include "ioport.h"

/**
 * \brief Set peripheral mode for IOPORT pins.
 * It will configure port mode and disable pin mode (but enable peripheral).
 * \param port IOPORT port to configure
 * \param masks IOPORT pin masks to configure
 * \param mode Mode masks to configure for the specified pin (\ref ioport_modes)
 */
#define ioport_set_port_peripheral_mode(port, masks, mode) \
	do {\
		ioport_set_port_mode(port, masks, mode);\
		ioport_disable_port(port, masks);\
	} while (0)

/**
 * \brief Set peripheral mode for one single IOPORT pin.
 * It will configure port mode and disable pin mode (but enable peripheral).
 * \param pin IOPORT pin to configure
 * \param mode Mode masks to configure for the specified pin (\ref ioport_modes)
 */
#define ioport_set_pin_peripheral_mode(pin, mode) \
	do {\
		ioport_set_pin_mode(pin, mode);\
		ioport_disable_pin(pin);\
	} while (0)

/**
 * \brief Set input mode for one single IOPORT pin.
 * It will configure port mode and disable pin mode (but enable peripheral).
 * \param pin IOPORT pin to configure
 * \param mode Mode masks to configure for the specified pin (\ref ioport_modes)
 * \param sense Sense for interrupt detection (\ref ioport_sense)
 */
#define ioport_set_pin_input_mode(pin, mode, sense) \
	do {\
		ioport_set_pin_dir(pin, IOPORT_DIR_INPUT);\
		ioport_set_pin_mode(pin, mode);\
		ioport_set_pin_sense_mode(pin, sense);\
	} while (0)

void board_init(void)
{
#ifndef CONF_BOARD_KEEP_WATCHDOG_AT_INIT
	/* Disable the watchdog */
	WDT->WDT_MR = WDT_MR_WDDIS;
#endif

	/* Initialize IOPORTs */
	ioport_init();

	/* Configure the pins connected to LEDs as output and set their
	 * default initial state to high (LEDs off).
	 */
	ioport_set_pin_dir(LED0_GPIO, IOPORT_DIR_OUTPUT);
	ioport_set_pin_level(LED0_GPIO, LED0_INACTIVE_LEVEL);
	ioport_set_pin_dir(LED1_GPIO, IOPORT_DIR_OUTPUT);
	ioport_set_pin_level(LED1_GPIO, LED0_INACTIVE_LEVEL);
	ioport_set_pin_dir(LED2_GPIO, IOPORT_DIR_OUTPUT);
	ioport_set_pin_level(LED2_GPIO, LED0_INACTIVE_LEVEL);

	/* Configure Push Button pins */
	ioport_set_pin_input_mode(GPIO_PUSH_BUTTON_1, GPIO_PUSH_BUTTON_1_FLAGS,
			GPIO_PUSH_BUTTON_1_SENSE);
	ioport_set_pin_input_mode(GPIO_PUSH_BUTTON_2, GPIO_PUSH_BUTTON_2_FLAGS,
			GPIO_PUSH_BUTTON_2_SENSE);
	ioport_set_pin_input_mode(GPIO_PUSH_BUTTON_3, GPIO_PUSH_BUTTON_3_FLAGS,
			GPIO_PUSH_BUTTON_3_SENSE);
	ioport_set_pin_input_mode(GPIO_PUSH_BUTTON_4, GPIO_PUSH_BUTTON_4_FLAGS,
			GPIO_PUSH_BUTTON_4_SENSE);

#ifdef CONF_BOARD_UART_CONSOLE
	/* Configure UART pins */
	ioport_set_port_peripheral_mode(PINS_UART0_PORT, PINS_UART0,
			PINS_UART0_MASK);
#endif

#ifdef CONF_BOARD_PWM_LED0
	/* Configure PWM LED0 pin */
	ioport_set_pin_peripheral_mode(PIN_PWM_LED0_GPIO, PIN_PWM_LED0_FLAGS);
#endif

#ifdef CONF_BOARD_PWM_LED1
	/* Configure PWM LED1 pin */
	ioport_set_pin_peripheral_mode(PIN_PWM_LED1_GPIO, PIN_PWM_LED1_FLAGS);
#endif

#ifdef CONF_BOARD_PWM_LED2
	/* Configure PWM LED2 pin */
	ioport_set_pin_peripheral_mode(PIN_PWM_LED2_GPIO, PIN_PWM_LED2_FLAGS);
#endif

#ifdef CONF_BOARD_PWM_LED3
	/* Configure PWM LED3 pin */
	ioport_set_pin_peripheral_mode(PIN_PWM_LED3_GPIO, PIN_PWM_LED3_FLAGS);
#endif

#ifdef CONF_BOARD_USART_RXD
	/* Configure USART RXD pin */
	ioport_set_pin_peripheral_mode(PIN_USART1_RXD_IDX,
			PIN_USART1_RXD_FLAGS);
#endif

#ifdef CONF_BOARD_USART_TXD
	/* Configure USART TXD pin */
	ioport_set_pin_peripheral_mode(PIN_USART1_TXD_IDX,
			PIN_USART1_TXD_FLAGS);
#endif

#ifdef CONF_BOARD_USART_CTS
	/* Configure USART CTS pin */
	ioport_set_pin_peripheral_mode(PIN_USART1_CTS_IDX,
			PIN_USART1_CTS_FLAGS);
#endif

#ifdef CONF_BOARD_USART_RTS
	/* Configure USART RTS pin */
	ioport_set_pin_peripheral_mode(PIN_USART1_RTS_IDX,
			PIN_USART1_RTS_FLAGS);
#endif

#ifdef CONF_BOARD_USART_SCK
	/* Configure USART synchronous communication SCK pin */
	ioport_set_pin_peripheral_mode(PIN_USART1_SCK_IDX,
			PIN_USART1_SCK_FLAGS);
#endif

#ifdef CONF_BOARD_ADM3312_EN
	/* Configure ADM3312 enable pin */
	ioport_set_pin_dir(PIN_USART1_EN_IDX, IOPORT_DIR_OUTPUT);
#ifdef CONF_BOARD_ADM3312_EN_DISABLE_AT_INIT
	ioport_set_pin_level(PIN_USART1_EN_IDX, PIN_USART1_EN_INACTIVE_LEVEL);
#else
	ioport_set_pin_level(PIN_USART1_EN_IDX, PIN_USART1_EN_ACTIVE_LEVEL);
#endif
#endif

#ifdef CONF_BOARD_ADS7843
	/* Configure Touchscreen SPI pins */
	ioport_set_pin_dir(BOARD_ADS7843_IRQ_GPIO, IOPORT_DIR_INPUT);
	ioport_set_pin_mode(BOARD_ADS7843_IRQ_GPIO, BOARD_ADS7843_IRQ_FLAGS);
	ioport_set_pin_dir(BOARD_ADS7843_BUSY_GPIO, IOPORT_DIR_INPUT);
	ioport_set_pin_mode(BOARD_ADS7843_BUSY_GPIO, BOARD_ADS7843_BUSY_FLAGS);
	ioport_set_pin_peripheral_mode(SPI_MISO_GPIO, SPI_MISO_FLAGS);
	ioport_set_pin_peripheral_mode(SPI_MOSI_GPIO, SPI_MOSI_FLAGS);
	ioport_set_pin_peripheral_mode(SPI_SPCK_GPIO, SPI_SPCK_FLAGS);
	ioport_set_pin_peripheral_mode(SPI_NPCS0_GPIO, SPI_NPCS0_FLAGS);
#endif

#ifdef CONF_BOARD_CAN0
	/* Configure the CAN0 TX and RX pins. */
	ioport_set_pin_peripheral_mode(PIN_CAN0_RX_IDX, PIN_CAN0_RX_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_CAN0_TX_IDX, PIN_CAN0_TX_FLAGS);
	/* Configure the transiver0 RS & EN pins. */
	ioport_set_pin_dir(PIN_CAN0_TR_RS_IDX, IOPORT_DIR_OUTPUT);
	ioport_set_pin_dir(PIN_CAN0_TR_EN_IDX, IOPORT_DIR_OUTPUT);
#endif

#ifdef CONF_BOARD_CAN1
	/* Configure the CAN1 TX and RX pin. */
	ioport_set_pin_peripheral_mode(PIN_CAN1_RX_IDX, PIN_CAN1_RX_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_CAN1_TX_IDX, PIN_CAN1_TX_FLAGS);
	/* Configure the transiver1 RS & EN pins. */
	ioport_set_pin_dir(PIN_CAN1_TR_RS_IDX, IOPORT_DIR_OUTPUT);
	ioport_set_pin_dir(PIN_CAN1_TR_EN_IDX, IOPORT_DIR_OUTPUT);
#endif

#if defined(CONF_BOARD_USB_PORT)
#  if defined(CONF_BOARD_USB_VBUS_DETECT)
	gpio_configure_pin(USB_VBUS_PIN, USB_VBUS_FLAGS);
#  endif
#endif

#ifdef CONF_BOARD_ILI93XX
	/* Configure LCD EBI pins */
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D0,PIN_EBI_DATA_BUS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D1,PIN_EBI_DATA_BUS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D2,PIN_EBI_DATA_BUS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D3,PIN_EBI_DATA_BUS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D4,PIN_EBI_DATA_BUS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D5,PIN_EBI_DATA_BUS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D6,PIN_EBI_DATA_BUS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_DATA_BUS_D7,PIN_EBI_DATA_BUS_FLAGS);
	
	ioport_set_pin_peripheral_mode(PIN_EBI_NRD,PIN_EBI_NRD_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NWE,PIN_EBI_NWE_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NCS1,PIN_EBI_NCS1_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_LCD_RS,PIN_EBI_LCD_RS_FLAGS);
#endif

#ifdef CONF_BOARD_AAT3155
	/* Configure Backlight control pin */
	ioport_set_pin_dir(BOARD_AAT31XX_SET_GPIO, IOPORT_DIR_OUTPUT);
#endif

#ifdef CONF_BOARD_SPI
	ioport_set_pin_peripheral_mode(SPI_MISO_GPIO, SPI_MISO_FLAGS);
	ioport_set_pin_peripheral_mode(SPI_MOSI_GPIO, SPI_MOSI_FLAGS);
	ioport_set_pin_peripheral_mode(SPI_SPCK_GPIO, SPI_SPCK_FLAGS);

#ifdef CONF_BOARD_SPI_NPCS0
	ioport_set_pin_peripheral_mode(SPI_NPCS0_GPIO, SPI_NPCS0_FLAGS);
#endif

#ifdef CONF_BOARD_SPI_NPCS3
#if defined(CONF_BOARD_SPI_NPCS3_GPIO) && defined(CONF_BOARD_SPI_NPCS3_FLAGS)
	ioport_set_pin_peripheral_mode(CONF_BOARD_SPI_NPCS3_GPIO,
			CONF_BOARD_SPI_NPCS3_FLAGS);
#else
	ioport_set_pin_peripheral_mode(SPI_NPCS3_PA5_GPIO, SPI_NPCS3_PA5_FLAGS);
#endif
#endif
#endif

#if (defined(CONF_BOARD_TWI0) || defined(CONF_BOARD_QTOUCH))
	ioport_set_pin_peripheral_mode(TWI0_DATA_GPIO, TWI0_DATA_FLAGS);
	ioport_set_pin_peripheral_mode(TWI0_CLK_GPIO, TWI0_CLK_FLAGS);
#endif

#if defined (CONF_BOARD_SD_MMC_HSMCI)
	/* Configure HSMCI pins */
	ioport_set_pin_peripheral_mode(PIN_HSMCI_MCCDA_GPIO, PIN_HSMCI_MCCDA_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_HSMCI_MCCK_GPIO, PIN_HSMCI_MCCK_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_HSMCI_MCDA0_GPIO, PIN_HSMCI_MCDA0_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_HSMCI_MCDA1_GPIO, PIN_HSMCI_MCDA1_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_HSMCI_MCDA2_GPIO, PIN_HSMCI_MCDA2_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_HSMCI_MCDA3_GPIO, PIN_HSMCI_MCDA3_FLAGS);

	/* Configure SD/MMC card detect pin */
	ioport_set_pin_peripheral_mode(SD_MMC_0_CD_GPIO, SD_MMC_0_CD_FLAGS);
#endif

#ifdef CONF_BOARD_TWI1
	ioport_set_pin_peripheral_mode(TWI1_DATA_GPIO, TWI1_DATA_FLAGS);
	ioport_set_pin_peripheral_mode(TWI1_CLK_GPIO, TWI1_CLK_FLAGS);
#endif

#ifdef CONF_BOARD_KSZ8051MNL
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_RXC_IDX,
			PIN_KSZ8051MNL_RXC_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_TXC_IDX,
			PIN_KSZ8051MNL_TXC_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_TXEN_IDX,
			PIN_KSZ8051MNL_TXEN_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_TXD3_IDX,
			PIN_KSZ8051MNL_TXD3_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_TXD2_IDX,
			PIN_KSZ8051MNL_TXD2_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_TXD1_IDX,
			PIN_KSZ8051MNL_TXD1_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_TXD0_IDX,
			PIN_KSZ8051MNL_TXD0_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_RXD3_IDX,
			PIN_KSZ8051MNL_RXD3_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_RXD2_IDX,
			PIN_KSZ8051MNL_RXD2_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_RXD1_IDX,
			PIN_KSZ8051MNL_RXD1_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_RXD0_IDX,
			PIN_KSZ8051MNL_RXD0_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_RXER_IDX,
			PIN_KSZ8051MNL_RXER_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_RXDV_IDX,
			PIN_KSZ8051MNL_RXDV_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_CRS_IDX,
			PIN_KSZ8051MNL_CRS_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_COL_IDX,
			PIN_KSZ8051MNL_COL_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_MDC_IDX,
			PIN_KSZ8051MNL_MDC_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_KSZ8051MNL_MDIO_IDX,
			PIN_KSZ8051MNL_MDIO_FLAGS);
	ioport_set_pin_dir(PIN_KSZ8051MNL_INTRP_IDX, IOPORT_DIR_INPUT);
#endif

#ifdef CONF_BOARD_TFDU4300_SD
	/* Configure IrDA transceiver shutdown pin */
	ioport_set_pin_dir(PIN_IRDA_SD_IDX, IOPORT_DIR_OUTPUT);
	ioport_set_pin_level(PIN_IRDA_SD_IDX, IOPORT_PIN_LEVEL_HIGH);
#endif

#ifdef CONF_BOARD_ADM3485_RE
	/* Configure RS485 transceiver RE pin */
	ioport_set_pin_dir(PIN_RE_IDX, IOPORT_DIR_OUTPUT);
	ioport_set_pin_level(PIN_RE_IDX, IOPORT_PIN_LEVEL_LOW);
#endif

#ifdef CONF_BOARD_ISO7816_RST
	/* Configure ISO7816 card reset pin */
	ioport_set_pin_dir(PIN_ISO7816_RST_IDX, IOPORT_DIR_OUTPUT);
	ioport_set_pin_level(PIN_ISO7816_RST_IDX, IOPORT_PIN_LEVEL_LOW);
#endif

#ifdef CONF_BOARD_ISO7816
	/* Configure ISO7816 interface TXD & SCK pin */
	ioport_set_pin_peripheral_mode(PIN_USART1_TXD_IDX, PIN_USART1_TXD_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_USART1_SCK_IDX, PIN_USART1_SCK_FLAGS);
#endif

#ifdef CONF_BOARD_NAND
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDOE,   PIN_EBI_NANDOE_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDWE,   PIN_EBI_NANDWE_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDCLE,  PIN_EBI_NANDCLE_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDALE,  PIN_EBI_NANDALE_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_0, PIN_EBI_NANDIO_0_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_1, PIN_EBI_NANDIO_1_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_2, PIN_EBI_NANDIO_2_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_3, PIN_EBI_NANDIO_3_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_4, PIN_EBI_NANDIO_4_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_5, PIN_EBI_NANDIO_5_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_6, PIN_EBI_NANDIO_6_FLAGS);
	ioport_set_pin_peripheral_mode(PIN_EBI_NANDIO_7, PIN_EBI_NANDIO_7_FLAGS);
    ioport_set_pin_dir(PIN_NF_CE_IDX, IOPORT_DIR_OUTPUT);
    ioport_set_pin_dir(PIN_NF_RB_IDX, IOPORT_DIR_INPUT);
	ioport_set_pin_mode(PIN_NF_RB_IDX, IOPORT_MODE_PULLUP);
#endif


#ifdef CONF_BOARD_QTOUCH
	/* Configure CHANGE pin for QTouch device */
	ioport_set_pin_input_mode(BOARD_QT_CHANGE_PIN_IDX, BOARD_QT_CHANGE_PIN_FLAGS,
			BOARD_QT_CHANGE_PIN_SENSE);
#endif
}
