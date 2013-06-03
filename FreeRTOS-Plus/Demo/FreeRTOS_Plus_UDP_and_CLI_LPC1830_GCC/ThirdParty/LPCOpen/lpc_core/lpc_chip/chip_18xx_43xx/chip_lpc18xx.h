/*
 * @brief LPC18xx basic chip inclusion file
 *
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __CHIP_LPC18XX_H_
#define __CHIP_LPC18XX_H_

#ifdef __cplusplus
extern "C" {
#endif

#include "lpc_types.h"
#include "sys_config.h"

#ifndef CORE_M3
#error CORE_M3 is not defined for the LPC18xx architecture
#error CORE_M3 should be defined as part of your compiler define list
#endif

#ifndef CHIP_LPC18XX
#error The LPC18XX Chip include path is used for this build, but
#error CHIP_LPC18XX is not defined!
#endif

/** @defgroup IP_LPC18XX_FILES CHIP: LPC18XX Chip layer required IP layer drivers
 * @ingroup CHIP_18XX_43XX_Drivers
 * This is a list of the IP drivers required for the LPC18XX device family.<br>
 * (adc_001.c, adc_001.h) @ref IP_ADC_001<br>
 * (atimer_001.c, atimer_001.h) @ref IP_ATIMER_001<br>
 * (ccan_001.c, ccan_001.h) @ref IP_CCAN_001<br>
 * (dac_001.c, dac_001.h) @ref IP_DAC_001<br>
 * (emc_001.c, emc_001.h) @ref IP_EMC_001<br>
 * (enet_001.c, enet_001.h) @ref IP_ENET_001<br>
 * (gima_001.h) @ref IP_GIMA_001<br>
 * (gpdma_001.c, gpdma_001.h) @ref IP_GPDMA_001<br>
 * (gpiogrpint_001.c, gpiogrpint_001.h) @ref IP_GPIOGRPINT_001<br>
 * (gpiopinint_001.c, gpiopinint_001.h) @ref IP_GPIOPININT_001<br>
 * (gpio_001.h) @ref IP_GPIO_001<br>
 * (i2c_001.c, i2c_001.h) @ref IP_I2C_001<br>
 * (i2s_001.c, i2s_001.h) @ref IP_I2S_001<br>
 * (lcd_001.c, lcd_001.h) @ref IP_LCD_001<br>
 * (mcpwm_001.h) @ref IP_MCPWM_001<br>
 * (pmc_001.h) @ref IP_PMC_001<br>
 * (qei_001.h) @ref IP_QEI_001<br>
 * (regfile_001.h) @ref IP_REGFILE_001<br>
 * (ritimer_001.c, ritimer_001.h) @ref IP_RITIMER_001<br>
 * (rtc_001.c, rtc_001.h) @ref IP_RTC_001<br>
 * (sct_001.c, sct_001.h) @ref IP_SCT_001<br>
 * (sdmmc_001.c, sdmmc_001.h) @ref IP_SDMMC_001<br>
 * (ssp_001.c, ssp_001.h) @ref IP_SSP_001<br>
 * (timer_001.c, timer_001.h) @ref IP_TIMER_001<br>
 * (usart_001.c, usart_001.h) @ref IP_USART_001<br>
 * (usbhs_001.h) @ref IP_USBHS_001<br>
 * (wwdt_001.c, wwdt_001.h) @ref IP_WWDT_001<br>
 * (eeprom_002.c, eeprom_002.h) @ref IP_EEPROM_002<br>
 * @{
 */

/**
 * @}
 */


#include "adc_001.h"
#include "atimer_001.h"
#include "ccan_001.h"
#include "dac_001.h"
#include "emc_001.h"
#include "enet_001.h"
#include "gima_001.h"
#include "gpdma_001.h"
#include "gpiogrpint_001.h"
#include "gpiopinint_001.h"
#include "gpio_001.h"
#include "i2c_001.h"
#include "i2s_001.h"
#include "lcd_001.h"
#include "mcpwm_001.h"
#include "pmc_001.h"
#include "qei_001.h"
#include "regfile_001.h"
#include "ritimer_001.h"
#include "rtc_001.h"
#include "sct_001.h"
#include "sdmmc_001.h"
#include "ssp_001.h"
#include "timer_001.h"
#include "usart_001.h"
#include "usbhs_001.h"
#include "wwdt_001.h"
#include "rgu_18xx_43xx.h"
#include "cguccu_18xx_43xx.h"
#include "eeprom_002.h"

/** @defgroup PERIPH_18XX_BASE CHIP: LPC18xx Peripheral addresses and register set declarations
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

#define LPC_SCT_BASE              0x40000000
#define LPC_GPDMA_BASE            0x40002000
#define LPC_SDMMC_BASE            0x40004000
#define LPC_EMC_BASE              0x40005000
#define LPC_USB0_BASE             0x40006000
#define LPC_USB1_BASE             0x40007000
#define LPC_LCD_BASE              0x40008000
#define LPC_ETHERNET_BASE         0x40010000
#define LPC_ATIMER_BASE           0x40040000
#define LPC_REGFILE_BASE          0x40041000
#define LPC_PMC_BASE              0x40042000
#define LPC_CREG_BASE             0x40043000
#define LPC_EVRT_BASE             0x40044000
#define LPC_OTP_BASE              0x40045000
#define LPC_RTC_BASE              0x40046000
#define LPC_CGU_BASE              0x40050000
#define LPC_CCU1_BASE             0x40051000
#define LPC_CCU2_BASE             0x40052000
#define LPC_RGU_BASE              0x40053000
#define LPC_WWDT_BASE             0x40080000
#define LPC_USART0_BASE           0x40081000
#define LPC_USART2_BASE           0x400C1000
#define LPC_USART3_BASE           0x400C2000
#define LPC_UART1_BASE            0x40082000
#define LPC_SSP0_BASE             0x40083000
#define LPC_SSP1_BASE             0x400C5000
#define LPC_TIMER0_BASE           0x40084000
#define LPC_TIMER1_BASE           0x40085000
#define LPC_TIMER2_BASE           0x400C3000
#define LPC_TIMER3_BASE           0x400C4000
#define LPC_SCU_BASE              0x40086000
#define LPC_GPIO_PIN_INT_BASE     0x40087000
#define LPC_GPIO_GROUP_INT0_BASE  0x40088000
#define LPC_GPIO_GROUP_INT1_BASE  0x40089000
#define LPC_MCPWM_BASE            0x400A0000
#define LPC_I2C0_BASE             0x400A1000
#define LPC_I2C1_BASE             0x400E0000
#define LPC_I2S0_BASE             0x400A2000
#define LPC_I2S1_BASE             0x400A3000
#define LPC_C_CAN1_BASE           0x400A4000
#define LPC_RITIMER_BASE          0x400C0000
#define LPC_QEI_BASE              0x400C6000
#define LPC_GIMA_BASE             0x400C7000
#define LPC_DAC_BASE              0x400E1000
#define LPC_C_CAN0_BASE           0x400E2000
#define LPC_ADC0_BASE             0x400E3000
#define LPC_ADC1_BASE             0x400E4000
#define LPC_GPIO_PORT_BASE        0x400F4000
#define LPC_SPI_BASE              0x40100000
#define LPC_SGPIO_BASE            0x40101000
#define LPC_EEPROM_BASE           0x4000E000

/* Normalize types */
typedef IP_SCT_001_T LPC_SCT_T;
typedef IP_GPDMA_001_T LPC_GPDMA_T;
typedef IP_SDMMC_001_T LPC_SDMMC_T;
typedef IP_EMC_001_T LPC_EMC_T;
typedef IP_USBHS_001_T LPC_USBHS_T;
typedef IP_ENET_001_T LPC_ENET_T;
typedef IP_ATIMER_001_T LPC_ATIMER_T;
typedef IP_REGFILE_001_T LPC_REGFILE_T;
typedef IP_PMC_001_T LPC_PMC_T;
typedef IP_RTC_001_T LPC_RTC_T;
typedef IP_WWDT_001_T LPC_WWDT_T;
typedef IP_USART_001_T LPC_USART_T;
typedef IP_SSP_001_T LPC_SSP_T;
typedef IP_TIMER_001_T LPC_TIMER_T;
typedef IP_GPIOPININT_001_T LPC_GPIOPININT_T;
typedef IP_MCPWM_001_T LPC_MCPWM_T;
typedef IP_I2C_001_T LPC_I2C_T;
typedef IP_I2S_001_T LPC_I2S_T;
typedef IP_CCAN_001_T LPC_CCAN_T;
typedef IP_RITIMER_001_T LPC_RITIMER_T;
typedef IP_QEI_001_T LPC_QEI_T;
typedef IP_GIMA_001_T LPC_GIMA_T;
typedef IP_DAC_001_T LPC_DAC_T;
typedef IP_ADC_001_T LPC_ADC_T;
typedef IP_GPIO_001_T LPC_GPIO_T;
typedef IP_LCD_001_T LPC_LCD_T;
typedef IP_EEPROM_002_T LPC_EEPROM_T;

#define LPC_SCT                   ((IP_SCT_001_T              *) LPC_SCT_BASE)
#define LPC_GPDMA                 ((IP_GPDMA_001_T            *) LPC_GPDMA_BASE)
#define LPC_SDMMC                 ((IP_SDMMC_001_T            *) LPC_SDMMC_BASE)
#define LPC_EMC                   ((IP_EMC_001_T              *) LPC_EMC_BASE)
#define LPC_USB0                  ((IP_USBHS_001_T            *) LPC_USB0_BASE)
#define LPC_USB1                  ((IP_USBHS_001_T            *) LPC_USB1_BASE)
#define LPC_LCD                   ((IP_LCD_001_T              *) LPC_LCD_BASE)
#define LPC_ETHERNET              ((IP_ENET_001_T             *) LPC_ETHERNET_BASE)
#define LPC_ATIMER                ((IP_ATIMER_001_T           *) LPC_ATIMER_BASE)
#define LPC_REGFILE               ((IP_REGFILE_001_T             *) LPC_REGFILE_BASE)
#define LPC_PMC                   ((IP_PMC_001_T              *) LPC_PMC_BASE)
#define LPC_EVRT                  ((LPC_EVRT_T                *) LPC_EVRT_BASE)
#define LPC_RTC                   ((IP_RTC_001_T                 *) LPC_RTC_BASE)
#define LPC_CGU                   ((LPC_CGU_T                    *) LPC_CGU_BASE)
#define LPC_CCU1                  ((LPC_CCU1_T                *) LPC_CCU1_BASE)
#define LPC_CCU2                  ((LPC_CCU2_T                *) LPC_CCU2_BASE)
#define LPC_CREG                  ((LPC_CREG_T                   *) LPC_CREG_BASE)
#define LPC_RGU                   ((LPC_RGU_T                    *) LPC_RGU_BASE)
#define LPC_WWDT                  ((IP_WWDT_001_T             *) LPC_WWDT_BASE)
#define LPC_USART0                ((IP_USART_001_T            *) LPC_USART0_BASE)
#define LPC_USART2                ((IP_USART_001_T            *) LPC_USART2_BASE)
#define LPC_USART3                ((IP_USART_001_T            *) LPC_USART3_BASE)
#define LPC_UART1                 ((IP_USART_001_T            *) LPC_UART1_BASE)
#define LPC_SSP0                  ((IP_SSP_001_T              *) LPC_SSP0_BASE)
#define LPC_SSP1                  ((IP_SSP_001_T              *) LPC_SSP1_BASE)
#define LPC_TIMER0                ((IP_TIMER_001_T            *) LPC_TIMER0_BASE)
#define LPC_TIMER1                ((IP_TIMER_001_T            *) LPC_TIMER1_BASE)
#define LPC_TIMER2                ((IP_TIMER_001_T            *) LPC_TIMER2_BASE)
#define LPC_TIMER3                ((IP_TIMER_001_T            *) LPC_TIMER3_BASE)
#define LPC_SCU                   ((LPC_SCU_T                 *) LPC_SCU_BASE)
#define LPC_GPIO_PIN_INT          ((IP_GPIOPININT_001_T       *) LPC_GPIO_PIN_INT_BASE)
#define LPC_GPIO_GROUP_INT0       ((IP_GPIOGROUPINT_001_T     *) LPC_GPIO_GROUP_INT0_BASE)
#define LPC_GPIO_GROUP_INT1       ((IP_GPIOGROUPINT_001_T     *) LPC_GPIO_GROUP_INT1_BASE)
#define LPC_MCPWM                 ((IP_MCPWM_001_T            *) LPC_MCPWM_BASE)
#define LPC_I2C0                  ((IP_I2C_001_T              *) LPC_I2C0_BASE)
#define LPC_I2C1                  ((IP_I2C_001_T              *) LPC_I2C1_BASE)
#define LPC_I2S0                  ((IP_I2S_001_T              *) LPC_I2S0_BASE)
#define LPC_I2S1                  ((IP_I2S_001_T              *) LPC_I2S1_BASE)
#define LPC_C_CAN1                ((IP_CCAN_001_T             *) LPC_C_CAN1_BASE)
#define LPC_RITIMER               ((IP_RITIMER_001_T          *) LPC_RITIMER_BASE)
#define LPC_QEI                   ((IP_QEI_001_T              *) LPC_QEI_BASE)
#define LPC_GIMA                  ((IP_GIMA_001_T             *) LPC_GIMA_BASE)
#define LPC_DAC                   ((IP_DAC_001_T              *) LPC_DAC_BASE)
#define LPC_C_CAN0                ((IP_CCAN_001_T             *) LPC_C_CAN0_BASE)
#define LPC_ADC0                  ((IP_ADC_001_T              *) LPC_ADC0_BASE)
#define LPC_ADC1                  ((IP_ADC_001_T              *) LPC_ADC1_BASE)
#define LPC_GPIO_PORT             ((IP_GPIO_001_T             *) LPC_GPIO_PORT_BASE)
#define LPC_EEPROM                ((IP_EEPROM_002_T           *) LPC_EEPROM_BASE)

/**
 * @}
 */

#include "clock_18xx_43xx.h"
#include "gpio_18xx_43xx.h"
#include "uart_18xx_43xx.h"
#include "gpdma_18xx_43xx.h"
#include "enet_18xx_43xx.h"
#include "i2c_18xx_43xx.h"
#include "i2s_18xx_43xx.h"
#include "ssp_18xx_43xx.h"
#include "rtc_18xx_43xx.h"
#include "evrt_18xx_43xx.h"
#include "atimer_18xx_43xx.h"
#include "wwdt_18xx_43xx.h"
#include "ritimer_18xx_43xx.h"
#include "emc_18xx_43xx.h"
#include "lcd_18xx_43xx.h"
#include "adc_18xx_43xx.h"
#include "dac_18xx_43xx.h"
#include "sdif_18xx_43xx.h"
#include "sdmmc_18xx_43xx.h"
#include "timer_18xx_43xx.h"
#include "creg_18xx_43xx.h"
#include "scu_18xx_43xx.h"
#include "sct_18xx_43xx.h"
#include "ccan_18xx_43xx.h"
#include "pmc_18xx_43xx.h"
#include "otp_18xx_43xx.h"
#include "aes_18xx_43xx.h"
#include "eeprom_18xx_43xx.h"

#ifdef __cplusplus
}
#endif

#endif /* __CHIP_LPC18XX_H_ */
