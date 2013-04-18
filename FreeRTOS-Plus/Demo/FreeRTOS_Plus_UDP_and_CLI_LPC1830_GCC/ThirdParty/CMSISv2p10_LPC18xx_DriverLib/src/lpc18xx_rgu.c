/**********************************************************************
* $Id$		lpc18xx_rgu.c		2011-06-02
*//**
* @file		lpc18xx_rgu.c
* @brief	Contains all functions support for RGU firmware library on LPC18xx
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

/* Peripheral group ----------------------------------------------------------- */
/** @addtogroup RGU
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_rgu.h"
#include "lpc18xx_cgu.h"

/* If this source file built with example, the LPC18xx FW library configuration
 * file in each example directory ("lpc18xx_libcfg.h") must be included,
 * otherwise the default FW library configuration file must be included instead
 */
#ifdef __BUILD_WITH_EXAMPLE__
#include "lpc18xx_libcfg.h"
#else
#include "lpc18xx_libcfg_default.h"
#endif /* __BUILD_WITH_EXAMPLE__ */


#ifdef _RGU
/* Public Functions ----------------------------------------------------------- */
/** @addtogroup RGU_Public_Functions
 * @{
 */

/*********************************************************************//**
 * @brief 		Soft Reset a Signal
 * @param[in]	ResetSignal indicates which signal will be reset, should be:
 * 					- RGU_SIG_CORE		:Core
 * 					- RGU_SIG_PERIPH	:Peripheral
 * 					- RGU_SIG_MASTER	:Master
 * 					- RGU_SIG_WWDT		:WWDT
 * 					- RGU_SIG_CREG		:Configuration register block
 * 					- RGU_SIG_BUS		:Buses
 * 					- RGU_SIG_SCU		:System control unit
 * 					- RGU_SIG_PINMUX	:Pin mux
 * 					- RGU_SIG_M3		:Cortex-M3 system
 * 					- RGU_SIG_LCD		:LCD controller
 * 					- RGU_SIG_USB0		:USB0
 * 					- RGU_SIG_USB1		:USB1
 * 					- RGU_SIG_DMA		:DMA
 * 					- RGU_SIG_SDIO		:SDIO
 * 					- RGU_SIG_EMC		:External memory controller
 * 					- RGU_SIG_ETHERNET	:Ethernet
 * 					- RGU_SIG_AES		:AES
 * 					- RGU_SIG_GPIO		:GPIO
 * 					- RGU_SIG_TIMER0	:Timer 0
 * 					- RGU_SIG_TIMER1	:Timer 1
 * 					- RGU_SIG_TIMER2	:Timer 2
 * 					- RGU_SIG_TIMER3	:Timer 3
 * 					- RGU_SIG_RITIMER	:Repetitive Interrupt Timer
 * 					- RGU_SIG_SCT		:State Configurable Timer
 * 					- RGU_SIG_MOTOCONPWM:Motor Control PWM
 * 					- RGU_SIG_QEI		:QEI
 * 					- RGU_SIG_ADC0		:ADC0
 * 					- RGU_SIG_ADC1		:ADC1
 * 					- RGU_SIG_DAC		:DAC
 * 					- RGU_SIG_UART0		:UART0
 * 					- RGU_SIG_UART1		:UART1
 * 					- RGU_SIG_UART2		:UART2
 * 					- RGU_SIG_UART3		:UART3
 * 					- RGU_SIG_I2C0		:I2C0
 * 					- RGU_SIG_I2C1		:I2C1
 * 					- RGU_SIG_SSP0		:SSP0
 * 					- RGU_SIG_SSP1		:SSP1
 * 					- RGU_SIG_I2S		:I2S
 * 					- RGU_SIG_SPIFI		:SPIFI
 * 					- RGU_SIG_CAN		:CAN
 * @return 		None
 **********************************************************************/
void RGU_SoftReset(RGU_SIG ResetSignal)
{
	if(ResetSignal < 32){
		LPC_RGU->RESET_CTRL0 = 1 << ResetSignal;
		LPC_RGU->RESET_CTRL0 = 0;
	}else{
		LPC_RGU->RESET_CTRL1 = 1 << (ResetSignal - 32);
		LPC_RGU->RESET_CTRL1 = 0;
	}
}

/*********************************************************************//**
 * @brief 		Get source cause of a signal
 * @param[in]	ResetSignal reset signal, should be:
 * 					- RGU_SIG_CORE		:Core
 * 					- RGU_SIG_PERIPH	:Peripheral
 * 					- RGU_SIG_MASTER	:Master
 * 					- RGU_SIG_WWDT		:WWDT
 * 					- RGU_SIG_CREG		:Configuration register block
 * 					- RGU_SIG_BUS		:Buses
 * 					- RGU_SIG_SCU		:System control unit
 * 					- RGU_SIG_PINMUX	:Pin mux
 * 					- RGU_SIG_M3		:Cortex-M3 system
 * 					- RGU_SIG_LCD		:LCD controller
 * 					- RGU_SIG_USB0		:USB0
 * 					- RGU_SIG_USB1		:USB1
 * 					- RGU_SIG_DMA		:DMA
 * 					- RGU_SIG_SDIO		:SDIO
 * 					- RGU_SIG_EMC		:External memory controller
 * 					- RGU_SIG_ETHERNET	:Ethernet
 * 					- RGU_SIG_AES		:AES
 * 					- RGU_SIG_GPIO		:GPIO
 * 					- RGU_SIG_TIMER0	:Timer 0
 * 					- RGU_SIG_TIMER1	:Timer 1
 * 					- RGU_SIG_TIMER2	:Timer 2
 * 					- RGU_SIG_TIMER3	:Timer 3
 * 					- RGU_SIG_RITIMER	:Repetitive Interrupt Timer
 * 					- RGU_SIG_SCT		:State Configurable Timer
 * 					- RGU_SIG_MOTOCONPWM:Motor Control PWM
 * 					- RGU_SIG_QEI		:QEI
 * 					- RGU_SIG_ADC0		:ADC0
 * 					- RGU_SIG_ADC1		:ADC1
 * 					- RGU_SIG_DAC		:DAC
 * 					- RGU_SIG_UART0		:UART0
 * 					- RGU_SIG_UART1		:UART1
 * 					- RGU_SIG_UART2		:UART2
 * 					- RGU_SIG_UART3		:UART3
 * 					- RGU_SIG_I2C0		:I2C0
 * 					- RGU_SIG_I2C1		:I2C1
 * 					- RGU_SIG_SSP0		:SSP0
 * 					- RGU_SIG_SSP1		:SSP1
 * 					- RGU_SIG_I2S		:I2S
 * 					- RGU_SIG_SPIFI		:SPIFI
 * 					- RGU_SIG_CAN		:CAN
 * @return 		Source cause of reset, could be:
 * 					- RGU_SRC_NONE		:No source
 * 					- RGU_SRC_SOFT		:Software reset source
 * 					- RGU_SRC_EXT		:External reset source
 * 					- RGU_SRC_CORE		:Core reset source
 * 					- RGU_SRC_PERIPH	:Peripheral reset source
 * 					- RGU_SRC_MASTER	:Master reset source
 * 					- RGU_SRC_BOD		:BOD reset source
 * 					- RGU_SRC_WWDT		:WWDT reset source
 **********************************************************************/
RGU_SRC RGU_GetSource(RGU_SIG ResetSignal)
{
	uint32_t i, temp, registercache;
	if(ResetSignal < 16)
		temp = 3 & (LPC_RGU->RESET_STATUS0 >> ResetSignal);
	else if(ResetSignal < 32)
		temp = 3 & (LPC_RGU->RESET_STATUS1 >> (ResetSignal - 16));
	else if(ResetSignal < 48)
		temp = 3 & (LPC_RGU->RESET_STATUS2 >> (ResetSignal - 32));
	else
		temp = 3 & (LPC_RGU->RESET_STATUS3 >> (ResetSignal - 48));

	if(temp == 0) return RGU_SRC_NONE;
	else if(temp == 3) return RGU_SRC_SOFT;
	else if(temp == 1){
		registercache = (((uint32_t*)&LPC_RGU->RESET_EXT_STAT0)[ResetSignal]);
		for(i = 0; i < 6; i++){
			if(registercache & (1<<i)){
				return (RGU_SRC)(RGU_SRC_EXT + i);
			}
		}
	}
	return RGU_SRC_NONE;
}

/*********************************************************************//**
 * @brief 		Get Current Status of Signal
 * @param[in]	ResetSignal Reset Signal, should be:
 * 					- RGU_SIG_CORE		:Core
 * 					- RGU_SIG_PERIPH	:Peripheral
 * 					- RGU_SIG_MASTER	:Master
 * 					- RGU_SIG_WWDT		:WWDT
 * 					- RGU_SIG_CREG		:Configuration register block
 * 					- RGU_SIG_BUS		:Buses
 * 					- RGU_SIG_SCU		:System control unit
 * 					- RGU_SIG_PINMUX	:Pin mux
 * 					- RGU_SIG_M3		:Cortex-M3 system
 * 					- RGU_SIG_LCD		:LCD controller
 * 					- RGU_SIG_USB0		:USB0
 * 					- RGU_SIG_USB1		:USB1
 * 					- RGU_SIG_DMA		:DMA
 * 					- RGU_SIG_SDIO		:SDIO
 * 					- RGU_SIG_EMC		:External memory controller
 * 					- RGU_SIG_ETHERNET	:Ethernet
 * 					- RGU_SIG_AES		:AES
 * 					- RGU_SIG_GPIO		:GPIO
 * 					- RGU_SIG_TIMER0	:Timer 0
 * 					- RGU_SIG_TIMER1	:Timer 1
 * 					- RGU_SIG_TIMER2	:Timer 2
 * 					- RGU_SIG_TIMER3	:Timer 3
 * 					- RGU_SIG_RITIMER	:Repetitive Interrupt Timer
 * 					- RGU_SIG_SCT		:State Configurable Timer
 * 					- RGU_SIG_MOTOCONPWM:Motor Control PWM
 * 					- RGU_SIG_QEI		:QEI
 * 					- RGU_SIG_ADC0		:ADC0
 * 					- RGU_SIG_ADC1		:ADC1
 * 					- RGU_SIG_DAC		:DAC
 * 					- RGU_SIG_UART0		:UART0
 * 					- RGU_SIG_UART1		:UART1
 * 					- RGU_SIG_UART2		:UART2
 * 					- RGU_SIG_UART3		:UART3
 * 					- RGU_SIG_I2C0		:I2C0
 * 					- RGU_SIG_I2C1		:I2C1
 * 					- RGU_SIG_SSP0		:SSP0
 * 					- RGU_SIG_SSP1		:SSP1
 * 					- RGU_SIG_I2S		:I2S
 * 					- RGU_SIG_SPIFI		:SPIFI
 * 					- RGU_SIG_CAN		:CAN
 * @return 		Signal status, could be:
 * 					- TRUE	:reset is active
 * 					- FALSE	:reset is inactive
 **********************************************************************/
Bool RGU_GetSignalStatus(RGU_SIG ResetSignal)
{
	if(ResetSignal < 32)
		return (Bool)!(LPC_RGU->RESET_ACTIVE_STATUS0 | (1 << ResetSignal));
	else
		return (Bool)!(LPC_RGU->RESET_ACTIVE_STATUS1 | (1 << (ResetSignal - 32)));
}


/**
 * @}
 */

#endif /* _RGU */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */

