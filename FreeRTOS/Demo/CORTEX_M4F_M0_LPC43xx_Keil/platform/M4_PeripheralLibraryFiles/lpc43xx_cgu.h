/**********************************************************************
* $Id$		lpc43xx_cgu.h			2011-06-02
*//**
* @file		llpc43xx_cgu.h
* @brief	Contains all macro definitions and function prototypes
* 			support for Clock Generation and Clock Control firmware
* 			library on lpc43xx
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
/** @defgroup CGU CGU (Clock Generation Unit)
 * @ingroup LPC4300CMSIS_FwLib_Drivers
 * @{
 */

#ifndef lpc43xx_CGU_H_
#define lpc43xx_CGU_H_

/* Includes ------------------------------------------------------------------- */
#include "lpc43xx.h"
#include "lpc_types.h"

#ifdef __cplusplus
extern "C"
{
#endif

/* Private Macros -------------------------------------------------------------- */
/** @defgroup CGU_Private_Macros CGU Private Macros
 * @{
 */

/** Branch clocks from CGU_BASE_SAFE */
#define CGU_ENTITY_NONE				CGU_ENTITY_NUM

/** Check bit at specific position is clear or not */
#define ISBITCLR(x,bit) 			((x&(1<<bit))^(1<<bit))
/** Check bit at specific position is set or not */
#define ISBITSET(x,bit) 			(x&(1<<bit))
/** Set mask */
#define ISMASKSET(x,mask) 			(x&mask)

/** CGU number of clock source */
#define CGU_CLKSRC_NUM (CGU_CLKSRC_IDIVE+1)

/*********************************************************************//**
 * Macro defines for CGU control mask bit definitions
 **********************************************************************/
/** CGU control enable mask bit */
#define CGU_CTRL_EN_MASK			1
/** CGU control clock-source mask bit */
#define CGU_CTRL_SRC_MASK			(0xF<<24)
/** CGU control auto block mask bit */
#define CGU_CTRL_AUTOBLOCK_MASK		(1<<11)

/*********************************************************************//**
 * Macro defines for CGU PLL1 mask bit definitions
 **********************************************************************/
/** CGU PLL1 feedback select mask bit */
#define CGU_PLL1_FBSEL_MASK			(1<<6)
/** CGU PLL1 Input clock bypass control mask bit */
#define CGU_PLL1_BYPASS_MASK		(1<<1)
/** CGU PLL1 direct CCO output mask bit */
#define CGU_PLL1_DIRECT_MASK		(1<<7)

/**
 * @}
 */

/* Public Types --------------------------------------------------------------- */
/** @defgroup CGU_Public_Types CGU Public Types
 * @{
 */

/*********************************************************************//**
 * @brief CGU enumeration
 **********************************************************************/
/*
 * @brief	CGU clock source enumerate definition
 */
typedef enum {
	/* Clock Source */
	CGU_CLKSRC_32KHZ_OSC = 0,					/**< 32KHz oscillator clock source 	*/
	CGU_CLKSRC_IRC,								/**< IRC 12 Mhz clock source 		*/
	CGU_CLKSRC_ENET_RX_CLK,						/**< Ethernet receive clock source 	*/
	CGU_CLKSRC_ENET_TX_CLK,						/**< Ethernet transmit clock source */
	CGU_CLKSRC_GP_CLKIN,						/**< General purpose clock source 	*/
	CGU_CLKSRC_TCK,								/**< TCK clock source 				*/
	CGU_CLKSRC_XTAL_OSC,						/**< Crystal oscillator clock source*/
	CGU_CLKSRC_PLL0,							/**< PLL0 (USB0) clock source		*/
	CGU_CLKSRC_PLL0_AUDIO,
	CGU_CLKSRC_PLL1,							/**< PLL1 clock source				*/
	CGU_CLKSRC_IDIVA = CGU_CLKSRC_PLL1 + 3,		/**< IDIVA clock source				*/
	CGU_CLKSRC_IDIVB,							/**< IDIVB clock source				*/
	CGU_CLKSRC_IDIVC,							/**< IDIVC clock source				*/
	CGU_CLKSRC_IDIVD,							/**< IDIVD clock source				*/
	CGU_CLKSRC_IDIVE,							/**< IDIVE clock source				*/

	/* Base */
	CGU_BASE_SAFE,								/**< Base save clock (always on) for WDT */
	CGU_BASE_USB0,								/**< USB0 base clock 				*/
	CGU_BASE_USB1 = CGU_BASE_USB0 + 2,			/**< USB1 base clock 				*/
	CGU_BASE_M3,								/**< ARM Cortex-M3 Core base clock 	*/
	CGU_BASE_SPIFI,								/**< SPIFI base clock				*/
	//CGU_BASE_SPI,
	CGU_BASE_PHY_RX = CGU_BASE_SPIFI + 2,		/**< Ethernet PHY Rx base clock		*/
	CGU_BASE_PHY_TX,							/**< Ethernet PHY Tx base clock		*/
	CGU_BASE_APB1,								/**< APB peripheral block #1 base clock	*/
	CGU_BASE_APB3,								/**< APB peripheral block #3 base clock	*/
	CGU_BASE_LCD,								/**< LCD base clock					*/
	CGU_BASE_ENET_CSR,
	CGU_BASE_SDIO,								/**< SDIO base clock				*/
	CGU_BASE_SSP0,								/**< SSP0 base clock				*/
	CGU_BASE_SSP1,								/**< SSP1 base clock				*/
	CGU_BASE_UART0,								/**< UART0 base clock				*/
	CGU_BASE_UART1,								/**< UART1 base clock				*/
	CGU_BASE_UART2,								/**< UART2 base clock				*/
	CGU_BASE_UART3,								/**< UART3 base clock				*/
	CGU_BASE_CLKOUT,							/**< CLKOUT base clock				*/
	CGU_BASE_APLL = CGU_BASE_CLKOUT + 5,
	CGU_BASE_OUT0,
	CGU_BASE_OUT1,
	CGU_ENTITY_NUM								/**< Number or clock source entity	*/
} CGU_ENTITY_T;

/*
 * @brief 	CGU PPL0 mode enumerate definition
 */
typedef enum {
	CGU_PLL0_MODE_1d = 0,
	CGU_PLL0_MODE_1c,
	CGU_PLL0_MODE_1b,
	CGU_PLL0_MODE_1a
}CGU_PLL0_MODE;

/*
 * @brief 	CGU peripheral enumerate definition
 */
typedef enum {
	CGU_PERIPHERAL_ADC0 = 0,					/**< ADC0 		*/
	CGU_PERIPHERAL_ADC1,						/**< ADC1 		*/
	CGU_PERIPHERAL_AES,							/**< AES		*/
//	CGU_PERIPHERAL_ALARMTIMER_CGU_RGU_RTC_WIC,
	CGU_PERIPHERAL_APB1_BUS,					/**< APB1 bus			*/
	CGU_PERIPHERAL_APB3_BUS,					/**< APB3 bus			*/
	CGU_PERIPHERAL_CAN,							/**< CAN 				*/
	CGU_PERIPHERAL_CREG,						/**< CREG				*/
	CGU_PERIPHERAL_DAC,							/**< DAC				*/
	CGU_PERIPHERAL_DMA,							/**< DMA				*/
	CGU_PERIPHERAL_EMC,							/**< EMC				*/
	CGU_PERIPHERAL_ETHERNET,					/**< Ethernet			*/
	CGU_PERIPHERAL_ETHERNET_TX, //HIDE			/**< Ethernet transmit 	*/
	CGU_PERIPHERAL_GPIO,						/**< GPIO				*/
	CGU_PERIPHERAL_I2C0,						/**< I2C0				*/
	CGU_PERIPHERAL_I2C1,						/**< I2C1				*/
	CGU_PERIPHERAL_I2S,							/**< I2S				*/
	CGU_PERIPHERAL_LCD,							/**< LCD				*/
	CGU_PERIPHERAL_M3CORE,						/**< ARM Cortex-M3 Core	*/
	CGU_PERIPHERAL_M3_BUS,						/**< ARM Cortex-M3 Bus	*/
	CGU_PERIPHERAL_MOTOCON,						/**< Motor Control 		*/
	CGU_PERIPHERAL_QEI,							/**< QEI				*/
	CGU_PERIPHERAL_RITIMER,						/**< RIT Timer			*/
	CGU_PERIPHERAL_SCT,							/**< SCT				*/
	CGU_PERIPHERAL_SCU,							/**< SCU				*/
	CGU_PERIPHERAL_SDIO,						/**< SDIO				*/
	CGU_PERIPHERAL_SPIFI,						/**< SPIFI				*/
	CGU_PERIPHERAL_SSP0,						/**< SSP0				*/
	CGU_PERIPHERAL_SSP1,						/**< SSP1				*/
	CGU_PERIPHERAL_TIMER0,						/**< TIMER 0 			*/
	CGU_PERIPHERAL_TIMER1,						/**< TIMER 1			*/
	CGU_PERIPHERAL_TIMER2,						/**< TIMER 2			*/
	CGU_PERIPHERAL_TIMER3,						/**< TIMER 3			*/
	CGU_PERIPHERAL_UART0,						/**< UART0				*/
	CGU_PERIPHERAL_UART1,						/**< UART1				*/
	CGU_PERIPHERAL_UART2,						/**< UART2				*/
	CGU_PERIPHERAL_UART3,						/**< UART3				*/
	CGU_PERIPHERAL_USB0,						/**< USB0				*/
	CGU_PERIPHERAL_USB1,						/**< USB1				*/
	CGU_PERIPHERAL_WWDT,						/**< WWDT				*/
	CGU_PERIPHERAL_NUM
} CGU_PERIPHERAL_T;

/**
 *  @brief	CGU error status enumerate definition
 */
typedef enum {
	CGU_ERROR_SUCCESS = 0,
	CGU_ERROR_CONNECT_TOGETHER,
	CGU_ERROR_INVALID_ENTITY,
	CGU_ERROR_INVALID_CLOCK_SOURCE,
	CGU_ERROR_INVALID_PARAM,
	CGU_ERROR_FREQ_OUTOF_RANGE
} CGU_ERROR;

/********************************************************************//**
* @brief CGU structure definitions
**********************************************************************/
/*
 * @brief	CGU peripheral clock structure
 */
typedef struct {
	uint8_t RegBaseEntity;						/**< Base register address 		*/
	uint16_t RegBranchOffset;					/**< Branch register offset		*/
	uint8_t PerBaseEntity;						/**< Base peripheral address	*/
	uint16_t PerBranchOffset;					/**< Base peripheral offset		*/
	uint8_t next;								/**< Pointer to next structure	*/
} CGU_PERIPHERAL_S;

/**
 * @}
 */


/* Public Functions ----------------------------------------------------------- */
/** @defgroup CGU_Public_Functions CGU Public Functions
 * @{
 */

/** Clock generate initialize/de-initialize */
uint32_t	CGU_Init(void);
uint32_t	CGU_DeInit(void);

/** Clock Generator and Clock Control */
uint32_t	CGU_ConfigPWR (CGU_PERIPHERAL_T PPType, FunctionalState en);
uint32_t	CGU_GetPCLKFrequency (CGU_PERIPHERAL_T Clock);

/** Clock Source and Base Clock operation */
uint32_t	CGU_SetXTALOSC(uint32_t ClockFrequency);
uint32_t	CGU_SetDIV(CGU_ENTITY_T SelectDivider, uint32_t divisor);
uint32_t	CGU_SetPLL0(void);
uint32_t	CGU_SetPLL1(uint32_t mult);
uint32_t	CGU_EnableEntity(CGU_ENTITY_T ClockEntity, uint32_t en);
uint32_t	CGU_EntityConnect(CGU_ENTITY_T ClockSource, CGU_ENTITY_T ClockEntity);
uint32_t	CGU_GetBaseStatus(CGU_ENTITY_T Base);
void		CGU_UpdateClock(void);
uint32_t	CGU_RealFrequencyCompare(CGU_ENTITY_T Clock, CGU_ENTITY_T CompareToClock, uint32_t *m, uint32_t *d);

/**
 * @}
 */


#ifdef __cplusplus
}
#endif

#endif /* lpc43xx_CGU_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
