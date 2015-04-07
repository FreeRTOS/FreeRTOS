/***********************************************************************//**
 * @file		lpc18xx_clkpwr.h
 * @brief		Contains all macro definitions and function prototypes
 * 				support for Clock and Power Control firmware library on LPC18xx
 * @version		1.0
 * @date		14. Dec. 2010
 * @author		NXP MCU SW Application Team
 **************************************************************************
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
 **************************************************************************/

/* Peripheral group ----------------------------------------------------------- */
/** @defgroup CLKPWR CLKPWR
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_CLKPWR_H_
#define LPC18XX_CLKPWR_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"

#ifdef __cplusplus
extern "C"
{
#endif

/* Public Macros -------------------------------------------------------------- */
/** @defgroup CLKPWR_Public_Macros CLKPWR Public Macros
 * @{
 */

typedef enum {
	/* Clock Source */
	CLKPWR_CLKSRC_32KHZ_OSC = 0,
	CLKPWR_CLKSRC_IRC,
	CLKPWR_CLKSRC_ENET_RX_CLK,
	CLKPWR_CLKSRC_ENET_TX_CLK,
	CLKPWR_CLKSRC_GP_CLKIN,
	CLKPWR_CLKSRC_TCK,
	CLKPWR_CLKSRC_XTAL_OSC,
	CLKPWR_CLKSRC_PLL0,
	CLKPWR_CLKSRC_PLL1,
	CLKPWR_CLKSRC_IDIVA = CLKPWR_CLKSRC_PLL1 + 3,
	CLKPWR_CLKSRC_IDIVB,
	CLKPWR_CLKSRC_IDIVC,
	CLKPWR_CLKSRC_IDIVD,
	CLKPWR_CLKSRC_IDIVE,

	/* Base */
	CLKPWR_BASE_SAFE,
	CLKPWR_BASE_USB0,
	CLKPWR_BASE_USB1 = CLKPWR_BASE_USB0 + 2,
	CLKPWR_BASE_M3,
	CLKPWR_BASE_SPIFI,
	//CLKPWR_BASE_SPI,
	CLKPWR_BASE_PHY_RX = CLKPWR_BASE_SPIFI + 2,
	CLKPWR_BASE_PHY_TX,
	CLKPWR_BASE_APB1,
	CLKPWR_BASE_APB3,
	CLKPWR_BASE_LCD,
	CLKPWR_BASE_SDIO = CLKPWR_BASE_LCD + 2,
	CLKPWR_BASE_SSP0,
	CLKPWR_BASE_SSP1,
	CLKPWR_BASE_UART0,
	CLKPWR_BASE_UART1,
	CLKPWR_BASE_UART2,
	CLKPWR_BASE_UART3,
	CLKPWR_BASE_CLKOUT,
	CLKPWR_ENTITY_NUM
} CLKPWR_ENTITY_T;

#define CLKPWR_CLKSRC_NUM (CLKPWR_CLKSRC_IDIVE+1)

typedef enum {
	CLKPWR_PLL0_MODE_1d = 0,
	CLKPWR_PLL0_MODE_1c,
	CLKPWR_PLL0_MODE_1b,
	CLKPWR_PLL0_MODE_1a,
}CLKPWR_PLL0_MODE;

typedef enum {
	CLKPWR_PERIPHERAL_ADC0 = 0,
	CLKPWR_PERIPHERAL_ADC1,
	CLKPWR_PERIPHERAL_AES,
//	CLKPWR_PERIPHERAL_ALARMTIMER_CGU_RGU_RTC_WIC,
	CLKPWR_PERIPHERAL_APB1_BUS,
	CLKPWR_PERIPHERAL_APB3_BUS,
	CLKPWR_PERIPHERAL_CAN,
	CLKPWR_PERIPHERAL_CREG,
	CLKPWR_PERIPHERAL_DAC,
	CLKPWR_PERIPHERAL_DMA,
	CLKPWR_PERIPHERAL_EMC,
	CLKPWR_PERIPHERAL_ETHERNET,
	CLKPWR_PERIPHERAL_ETHERNET_TX, //HIDE
	CLKPWR_PERIPHERAL_GPIO,
	CLKPWR_PERIPHERAL_I2C0,
	CLKPWR_PERIPHERAL_I2C1,
	CLKPWR_PERIPHERAL_I2S,
	CLKPWR_PERIPHERAL_LCD,
	CLKPWR_PERIPHERAL_M3CORE,
	CLKPWR_PERIPHERAL_M3_BUS,
	CLKPWR_PERIPHERAL_MOTOCON,
	CLKPWR_PERIPHERAL_QEI,
	CLKPWR_PERIPHERAL_RITIMER,
	CLKPWR_PERIPHERAL_SCT,
	CLKPWR_PERIPHERAL_SCU,
	CLKPWR_PERIPHERAL_SDIO,
	CLKPWR_PERIPHERAL_SPIFI,
	CLKPWR_PERIPHERAL_SSP0,
	CLKPWR_PERIPHERAL_SSP1,
	CLKPWR_PERIPHERAL_TIMER0,
	CLKPWR_PERIPHERAL_TIMER1,
	CLKPWR_PERIPHERAL_TIMER2,
	CLKPWR_PERIPHERAL_TIMER3,
	CLKPWR_PERIPHERAL_UART0,
	CLKPWR_PERIPHERAL_UART1,
	CLKPWR_PERIPHERAL_UART2,
	CLKPWR_PERIPHERAL_UART3,
	CLKPWR_PERIPHERAL_USB0,
	CLKPWR_PERIPHERAL_USB1,
	CLKPWR_PERIPHERAL_WWDT,
	CLKPWR_PERIPHERAL_NUM
} CLKPWR_PERIPHERAL_T;
//typedef CLKPWR_CLK_T CLKPWR_BASE_T;

typedef struct {
	uint8_t RegBaseEntity;
	uint16_t RegBranchOffset;
	uint8_t PerBaseEntity;
	uint16_t PerBranchOffset;
	uint8_t next;
} CLKPWR_PERIPHERAL_S;

typedef enum {
	CLKPWR_ERROR_SUCCESS = 0,
	CLKPWR_ERROR_CONNECT_TOGETHER,
	CLKPWR_ERROR_INVALID_ENTITY,
	CLKPWR_ERROR_INVALID_CLOCK_SOURCE,
	CLKPWR_ERROR_INVALID_PARAM,
	CLKPWR_ERROR_FREQ_OUTOF_RANGE
} CLKPWR_ERROR;

/* Branch clocks from CLKPWR_BASE_SAFE */

#define CLKPWR_ENTITY_NONE	CLKPWR_ENTITY_NUM

#define ISBITCLR(x,bit) ((x&(1<<bit))^(1<<bit))
#define ISBITSET(x,bit) (x&(1<<bit))
#define ISMASKSET(x,mask) (x&mask)

#define CLKPWR_CTRL_EN_MASK		1
#define CLKPWR_CTRL_SRC_MASK	(0xF<<24)
#define CLKPWR_CTRL_AUTOBLOCK_MASK	(1<<11)
#define CLKPWR_PLL1_FBSEL_MASK	(1<<6)
#define CLKPWR_PLL1_BYPASS_MASK	(1<<1)
#define CLKPWR_PLL1_DIRECT_MASK	(1<<7)

#define CLKPWR_SLEEP_MODE_DEEP_SLEEP	0x3F00AA
#define CLKPWR_SLEEP_MODE_POWER_DOWN	0x3FFCBA
#define CLKPWR_SLEEP_MODE_DEEP_POWER_DOWN	0x3FFF7F

/* Public Functions ----------------------------------------------------------- */
/** @defgroup CLKPWR_Public_Functions CLKPWR Public Functions
 * @{
 */
/* Clock Generator */

uint32_t	CLKPWR_ConfigPWR (CLKPWR_PERIPHERAL_T PPType, FunctionalState en);

uint32_t	CLKPWR_GetPCLKFrequency (CLKPWR_PERIPHERAL_T Clock);

/* Clock Source and Base Clock operation */
uint32_t	CLKPWR_SetXTALOSC(uint32_t ClockFrequency);
uint32_t	CLKPWR_SetDIV(CLKPWR_ENTITY_T SelectDivider, uint32_t divisor);
uint32_t	CLKPWR_SetPLL0(void);
uint32_t	CLKPWR_SetPLL1(uint32_t mult);
uint32_t	CLKPWR_EnableEntity(CLKPWR_ENTITY_T ClockEntity, uint32_t en);
uint32_t	CLKPWR_EntityConnect(CLKPWR_ENTITY_T ClockSource, CLKPWR_ENTITY_T ClockEntity);
uint32_t	CLKPWR_GetBaseStatus(CLKPWR_ENTITY_T Base);

void		CLKPWR_UpdateClock(void);
uint32_t	CLKPWR_RealFrequencyCompare(CLKPWR_ENTITY_T Clock, CLKPWR_ENTITY_T CompareToClock, uint32_t *m, uint32_t *d);

uint32_t	CLKPWR_Init(void);
uint32_t	CLKPWR_DeInit(void);

void CLKPWR_Sleep(void);
void CLKPWR_DeepSleep(void);
void CLKPWR_PowerDown(void);
void CLKPWR_DeepPowerDown(void);

/**
 * @}
 */


#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_CLKPWR_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
