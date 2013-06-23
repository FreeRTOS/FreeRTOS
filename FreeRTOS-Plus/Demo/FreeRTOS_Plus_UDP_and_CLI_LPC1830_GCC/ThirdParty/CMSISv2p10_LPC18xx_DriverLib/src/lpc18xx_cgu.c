/**********************************************************************
* $Id$		lpc18xx_cgu.c		2011-06-02
*//**
* @file		lpc18xx_cgu.c
* @brief	Contains all functions support for Clock Generation and Control
* 			firmware library on LPC18xx
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
/** @addtogroup CGU
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc_types.h"
#include "lpc18xx_scu.h"
#include "lpc18xx_cgu.h"

/** This define used to fix mistake when run with IAR compiler */
#ifdef __ICCARM__
#define CGU_BRANCH_STATUS_ENABLE_MASK  0x80000001
#else
#define CGU_BRANCH_STATUS_ENABLE_MASK  0x01
#endif

/*TODO List:
 * SET PLL0
 * UPDATE Clock from PLL0
 * SetDIV uncheck value
 * GetBaseStatus BASE_SAFE
 * */
/* Local definition */
#define CGU_ADDRESS32(x,y) (*(uint32_t*)((uint32_t)x+y))

/* Local Variable */
const int16_t CGU_Entity_ControlReg_Offset[CGU_ENTITY_NUM] = {
		-1,		//CGU_CLKSRC_32KHZ_OSC,
		-1,		//CGU_CLKSRC_IRC,
		-1,		//CGU_CLKSRC_ENET_RX_CLK,
		-1,		//CGU_CLKSRC_ENET_TX_CLK,
		-1,		//CGU_CLKSRC_GP_CLKIN,
		-1,		//CGU_CLKSRC_TCK,
		0x18,	//CGU_CLKSRC_XTAL_OSC,
		0x20,	//CGU_CLKSRC_PLL0,
		0x30,	//CGU_CLKSRC_PLL0_AUDIO **REV A**
		0x44,	//CGU_CLKSRC_PLL1,
		-1,		//CGU_CLKSRC_RESERVE,
		-1,		//CGU_CLKSRC_RESERVE,
		0x48,	//CGU_CLKSRC_IDIVA,,
		0x4C,	//CGU_CLKSRC_IDIVB,
		0x50,	//CGU_CLKSRC_IDIVC,
		0x54,	//CGU_CLKSRC_IDIVD,
		0x58,	//CGU_CLKSRC_IDIVE,

		0x5C,	//CGU_BASE_SAFE,
		0x60,	//CGU_BASE_USB0,
		-1,		//CGU_BASE_RESERVE,
		0x68,	//CGU_BASE_USB1,
		0x6C,	//CGU_BASE_M3,
		0x70,	//CGU_BASE_SPIFI,
		-1,		//CGU_BASE_RESERVE,
		0x78,	//CGU_BASE_PHY_RX,
		0x7C,	//CGU_BASE_PHY_TX,
		0x80,	//CGU_BASE_APB1,
		0x84,	//CGU_BASE_APB3,
		0x88,	//CGU_BASE_LCD,
		0X8C,	//CGU_BASE_ENET_CSR, **REV A**
		0x90,	//CGU_BASE_SDIO,
		0x94,	//CGU_BASE_SSP0,
		0x98,	//CGU_BASE_SSP1,
		0x9C,	//CGU_BASE_UART0,
		0xA0,	//CGU_BASE_UART1,
		0xA4,	//CGU_BASE_UART2,
		0xA8,	//CGU_BASE_UART3,
		0xAC,	//CGU_BASE_CLKOUT
		-1,
		-1,
		-1,
		-1,
		0xC0,	//CGU_BASE_APLL
		0xC4,	//CGU_BASE_OUT0
		0xC8	//CGU_BASE_OUT1
};

const uint8_t CGU_ConnectAlloc_Tbl[CGU_CLKSRC_NUM][CGU_ENTITY_NUM] = {
//       3 I E E G T X P P P x x D D D D D S U x U M S x P P A A L E S S S U U U U C x x x x A O O
//       2 R R T P C T L L L     I I I I I A S   S 3 P   H H P P C N D S S R R R R O         P U U
//         C X X I K A 0 A 1     A B C D E F B   B   F   RxTx1 3 D T I 0 1 0 1 2 3           L T T
		{0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_32KHZ_OSC = 0,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,1,1,1,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_IRC,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_ENET_RX_CLK,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_ENET_TX_CLK,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_GP_CLKIN,*/
		{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0},/*CGU_CLKSRC_TCK,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_XTAL_OSC,*/
		{0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,1},/*CGU_CLKSRC_PLL0,*/
		{0,0,0,0,0,0,0,0,0,1,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_PLL0_AUDIO,*/
		{0,0,0,0,0,0,0,1,1,0,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_PLL1,*/
		{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
		{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
		{0,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,1,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_IDIVA = CGU_CLKSRC_PLL1 + 3,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_IDIVB,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_IDIVC,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1},/*CGU_CLKSRC_IDIVD,*/
		{0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,1,1,1}/*CGU_CLKSRC_IDIVE,*/
};

const CGU_PERIPHERAL_S CGU_PERIPHERAL_Info[CGU_PERIPHERAL_NUM] = {
	/*	Register Clock			|	Peripheral Clock
		 |	BASE	|		BRANCH	|	BASE		|	BRANCH		*/
		{CGU_BASE_APB3,	0x1118, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_ADC0,
		{CGU_BASE_APB3,	0x1120, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_ADC1,
		{CGU_BASE_M3,	0x1460, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_AES,
		////	CGU_PERIPHERAL_ALARMTIMER_CGU_RGU_RTC_WIC,
		{CGU_BASE_APB1,	0x1200, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_APB1_BUS,
		{CGU_BASE_APB3,	0x1100, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_APB3_BUS,
		{CGU_BASE_APB3,	0x1128, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_CAN0,
		{CGU_BASE_M3,	0x1538, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_CREG,
		{CGU_BASE_APB3,	0x1110, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_DAC,
		{CGU_BASE_M3,	0x1440, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_DMA,
		{CGU_BASE_M3,	0x1430, CGU_BASE_M3,		0x1478, 0},//CGU_PERIPHERAL_EMC,
		{CGU_BASE_M3,	0x1420, CGU_BASE_PHY_RX,	0x0000, CGU_PERIPHERAL_ETHERNET_TX},//CGU_PERIPHERAL_ETHERNET,
		{CGU_ENTITY_NONE,0x0000, CGU_BASE_PHY_TX,	0x0000, 0},//CGU_PERIPHERAL_ETHERNET_TX
		{CGU_BASE_M3,	0x1410, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_GPIO,
		{CGU_BASE_APB1,	0x1210, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_I2C0,
		{CGU_BASE_APB3,	0x1108, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_I2C1,
		{CGU_BASE_APB1,	0x1218, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_I2S,
		{CGU_BASE_M3,	0x1418, CGU_BASE_LCD,	0x0000, 0},//CGU_PERIPHERAL_LCD,
		{CGU_BASE_M3,	0x1448, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_M3CORE,
		{CGU_BASE_M3,	0x1400, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_M3_BUS,
		{CGU_BASE_APB1,	0x1208, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_MOTOCON,
		{CGU_BASE_M3,	0x1630, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_QEI,
		{CGU_BASE_M3,	0x1600, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_RITIMER,
		{CGU_BASE_M3,	0x1468, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_SCT,
		{CGU_BASE_M3,	0x1530, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_SCU,
		{CGU_BASE_M3,	0x1438, CGU_BASE_SDIO,	0x2800, 0},//CGU_PERIPHERAL_SDIO,
		{CGU_BASE_M3,	0x1408, CGU_BASE_SPIFI,	0x1300, 0},//CGU_PERIPHERAL_SPIFI,
		{CGU_BASE_M3,	0x1518, CGU_BASE_SSP0,	0x2700, 0},//CGU_PERIPHERAL_SSP0,
		{CGU_BASE_M3,	0x1628, CGU_BASE_SSP1,	0x2600, 0},//CGU_PERIPHERAL_SSP1,
		{CGU_BASE_M3,	0x1520, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_TIMER0,
		{CGU_BASE_M3,	0x1528, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_TIMER1,
		{CGU_BASE_M3,	0x1618, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_TIMER2,
		{CGU_BASE_M3,	0x1620, CGU_ENTITY_NONE,	0x0000, 0},//CGU_PERIPHERAL_TIMER3,
		{CGU_BASE_M3,	0x1508, CGU_BASE_UART0,	0x2500, 0},//CGU_PERIPHERAL_UART0,
		{CGU_BASE_M3,	0x1510, CGU_BASE_UART1,	0x2400, 0},//CGU_PERIPHERAL_UART1,
		{CGU_BASE_M3,	0x1608, CGU_BASE_UART2,	0x2300, 0},//CGU_PERIPHERAL_UART2,
		{CGU_BASE_M3,	0x1610, CGU_BASE_UART3,	0x2200, 0},//CGU_PERIPHERAL_UART3,
		{CGU_BASE_M3,	0x1428, CGU_BASE_USB0,	0x1800, 0},//CGU_PERIPHERAL_USB0,
		{CGU_BASE_M3,	0x1470, CGU_BASE_USB1,	0x1900, 0},//CGU_PERIPHERAL_USB1,
		{CGU_BASE_M3,	0x1500, CGU_BASE_SAFE,	0x0000, 0},//CGU_PERIPHERAL_WWDT,
};

uint32_t CGU_ClockSourceFrequency[CGU_CLKSRC_NUM] = {0,12000000,0,0,0,0, 0, 480000000,0,0,0,0,0,0,0,0,0};

#define CGU_CGU_ADDR	((uint32_t)LPC_CGU)
#define CGU_REG_BASE_CTRL(x) (*(uint32_t*)(CGU_CGU_ADDR+CGU_Entity_ControlReg_Offset[CGU_PERIPHERAL_Info[x].RegBaseEntity]))
#define CGU_REG_BRANCH_CTRL(x) (*(uint32_t*)(CGU_CGU_ADDR+CGU_PERIPHERAL_Info[x].RegBranchOffset))
#define CGU_REG_BRANCH_STATUS(x) (*(uint32_t*)(CGU_CGU_ADDR+CGU_PERIPHERAL_Info[x].RegBranchOffset+4))

#define CGU_PER_BASE_CTRL(x) (*(uint32_t*)(CGU_CGU_ADDR+CGU_Entity_ControlReg_Offset[CGU_PERIPHERAL_Info[x].PerBaseEntity]))
#define CGU_PER_BRANCH_CTRL(x) (*(uint32_t*)(CGU_CGU_ADDR+CGU_PERIPHERAL_Info[x].PerBranchOffset))
#define CGU_PER_BRANCH_STATUS(x) (*(uint32_t*)(CGU_CGU_ADDR+CGU_PERIPHERAL_Info[x].PerBranchOffset+4))


/*********************************************************************//**
 * @brief		Initialize default clock for LPC1800 Eval board
 * @param[in]	None
 * @return 		Initialize status, could be:
 * 					- CGU_ERROR_SUCCESS: successful
 * 					- Other: error
 **********************************************************************/
uint32_t	CGU_Init(void){
	CGU_SetXTALOSC(12000000);
	CGU_EnableEntity(CGU_CLKSRC_XTAL_OSC, ENABLE);
	CGU_EntityConnect(CGU_CLKSRC_XTAL_OSC, CGU_CLKSRC_PLL1);
	// Disable PLL1 CPU hang???
	//CGU_EnableEntity(CGU_CLKSRC_PLL1, DISABLE);
	CGU_SetPLL1(10);
	CGU_EnableEntity(CGU_CLKSRC_PLL1, ENABLE);
	CGU_EntityConnect(CGU_CLKSRC_PLL1, CGU_BASE_M3);
	CGU_UpdateClock();
	return 0;
}

/*********************************************************************//**
 * @brief		Configure power for individual peripheral
 * @param[in]	PPType	peripheral type, should be:
 * 					- CGU_PERIPHERAL_ADC0		:ADC0
 * 					- CGU_PERIPHERAL_ADC1		:ADC1
 * 					- CGU_PERIPHERAL_AES		:AES
 * 					- CGU_PERIPHERAL_APB1_BUS	:APB1 bus
 * 					- CGU_PERIPHERAL_APB3_BUS	:APB3 bus
 * 					- CGU_PERIPHERAL_CAN		:CAN
 * 					- CGU_PERIPHERAL_CREG		:CREG
 * 					- CGU_PERIPHERAL_DAC		:DAC
 * 					- CGU_PERIPHERAL_DMA		:DMA
 * 					- CGU_PERIPHERAL_EMC		:EMC
 * 					- CGU_PERIPHERAL_ETHERNET	:ETHERNET
 * 					- CGU_PERIPHERAL_GPIO		:GPIO
 * 					- CGU_PERIPHERAL_I2C0		:I2C0
 * 					- CGU_PERIPHERAL_I2C1		:I2C1
 * 					- CGU_PERIPHERAL_I2S		:I2S
 * 					- CGU_PERIPHERAL_LCD		:LCD
 * 					- CGU_PERIPHERAL_M3CORE		:M3 core
 * 					- CGU_PERIPHERAL_M3_BUS		:M3 bus
 * 					- CGU_PERIPHERAL_MOTOCON	:Motor control
 * 					- CGU_PERIPHERAL_QEI		:QEI
 * 					- CGU_PERIPHERAL_RITIMER	:RIT timer
 * 					- CGU_PERIPHERAL_SCT		:SCT
 * 					- CGU_PERIPHERAL_SCU		:SCU
 * 					- CGU_PERIPHERAL_SDIO		:SDIO
 * 					- CGU_PERIPHERAL_SPIFI		:SPIFI
 * 					- CGU_PERIPHERAL_SSP0		:SSP0
 * 					- CGU_PERIPHERAL_SSP1		:SSP1
 * 					- CGU_PERIPHERAL_TIMER0		:TIMER0
 * 					- CGU_PERIPHERAL_TIMER1		:TIMER1
 * 					- CGU_PERIPHERAL_TIMER2		:TIMER2
 * 					- CGU_PERIPHERAL_TIMER3		:TIMER3
 * 					- CGU_PERIPHERAL_UART0		:UART0
 * 					- CGU_PERIPHERAL_UART1		:UART1
 * 					- CGU_PERIPHERAL_UART2		:UART2
 * 					- CGU_PERIPHERAL_UART3		:UART3
 * 					- CGU_PERIPHERAL_USB0		:USB0
 * 					- CGU_PERIPHERAL_USB1		:USB1
 * 					- CGU_PERIPHERAL_WWDT		:WWDT
 * @param[in]	en status, should be:
 * 					- ENABLE: Enable power
 * 					- DISABLE: Disable power
 * @return 		Configure status, could be:
 * 					- CGU_ERROR_SUCCESS: successful
 * 					- Other: error
 **********************************************************************/
uint32_t CGU_ConfigPWR (CGU_PERIPHERAL_T PPType,  FunctionalState en){
	if(PPType >= CGU_PERIPHERAL_WWDT && PPType <= CGU_PERIPHERAL_ADC0)
		return CGU_ERROR_INVALID_PARAM;
	if(en == DISABLE){/* Going to disable clock */
		/*Get Reg branch status */
		if(CGU_PERIPHERAL_Info[PPType].RegBranchOffset!= 0 &&
				CGU_REG_BRANCH_STATUS(PPType) & 1){
			CGU_REG_BRANCH_CTRL(PPType) &= ~1; /* Disable branch clock */
			while(CGU_REG_BRANCH_STATUS(PPType) & 1);
		}
		/* GetBase Status*/
		if((CGU_PERIPHERAL_Info[PPType].RegBaseEntity!=CGU_ENTITY_NONE) &&
			CGU_GetBaseStatus((CGU_ENTITY_T)CGU_PERIPHERAL_Info[PPType].RegBaseEntity) == 0){
			/* Disable Base */
			CGU_EnableEntity((CGU_ENTITY_T)CGU_PERIPHERAL_Info[PPType].RegBaseEntity,0);
		}

		/* Same for Peripheral */
		if((CGU_PERIPHERAL_Info[PPType].PerBranchOffset!= 0) && (CGU_PER_BRANCH_STATUS(PPType) & CGU_BRANCH_STATUS_ENABLE_MASK)){
			CGU_PER_BRANCH_CTRL(PPType) &= ~1; /* Disable branch clock */
			while(CGU_PER_BRANCH_STATUS(PPType) & CGU_BRANCH_STATUS_ENABLE_MASK);
		}
		/* GetBase Status*/
		if((CGU_PERIPHERAL_Info[PPType].PerBaseEntity!=CGU_ENTITY_NONE) &&
			CGU_GetBaseStatus((CGU_ENTITY_T)CGU_PERIPHERAL_Info[PPType].PerBaseEntity) == 0){
			/* Disable Base */
			CGU_EnableEntity((CGU_ENTITY_T)CGU_PERIPHERAL_Info[PPType].PerBaseEntity,0);
		}
	}else{
		/* enable */
		/* GetBase Status*/
		if((CGU_PERIPHERAL_Info[PPType].RegBaseEntity!=CGU_ENTITY_NONE) && CGU_REG_BASE_CTRL(PPType) & CGU_BRANCH_STATUS_ENABLE_MASK){
			/* Enable Base */
			CGU_EnableEntity((CGU_ENTITY_T)CGU_PERIPHERAL_Info[PPType].RegBaseEntity, 1);
		}
		/*Get Reg branch status */
		if((CGU_PERIPHERAL_Info[PPType].RegBranchOffset!= 0) && !(CGU_REG_BRANCH_STATUS(PPType) & CGU_BRANCH_STATUS_ENABLE_MASK)){
			CGU_REG_BRANCH_CTRL(PPType) |= 1; /* Enable branch clock */
			while(!(CGU_REG_BRANCH_STATUS(PPType) & CGU_BRANCH_STATUS_ENABLE_MASK));
		}

		/* Same for Peripheral */
		/* GetBase Status*/
		if((CGU_PERIPHERAL_Info[PPType].PerBaseEntity != CGU_ENTITY_NONE) &&
				(CGU_PER_BASE_CTRL(PPType) & 1)){
			/* Enable Base */
			CGU_EnableEntity((CGU_ENTITY_T)CGU_PERIPHERAL_Info[PPType].PerBaseEntity, 1);
		}
		/*Get Reg branch status */
		if((CGU_PERIPHERAL_Info[PPType].PerBranchOffset!= 0) && !(CGU_PER_BRANCH_STATUS(PPType) & CGU_BRANCH_STATUS_ENABLE_MASK)){
			CGU_PER_BRANCH_CTRL(PPType) |= 1; /* Enable branch clock */
			while(!(CGU_PER_BRANCH_STATUS(PPType) & CGU_BRANCH_STATUS_ENABLE_MASK));
		}

	}

	if(CGU_PERIPHERAL_Info[PPType].next){
		return CGU_ConfigPWR((CGU_PERIPHERAL_T)CGU_PERIPHERAL_Info[PPType].next, en);
	}
	return CGU_ERROR_SUCCESS;
}


/*********************************************************************//**
 * @brief		Get peripheral clock frequency
 * @param[in]	Clock	Peripheral type, should be:
 * 					- CGU_PERIPHERAL_ADC0		:ADC0
 * 					- CGU_PERIPHERAL_ADC1		:ADC1
 * 					- CGU_PERIPHERAL_AES		:AES
 * 					- CGU_PERIPHERAL_APB1_BUS	:APB1 bus
 * 					- CGU_PERIPHERAL_APB3_BUS	:APB3 bus
 * 					- CGU_PERIPHERAL_CAN		:CAN
 * 					- CGU_PERIPHERAL_CREG		:CREG
 * 					- CGU_PERIPHERAL_DAC		:DAC
 * 					- CGU_PERIPHERAL_DMA		:DMA
 * 					- CGU_PERIPHERAL_EMC		:EMC
 * 					- CGU_PERIPHERAL_ETHERNET	:ETHERNET
 * 					- CGU_PERIPHERAL_GPIO		:GPIO
 * 					- CGU_PERIPHERAL_I2C0		:I2C0
 * 					- CGU_PERIPHERAL_I2C1		:I2C1
 * 					- CGU_PERIPHERAL_I2S		:I2S
 * 					- CGU_PERIPHERAL_LCD		:LCD
 * 					- CGU_PERIPHERAL_M3CORE		:M3 core
 * 					- CGU_PERIPHERAL_M3_BUS		:M3 bus
 * 					- CGU_PERIPHERAL_MOTOCON	:Motor control
 * 					- CGU_PERIPHERAL_QEI		:QEI
 * 					- CGU_PERIPHERAL_RITIMER	:RIT timer
 * 					- CGU_PERIPHERAL_SCT		:SCT
 * 					- CGU_PERIPHERAL_SCU		:SCU
 * 					- CGU_PERIPHERAL_SDIO		:SDIO
 * 					- CGU_PERIPHERAL_SPIFI		:SPIFI
 * 					- CGU_PERIPHERAL_SSP0		:SSP0
 * 					- CGU_PERIPHERAL_SSP1		:SSP1
 * 					- CGU_PERIPHERAL_TIMER0		:TIMER0
 * 					- CGU_PERIPHERAL_TIMER1		:TIMER1
 * 					- CGU_PERIPHERAL_TIMER2		:TIMER2
 * 					- CGU_PERIPHERAL_TIMER3		:TIMER3
 * 					- CGU_PERIPHERAL_UART0		:UART0
 * 					- CGU_PERIPHERAL_UART1		:UART1
 * 					- CGU_PERIPHERAL_UART2		:UART2
 * 					- CGU_PERIPHERAL_UART3		:UART3
 * 					- CGU_PERIPHERAL_USB0		:USB0
 * 					- CGU_PERIPHERAL_USB1		:USB1
 * 					- CGU_PERIPHERAL_WWDT		:WWDT
 * @return 		Return frequently value
 **********************************************************************/
uint32_t CGU_GetPCLKFrequency (CGU_PERIPHERAL_T Clock){
	uint32_t ClkSrc;
	if(Clock >= CGU_PERIPHERAL_WWDT && Clock <= CGU_PERIPHERAL_ADC0)
		return CGU_ERROR_INVALID_PARAM;

	if(CGU_PERIPHERAL_Info[Clock].PerBaseEntity != CGU_ENTITY_NONE){
		/* Get Base Clock Source */
		ClkSrc = (CGU_PER_BASE_CTRL(Clock) & CGU_CTRL_SRC_MASK) >> 24;
		/* GetBase Status*/
		if(CGU_PER_BASE_CTRL(Clock) & 1)
			return 0;
		/* check Branch if it is enabled */
		if((CGU_PERIPHERAL_Info[Clock].PerBranchOffset!= 0) && !(CGU_PER_BRANCH_STATUS(Clock) & CGU_BRANCH_STATUS_ENABLE_MASK)) return 0;
	}else{
		if(CGU_REG_BASE_CTRL(Clock) & 1)	return 0;
		ClkSrc = (CGU_REG_BASE_CTRL(Clock) & CGU_CTRL_SRC_MASK) >> 24;
		/* check Branch if it is enabled */
		if((CGU_PERIPHERAL_Info[Clock].RegBranchOffset!= 0) && !(CGU_REG_BRANCH_STATUS(Clock) & CGU_BRANCH_STATUS_ENABLE_MASK)) return 0;
	}
	return CGU_ClockSourceFrequency[ClkSrc];
}


/*********************************************************************//**
 * @brief		Update clock
 * @param[in]	None
 * @return 		None
 **********************************************************************/
void CGU_UpdateClock(void){
	uint32_t ClkSrc;
	uint32_t div;
	uint32_t divisor;
	int32_t RegOffset;
	/* 32OSC */
	if(ISBITSET(LPC_CREG->CREG0,1) && ISBITCLR(LPC_CREG->CREG0,3))
		CGU_ClockSourceFrequency[CGU_CLKSRC_32KHZ_OSC] = 32768;
	else
		CGU_ClockSourceFrequency[CGU_CLKSRC_32KHZ_OSC] = 0;
	/*PLL0*/
	/* PLL1 */
	if(ISBITCLR(LPC_CGU->PLL1_CTRL,1) /* Enabled */
			&& (LPC_CGU->PLL1_STAT&1)){ /* Locked? */
		ClkSrc = (LPC_CGU->PLL1_CTRL & CGU_CTRL_SRC_MASK)>>24;
		CGU_ClockSourceFrequency[CGU_CLKSRC_PLL1] = CGU_ClockSourceFrequency[ClkSrc] *
															(((LPC_CGU->PLL1_CTRL>>16)&0xFF)+1);
	}else
		CGU_ClockSourceFrequency[CGU_CLKSRC_PLL1] = 0;

	/* DIV */
	for(div = CGU_CLKSRC_IDIVA; div <= CGU_CLKSRC_IDIVE; div++){
		RegOffset = CGU_Entity_ControlReg_Offset[div];
		if(ISBITCLR(CGU_ADDRESS32(LPC_CGU,RegOffset),1)){
			ClkSrc = (CGU_ADDRESS32(LPC_CGU,RegOffset) & CGU_CTRL_SRC_MASK) >> 24;
			divisor = (CGU_ADDRESS32(LPC_CGU,RegOffset)>>2) & 0xFF;
			divisor ++;
			CGU_ClockSourceFrequency[div] = CGU_ClockSourceFrequency[ClkSrc] / divisor;
		}else
			CGU_ClockSourceFrequency[div] = 0;
	}
}

/*********************************************************************//**
 * @brief		Set XTAL oscillator value
 * @param[in]	ClockFrequency	XTAL Frequency value
 * @return 		Setting status, could be:
 * 					- CGU_ERROR_SUCCESS: successful
 * 					- CGU_ERROR_FREQ_OUTOF_RANGE: XTAL value set is out of range
 **********************************************************************/
uint32_t	CGU_SetXTALOSC(uint32_t ClockFrequency){
	if(ClockFrequency < 15000000){
		LPC_CGU->XTAL_OSC_CTRL &= ~(1<<2);
	}else if(ClockFrequency < 25000000){
		LPC_CGU->XTAL_OSC_CTRL |= (1<<2);
	}else
		return CGU_ERROR_FREQ_OUTOF_RANGE;

	CGU_ClockSourceFrequency[CGU_CLKSRC_XTAL_OSC] = ClockFrequency;
	return CGU_ERROR_SUCCESS;
}


/*********************************************************************//**
 * @brief		Set clock divider
 * @param[in]	SelectDivider	Clock source, should be:
 * 					- CGU_CLKSRC_IDIVA	:Integer divider register A
 * 					- CGU_CLKSRC_IDIVB	:Integer divider register B
 * 					- CGU_CLKSRC_IDIVC	:Integer divider register C
 * 					- CGU_CLKSRC_IDIVD	:Integer divider register D
 * 					- CGU_CLKSRC_IDIVE	:Integer divider register E
 * @param[in]	divisor	Divisor value, should be: 0..255
 * @return 		Setting status, could be:
 * 					- CGU_ERROR_SUCCESS: successful
 * 					- CGU_ERROR_INVALID_ENTITY: Invalid entity
 **********************************************************************/
/* divisor number must >=1*/
uint32_t	CGU_SetDIV(CGU_ENTITY_T SelectDivider, uint32_t divisor){
	int32_t RegOffset;
	uint32_t tempReg;
	if(SelectDivider>=CGU_CLKSRC_IDIVA && SelectDivider<=CGU_CLKSRC_IDIVE){
		RegOffset = CGU_Entity_ControlReg_Offset[SelectDivider];
		if(RegOffset == -1) return CGU_ERROR_INVALID_ENTITY;
		tempReg = CGU_ADDRESS32(LPC_CGU,RegOffset);
		tempReg &= ~(0xFF<<2);
		tempReg |= ((divisor-1)&0xFF)<<2;
		CGU_ADDRESS32(LPC_CGU,RegOffset) = tempReg;
		return CGU_ERROR_SUCCESS;
	}
	return CGU_ERROR_INVALID_ENTITY;
}

/*********************************************************************//**
 * @brief		Enable clock entity
 * @param[in]	ClockEntity	Clock entity, should be:
 * 					- CGU_CLKSRC_32KHZ_OSC		:32Khz oscillator
 * 					- CGU_CLKSRC_IRC			:IRC clock
 * 					- CGU_CLKSRC_ENET_RX_CLK	:Ethernet receive clock
 * 					- CGU_CLKSRC_ENET_TX_CLK	:Ethernet transmit clock
 * 					- CGU_CLKSRC_GP_CLKIN		:General purpose input clock
 * 					- CGU_CLKSRC_XTAL_OSC		:Crystal oscillator
 * 					- CGU_CLKSRC_PLL0			:PLL0 clock
 * 					- CGU_CLKSRC_PLL1			:PLL1 clock
 * 					- CGU_CLKSRC_IDIVA			:Integer divider register A
 * 					- CGU_CLKSRC_IDIVB			:Integer divider register B
 * 					- CGU_CLKSRC_IDIVC			:Integer divider register C
 * 					- CGU_CLKSRC_IDIVD			:Integer divider register D
 * 					- CGU_CLKSRC_IDIVE			:Integer divider register E
 * 					- CGU_BASE_SAFE				:Base safe clock (always on)for WDT
 * 					- CGU_BASE_USB0				:Base clock for USB0
 * 					- CGU_BASE_USB1				:Base clock for USB1
 * 					- CGU_BASE_M3				:System base clock for ARM Cortex-M3 core
 * 												 and APB peripheral blocks #0 and #2
 * 					- CGU_BASE_SPIFI			:Base clock for SPIFI
 * 					- CGU_BASE_PHY_RX			:Base clock for Ethernet PHY Rx
 * 					- CGU_BASE_PHY_TX			:Base clock for Ethernet PHY Tx
 * 					- CGU_BASE_APB1				:Base clock for APB peripheral block #1
 * 					- CGU_BASE_APB3				:Base clock for APB peripheral block #3
 * 					- CGU_BASE_LCD				:Base clock for LCD
 * 					- CGU_BASE_SDIO				:Base clock for SDIO card reader
 * 					- CGU_BASE_SSP0				:Base clock for SSP0
 * 					- CGU_BASE_SSP1				:Base clock for SSP1
 * 					- CGU_BASE_UART0			:Base clock for UART0
 * 					- CGU_BASE_UART1			:Base clock for UART1
 * 					- CGU_BASE_UART2			:Base clock for UART2
 * 					- CGU_BASE_UART3			:Base clock for UART3
 * 					- CGU_BASE_CLKOUT			:Base clock for CLKOUT pin
 * @param[in]	en status, should be:
 * 					- ENABLE: Enable power
 * 					- DISABLE: Disable power
 * @return 		Setting status, could be:
 * 					- CGU_ERROR_SUCCESS: successful
 * 					- CGU_ERROR_INVALID_ENTITY: Invalid entity
 **********************************************************************/
uint32_t CGU_EnableEntity(CGU_ENTITY_T ClockEntity, uint32_t en){
	int32_t RegOffset;
	int32_t i;
	if(ClockEntity == CGU_CLKSRC_32KHZ_OSC){
		if(en){
			LPC_CREG->CREG0 &= ~((1<<3)|(1<<2));
			LPC_CREG->CREG0 |= (1<<1)|(1<<0);
		}else{
			LPC_CREG->CREG0 &= ~((1<<1)|(1<<0));
			LPC_CREG->CREG0 |= (1<<3);
		}
		for(i = 0;i<1000000;i++);

	}else if(ClockEntity == CGU_CLKSRC_ENET_RX_CLK){
		scu_pinmux(0xC ,0 , MD_PLN, FUNC3);

	}else if(ClockEntity == CGU_CLKSRC_ENET_TX_CLK){
		scu_pinmux(0x1 ,19 , MD_PLN, FUNC0);

	}else if(ClockEntity == CGU_CLKSRC_GP_CLKIN){

	}else if(ClockEntity == CGU_CLKSRC_TCK){

	}else if(ClockEntity == CGU_CLKSRC_XTAL_OSC){
		if(!en)
			LPC_CGU->XTAL_OSC_CTRL |= CGU_CTRL_EN_MASK;
		else
			LPC_CGU->XTAL_OSC_CTRL &= ~CGU_CTRL_EN_MASK;
		/*Delay for stable clock*/
		for(i = 0;i<1000000;i++);

	}else{
		RegOffset = CGU_Entity_ControlReg_Offset[ClockEntity];
		if(RegOffset == -1) return CGU_ERROR_INVALID_ENTITY;
		if(!en){
			CGU_ADDRESS32(CGU_CGU_ADDR,RegOffset) |= CGU_CTRL_EN_MASK;
		}else{
			CGU_ADDRESS32(CGU_CGU_ADDR,RegOffset) &= ~CGU_CTRL_EN_MASK;
			/*if PLL is selected check if it is locked */
			if(ClockEntity == CGU_CLKSRC_PLL0){
				while((LPC_CGU->PLL0USB_STAT&1) == 0x0);
			}
			if(ClockEntity == CGU_CLKSRC_PLL1){
				while((LPC_CGU->PLL1_STAT&1) == 0x0);
				/*post check lock status */
				if(!(LPC_CGU->PLL1_STAT&1))
					while(1);
			}
		}
	}
	return CGU_ERROR_SUCCESS;
}

/*********************************************************************//**
 * @brief		Connect entity clock source
 * @param[in]	ClockSource	Clock source, should be:
 * 					- CGU_CLKSRC_32KHZ_OSC		:32Khz oscillator
 * 					- CGU_CLKSRC_IRC			:IRC clock
 * 					- CGU_CLKSRC_ENET_RX_CLK	:Ethernet receive clock
 * 					- CGU_CLKSRC_ENET_TX_CLK	:Ethernet transmit clock
 * 					- CGU_CLKSRC_GP_CLKIN		:General purpose input clock
 * 					- CGU_CLKSRC_XTAL_OSC		:Crystal oscillator
 * 					- CGU_CLKSRC_PLL0			:PLL0 clock
 * 					- CGU_CLKSRC_PLL1			:PLL1 clock
 * 					- CGU_CLKSRC_IDIVA			:Integer divider register A
 * 					- CGU_CLKSRC_IDIVB			:Integer divider register B
 * 					- CGU_CLKSRC_IDIVC			:Integer divider register C
 * 					- CGU_CLKSRC_IDIVD			:Integer divider register D
 * 					- CGU_CLKSRC_IDIVE			:Integer divider register E
 * @param[in]	ClockEntity	Clock entity, should be:
 * 					- CGU_CLKSRC_PLL0			:PLL0 clock
 * 					- CGU_CLKSRC_PLL1			:PLL1 clock
 * 					- CGU_CLKSRC_IDIVA			:Integer divider register A
 * 					- CGU_CLKSRC_IDIVB			:Integer divider register B
 * 					- CGU_CLKSRC_IDIVC			:Integer divider register C
 * 					- CGU_CLKSRC_IDIVD			:Integer divider register D
 * 					- CGU_CLKSRC_IDIVE			:Integer divider register E
 * 					- CGU_BASE_SAFE				:Base safe clock (always on)for WDT
 * 					- CGU_BASE_USB0				:Base clock for USB0
 * 					- CGU_BASE_USB1				:Base clock for USB1
 * 					- CGU_BASE_M3				:System base clock for ARM Cortex-M3 core
 * 												 and APB peripheral blocks #0 and #2
 * 					- CGU_BASE_SPIFI			:Base clock for SPIFI
 * 					- CGU_BASE_PHY_RX			:Base clock for Ethernet PHY Rx
 * 					- CGU_BASE_PHY_TX			:Base clock for Ethernet PHY Tx
 * 					- CGU_BASE_APB1				:Base clock for APB peripheral block #1
 * 					- CGU_BASE_APB3				:Base clock for APB peripheral block #3
 * 					- CGU_BASE_LCD				:Base clock for LCD
 * 					- CGU_BASE_SDIO				:Base clock for SDIO card reader
 * 					- CGU_BASE_SSP0				:Base clock for SSP0
 * 					- CGU_BASE_SSP1				:Base clock for SSP1
 * 					- CGU_BASE_UART0			:Base clock for UART0
 * 					- CGU_BASE_UART1			:Base clock for UART1
 * 					- CGU_BASE_UART2			:Base clock for UART2
 * 					- CGU_BASE_UART3			:Base clock for UART3
 * 					- CGU_BASE_CLKOUT			:Base clock for CLKOUT pin
 * @return 		Setting status, could be:
 * 					- CGU_ERROR_SUCCESS: successful
 * 					- CGU_ERROR_CONNECT_TOGETHER: Error when 2 clock source connect together
 * 					- CGU_ERROR_INVALID_CLOCK_SOURCE: Invalid clock source error
 * 					- CGU_ERROR_INVALID_ENTITY: Invalid entity error
 **********************************************************************/
/* Connect one entity into clock source */
uint32_t CGU_EntityConnect(CGU_ENTITY_T ClockSource, CGU_ENTITY_T ClockEntity){
	int32_t RegOffset;
	uint32_t tempReg;

	if(ClockSource > CGU_CLKSRC_IDIVE)
		return CGU_ERROR_INVALID_CLOCK_SOURCE;

	if(ClockEntity >= CGU_CLKSRC_PLL0 && ClockEntity <= CGU_BASE_CLKOUT){
		if(CGU_ConnectAlloc_Tbl[ClockSource][ClockEntity]){
			RegOffset = CGU_Entity_ControlReg_Offset[ClockSource];
			if(RegOffset != -1){
				if(ClockEntity<=CGU_CLKSRC_IDIVE &&
					ClockEntity>=CGU_CLKSRC_PLL0)
				{
					//RegOffset = (CGU_ADDRESS32(LPC_CGU,RegOffset)>>24)&0xF;
					if(((CGU_ADDRESS32(LPC_CGU,RegOffset)>>24)& 0xF) == ClockEntity)
						return CGU_ERROR_CONNECT_TOGETHER;
				}
			}
			RegOffset = CGU_Entity_ControlReg_Offset[ClockEntity];
			if(RegOffset == -1) return CGU_ERROR_INVALID_ENTITY;
			tempReg = CGU_ADDRESS32(LPC_CGU,RegOffset);
			tempReg &= ~CGU_CTRL_SRC_MASK;
			tempReg |= ClockSource<<24 | CGU_CTRL_AUTOBLOCK_MASK;
			CGU_ADDRESS32(LPC_CGU,RegOffset) = tempReg;
			return CGU_ERROR_SUCCESS;
		}else
			return CGU_ERROR_INVALID_CLOCK_SOURCE;
	}else
		return CGU_ERROR_INVALID_ENTITY;
}


/*********************************************************************//**
 * @brief		Get current USB PLL clock from XTAL
 * @param[in]	None
 * @return 		Returned clock value
 **********************************************************************/
uint32_t CGU_SetPLL0(void){
	// Setup PLL550 to generate 480MHz from 12 MHz crystal
	LPC_CGU->PLL0USB_CTRL |= 1; 	// Power down PLL
						//	P			N
	LPC_CGU->PLL0USB_NP_DIV = (98<<0) | (514<<12);
						//	SELP	SELI	SELR	MDEC
	LPC_CGU->PLL0USB_MDIV = (0xB<<17)|(0x10<<22)|(0<<28)|(0x7FFA<<0);
	LPC_CGU->PLL0USB_CTRL =(CGU_CLKSRC_XTAL_OSC<<24) | (0x3<<2) | (1<<4);
	return CGU_ERROR_SUCCESS;
}


/*********************************************************************//**
 * @brief		Setting PLL1
 * @param[in]	mult	Multiple value
 * @return 		Setting status, could be:
 * 					- CGU_ERROR_SUCCESS: successful
 * 					- CGU_ERROR_INVALID_PARAM: Invalid parameter error
 **********************************************************************/
uint32_t	CGU_SetPLL1(uint32_t mult){
	uint32_t msel=0, nsel=0, psel=0, pval=1;
	uint32_t freq;
	uint32_t ClkSrc = (LPC_CGU->PLL1_CTRL & CGU_CTRL_SRC_MASK)>>24;
	freq = CGU_ClockSourceFrequency[ClkSrc];
	freq *= mult;
	msel = mult-1;

	LPC_CGU->PLL1_CTRL &= ~(CGU_PLL1_FBSEL_MASK |
									CGU_PLL1_BYPASS_MASK |
									CGU_PLL1_DIRECT_MASK |
									(0x03<<8) | (0xFF<<16) | (0x03<<12));

	if(freq<156000000){
		//psel is encoded such that 0=1, 1=2, 2=4, 3=8
		while(2*(pval)*freq < 156000000) {
			psel++;
			pval*=2;
		}
//		if(2*(pval)*freq > 320000000) {
//			//THIS IS OUT OF RANGE!!!
//			//HOW DO WE ASSERT IN SAMPLE CODE?
//			//__breakpoint(0);
//			return CGU_ERROR_INVALID_PARAM;
//		}
		LPC_CGU->PLL1_CTRL |= (msel<<16) | (nsel<<12) | (psel<<8) | CGU_PLL1_FBSEL_MASK;
	}else if(freq<320000000){
		LPC_CGU->PLL1_CTRL |= (msel<<16) | (nsel<<12) | (psel<<8) |CGU_PLL1_DIRECT_MASK | CGU_PLL1_FBSEL_MASK;
	}else
		return CGU_ERROR_INVALID_PARAM;

	return CGU_ERROR_SUCCESS;
}


/*********************************************************************//**
 * @brief		Get current base status
 * @param[in]	Base	Base type, should be:
 * 					- CGU_BASE_USB0				:Base clock for USB0
 * 					- CGU_BASE_USB1				:Base clock for USB1
 * 					- CGU_BASE_M3				:System base clock for ARM Cortex-M3 core
 * 												 and APB peripheral blocks #0 and #2
 * 					- CGU_BASE_SPIFI			:Base clock for SPIFI
 * 					- CGU_BASE_APB1				:Base clock for APB peripheral block #1
 * 					- CGU_BASE_APB3				:Base clock for APB peripheral block #3
 * 					- CGU_BASE_SDIO				:Base clock for SDIO card reader
 * 					- CGU_BASE_SSP0				:Base clock for SSP0
 * 					- CGU_BASE_SSP1				:Base clock for SSP1
 * 					- CGU_BASE_UART0			:Base clock for UART0
 * 					- CGU_BASE_UART1			:Base clock for UART1
 * 					- CGU_BASE_UART2			:Base clock for UART2
 * 					- CGU_BASE_UART3			:Base clock for UART3
 * @return 		Always return 0
 **********************************************************************/
uint32_t	CGU_GetBaseStatus(CGU_ENTITY_T Base){
	switch(Base){
	/*CCU1*/
	case CGU_BASE_APB3:
		return LPC_CCU1->BASE_STAT & 1;

	case CGU_BASE_APB1:
		return (LPC_CCU1->BASE_STAT>>1) & 1;

	case CGU_BASE_SPIFI:
		return (LPC_CCU1->BASE_STAT>>2) & 1;

	case CGU_BASE_M3:
		return (LPC_CCU1->BASE_STAT>>3) & 1;

	case CGU_BASE_USB0:
		return (LPC_CCU1->BASE_STAT>>7) & 1;

	case CGU_BASE_USB1:
		return (LPC_CCU1->BASE_STAT>>8) & 1;

	/*CCU2*/
	case CGU_BASE_UART3:
		return (LPC_CCU2->BASE_STAT>>1) & 1;

	case CGU_BASE_UART2:
		return (LPC_CCU2->BASE_STAT>>2) & 1;

	case CGU_BASE_UART1:
		return (LPC_CCU2->BASE_STAT>>3) & 1;

	case CGU_BASE_UART0:
		return (LPC_CCU2->BASE_STAT>>4) & 1;

	case CGU_BASE_SSP1:
		return (LPC_CCU2->BASE_STAT>>5) & 1;

	case CGU_BASE_SSP0:
		return (LPC_CCU2->BASE_STAT>>6) & 1;

	case CGU_BASE_SDIO:
		return (LPC_CCU2->BASE_STAT>>7) & 1;

	/*BASE SAFE is used by WWDT and RGU*/
	case CGU_BASE_SAFE:
		break;
	default:
		break;
	}
	return 0;
}


/*********************************************************************//**
 * @brief		Compare one source clock to IRC clock
 * @param[in]	Clock	Clock entity that will be compared to IRC, should be:
 * 					- CGU_CLKSRC_32KHZ_OSC		:32Khz crystal oscillator
 * 					- CGU_CLKSRC_ENET_RX_CLK	:Ethernet receive clock
 * 					- CGU_CLKSRC_ENET_TX_CLK	:Ethernet transmit clock
 * 					- CGU_CLKSRC_GP_CLKIN		:General purpose input clock
 * 					- CGU_CLKSRC_XTAL_OSC		:Crystal oscillator
 * 					- CGU_CLKSRC_PLL0			:PLL0 clock
 * 					- CGU_CLKSRC_PLL1			:PLL1 clock
 * 					- CGU_CLKSRC_IDIVA			:Integer divider register A
 * 					- CGU_CLKSRC_IDIVB			:Integer divider register B
 * 					- CGU_CLKSRC_IDIVC			:Integer divider register C
 * 					- CGU_CLKSRC_IDIVD			:Integer divider register D
 * 					- CGU_CLKSRC_IDIVE			:Integer divider register E
 * 					- CGU_BASE_SAFE				:Base safe clock (always on)for WDT
 * 					- CGU_BASE_USB0				:Base clock for USB0
 * 					- CGU_BASE_USB1				:Base clock for USB1
 * 					- CGU_BASE_M3				:System base clock for ARM Cortex-M3 core
 * 												 and APB peripheral blocks #0 and #2
 * 					- CGU_BASE_SPIFI			:Base clock for SPIFI
 * 					- CGU_BASE_PHY_RX			:Base clock for Ethernet PHY Rx
 * 					- CGU_BASE_PHY_TX			:Base clock for Ethernet PHY Tx
 * 					- CGU_BASE_APB1				:Base clock for APB peripheral block #1
 * 					- CGU_BASE_APB3				:Base clock for APB peripheral block #3
 * 					- CGU_BASE_LCD				:Base clock for LCD
 * 					- CGU_BASE_SDIO				:Base clock for SDIO card reader
 * 					- CGU_BASE_SSP0				:Base clock for SSP0
 * 					- CGU_BASE_SSP1				:Base clock for SSP1
 * 					- CGU_BASE_UART0			:Base clock for UART0
 * 					- CGU_BASE_UART1			:Base clock for UART1
 * 					- CGU_BASE_UART2			:Base clock for UART2
 * 					- CGU_BASE_UART3			:Base clock for UART3
 * 					- CGU_BASE_CLKOUT			:Base clock for CLKOUT pin
 * @param[in]	m	Multiple value pointer
 * @param[in]	d	Divider value pointer
 * @return 		Compare status, could be:
 * 					- (-1): fail
 * 					- 0: successful
 * @note		Formula used to compare:
 * 				FClock = F_IRC* m / d
 **********************************************************************/
int CGU_FrequencyMonitor(CGU_ENTITY_T Clock, uint32_t *m, uint32_t *d){
	uint32_t n,c,temp;
	int i;

	/* Maximum allow RCOUNT number */
	c= 511;
	/* Check Source Clock Freq is larger or smaller */
	LPC_CGU->FREQ_MON = (Clock<<24) | 1<<23 | c;
	while(LPC_CGU->FREQ_MON & (1 <<23));
	for(i=0;i<10000;i++);
	temp = (LPC_CGU->FREQ_MON >>9) & 0x3FFF;

	if(temp == 0) /* too low F < 12000000/511*/
		return -1;
	if(temp > 511){ /* larger */

		c = 511 - (LPC_CGU->FREQ_MON&0x1FF);
	}else{
		do{
			c--;
			LPC_CGU->FREQ_MON = (Clock<<24) | 1<<23 | c;
			while(LPC_CGU->FREQ_MON & (1 <<23));
			for(i=0;i<10000;i++);
			n = (LPC_CGU->FREQ_MON >>9) & 0x3FFF;
		}while(n==temp);
		c++;
	}
	*m = temp;
	*d = c;
	return 0;
}

/*********************************************************************//**
 * @brief		Compare one source clock to another source clock
 * @param[in]	Clock	Clock entity that will be compared to second source, should be:
 * 					- CGU_CLKSRC_32KHZ_OSC		:32Khz crystal oscillator
 * 					- CGU_CLKSRC_ENET_RX_CLK	:Ethernet receive clock
 * 					- CGU_CLKSRC_ENET_TX_CLK	:Ethernet transmit clock
 * 					- CGU_CLKSRC_GP_CLKIN		:General purpose input clock
 * 					- CGU_CLKSRC_XTAL_OSC		:Crystal oscillator
 * 					- CGU_CLKSRC_PLL0			:PLL0 clock
 * 					- CGU_CLKSRC_PLL1			:PLL1 clock
 * 					- CGU_CLKSRC_IDIVA			:Integer divider register A
 * 					- CGU_CLKSRC_IDIVB			:Integer divider register B
 * 					- CGU_CLKSRC_IDIVC			:Integer divider register C
 * 					- CGU_CLKSRC_IDIVD			:Integer divider register D
 * 					- CGU_CLKSRC_IDIVE			:Integer divider register E
 * 					- CGU_BASE_SAFE				:Base safe clock (always on)for WDT
 * 					- CGU_BASE_USB0				:Base clock for USB0
 * 					- CGU_BASE_USB1				:Base clock for USB1
 * 					- CGU_BASE_M3				:System base clock for ARM Cortex-M3 core
 * 												 and APB peripheral blocks #0 and #2
 * 					- CGU_BASE_SPIFI			:Base clock for SPIFI
 * 					- CGU_BASE_PHY_RX			:Base clock for Ethernet PHY Rx
 * 					- CGU_BASE_PHY_TX			:Base clock for Ethernet PHY Tx
 * 					- CGU_BASE_APB1				:Base clock for APB peripheral block #1
 * 					- CGU_BASE_APB3				:Base clock for APB peripheral block #3
 * 					- CGU_BASE_LCD				:Base clock for LCD
 * 					- CGU_BASE_SDIO				:Base clock for SDIO card reader
 * 					- CGU_BASE_SSP0				:Base clock for SSP0
 * 					- CGU_BASE_SSP1				:Base clock for SSP1
 * 					- CGU_BASE_UART0			:Base clock for UART0
 * 					- CGU_BASE_UART1			:Base clock for UART1
 * 					- CGU_BASE_UART2			:Base clock for UART2
 * 					- CGU_BASE_UART3			:Base clock for UART3
 * 					- CGU_BASE_CLKOUT			:Base clock for CLKOUT pin
 * @param[in]	CompareToClock	Clock source that to be compared to first source, should be different
 * 				to first source.
 * @param[in]	m	Multiple value pointer
 * @param[in]	d	Divider value pointer
 * @return 		Compare status, could be:
 * 					- (-1): fail
 * 					- 0: successful
 * @note		Formula used to compare:
 * 				FClock = m*FCompareToClock/d
 **********************************************************************/
uint32_t CGU_RealFrequencyCompare(CGU_ENTITY_T Clock, CGU_ENTITY_T CompareToClock, uint32_t *m, uint32_t *d){
	uint32_t m1,m2,d1,d2;
	/* Check Parameter */
	if((Clock>CGU_CLKSRC_IDIVE) || (CompareToClock>CGU_CLKSRC_IDIVE))
		return CGU_ERROR_INVALID_PARAM;
	/* Check for Clock Enable - Not yet implement
	 * The Comparator will hang if Clock has not been set*/
	CGU_FrequencyMonitor(Clock, &m1, &d1);
	CGU_FrequencyMonitor(CompareToClock, &m2, &d2);
	*m= m1*d2;
	*d= d1*m2;
	return 0;

}
/**
 * @}
 */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
