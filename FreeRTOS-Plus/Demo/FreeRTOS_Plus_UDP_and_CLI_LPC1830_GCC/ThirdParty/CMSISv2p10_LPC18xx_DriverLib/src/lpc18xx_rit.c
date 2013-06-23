/**********************************************************************
* $Id$		lpc18xx_rit.c		2011-06-02
*//**
* @file		lpc18xx_rit.c
* @brief	Contains all functions support for RIT firmware library on LPC18xx
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
/** @addtogroup RIT
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_rit.h"
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

#ifdef _RIT

/* Public Functions ----------------------------------------------------------- */
/** @addtogroup RIT_Public_Functions
 * @{
 */

/******************************************************************************//*
 * @brief 		Initial for RIT
 * 					- Turn on power and clock
 * 					- Setup default register values
 * @param[in]	RITx is RIT peripheral selected, should be: LPC_RIT
 * @return 		None
 *******************************************************************************/
void RIT_Init(LPC_RITIMER_Type *RITx)
{
	CHECK_PARAM(PARAM_RITx(RITx));
	//CGU_ConfigPPWR (CGU_PCONP_PCRIT, ENABLE);
	//Set up default register values
	RITx->COMPVAL = 0xFFFFFFFF;
	RITx->MASK	= 0x00000000;
	RITx->CTRL	= 0x0C;
	RITx->COUNTER	= 0x00000000;
	// Turn on power and clock

}
/******************************************************************************//*
 * @brief 		DeInitial for RIT
 * 					- Turn off power and clock
 * 					- ReSetup default register values
 * @param[in]	RITx is RIT peripheral selected, should be: LPC_RIT
 * @return 		None
 *******************************************************************************/
void RIT_DeInit(LPC_RITIMER_Type *RITx)
{
	CHECK_PARAM(PARAM_RITx(RITx));

	// Turn off power and clock
	//CGU_ConfigPPWR (CGU_PCONP_PCRIT, DISABLE);
	//ReSetup default register values
	RITx->COMPVAL = 0xFFFFFFFF;
	RITx->MASK	= 0x00000000;
	RITx->CTRL	= 0x0C;
	RITx->COUNTER	= 0x00000000;
}

/******************************************************************************//*
 * @brief 		Set compare value, mask value and time counter value
 * @param[in]	RITx is RIT peripheral selected, should be: LPC_RIT
 * @param[in]	time_interval timer interval value (ms)
 * @return 		None
 *******************************************************************************/

void RIT_TimerConfig(LPC_RITIMER_Type *RITx, uint32_t time_interval)
{
	uint32_t clock_rate, cmp_value;
	CHECK_PARAM(PARAM_RITx(RITx));

	// Get PCLK value of RIT
	clock_rate = /*CGU_GetPCLK(CGU_PCLKSEL_RIT)*/ CGU_GetPCLKFrequency(CGU_PERIPHERAL_M3CORE);

	/* calculate compare value for RIT to generate interrupt at
	 * specified time interval
	 * COMPVAL = (RIT_PCLK * time_interval)/1000
	 * (with time_interval unit is millisecond)
	 */
	cmp_value = (clock_rate /1000) * time_interval;
	RITx->COMPVAL = cmp_value;

	/* Set timer enable clear bit to clear timer to 0 whenever
	 * counter value equals the contents of RICOMPVAL
	 */
	RITx->CTRL |= (1<<1);
}


/******************************************************************************//*
 * @brief 		Enable/Disable Timer
 * @param[in]	RITx is RIT peripheral selected, should be: LPC_RIT
 * @param[in]	NewState 	New State of this function
 * 					-ENABLE		:Enable Timer
 * 					-DISABLE	:Disable Timer
 * @return 		None
 *******************************************************************************/
void RIT_Cmd(LPC_RITIMER_Type *RITx, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_RITx(RITx));
	CHECK_PARAM(PARAM_FUNCTIONALSTATE(NewState));

	//Enable or Disable Timer
	if(NewState==ENABLE)
	{
		RITx->CTRL |= RIT_CTRL_TEN;
	}
	else
	{
		RITx->CTRL &= ~RIT_CTRL_TEN;
	}
}

/******************************************************************************//*
 * @brief 		Timer Enable/Disable on debug
 * @param[in]	RITx is RIT peripheral selected, should be: LPC_RIT
 * @param[in]	NewState 	New State of this function
 * 					-ENABLE		:The timer is halted whenever a hardware break condition occurs
 * 					-DISABLE	:Hardware break has no effect on the timer operation
 * @return 		None
 *******************************************************************************/
void RIT_TimerDebugCmd(LPC_RITIMER_Type *RITx, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_RITx(RITx));
	CHECK_PARAM(PARAM_FUNCTIONALSTATE(NewState));

	//Timer Enable/Disable on break
	if(NewState==ENABLE)
	{
		RITx->CTRL |= RIT_CTRL_ENBR;
	}
	else
	{
		RITx->CTRL &= ~RIT_CTRL_ENBR;
	}
}
/******************************************************************************//*
 * @brief 		Check whether interrupt flag is set or not
 * @param[in]	RITx is RIT peripheral selected, should be: LPC_RIT
 * @return 		Current interrupt status, could be
 * 					- SET
 * 					- RESET
 *******************************************************************************/
IntStatus RIT_GetIntStatus(LPC_RITIMER_Type *RITx)
{
	uint8_t result;
	CHECK_PARAM(PARAM_RITx(RITx));
	if((RITx->CTRL&RIT_CTRL_INTEN)==1)	result= SET;
	else return RESET;
	//clear interrupt flag
	RITx->CTRL |= RIT_CTRL_INTEN;
	return (IntStatus)result;
}

/**
 * @}
 */

#endif /* _RIT */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
