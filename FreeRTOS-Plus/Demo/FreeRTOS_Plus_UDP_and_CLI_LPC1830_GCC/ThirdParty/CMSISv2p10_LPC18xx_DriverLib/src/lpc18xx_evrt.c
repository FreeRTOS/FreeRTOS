/**********************************************************************
* $Id$		lpc18xx_evrt.c		2011-06-02
*//**
* @file		lpc18xx_evrt.c
* @brief	Contains all functions support for Event Router firmware
* 			library on LPC18xx
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
/** @addtogroup EVRT
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_evrt.h"

/* If this source file built with example, the LPC18xx FW library configuration
 * file in each example directory ("lpc18xx_libcfg.h") must be included,
 * otherwise the default FW library configuration file must be included instead
 */
#ifdef __BUILD_WITH_EXAMPLE__
#include "lpc18xx_libcfg.h"
#else
#include "lpc18xx_libcfg_default.h"
#endif /* __BUILD_WITH_EXAMPLE__ */

/* Public Functions ----------------------------------------------------------- */
/** @addtogroup EVRT_Public_Functions
 * @{
 */

/********************************************************************//**
 * @brief		Initializes the EVRT peripheral.
 * @param[in]	EVRTx	EVRT peripheral selected, should be: LPC_EVRT
 * @return 		None
 *********************************************************************/
void EVRT_Init (LPC_EVENTROUTER_Type *EVRTx)
{
	uint8_t i=0;

	CHECK_PARAM(PARAM_EVRTx(EVRTx));

	// Clear all register to be default
	EVRTx->HILO 		= 0x0000;
	EVRTx->EDGE 		= 0x0000;
	EVRTx->CLR_EN 	= 0xFFFF;
	do
	{
		i++;
		EVRTx->CLR_STAT 	= 0xFFFFF;
	}while((EVRTx->STATUS != 0)&&(i<10));
}

/*********************************************************************//**
 * @brief		De-initializes the EVRT peripheral registers to their
*                  default reset values.
 * @param[in]	EVRTx	EVRT peripheral selected, should be: LPC_EVRT
 * @return 		None
 **********************************************************************/
void EVRT_DeInit(LPC_EVENTROUTER_Type *EVRTx)
{
	CHECK_PARAM(PARAM_EVRTx(EVRTx));

	EVRTx->CLR_EN 	= 0xFFFF;
	EVRTx->CLR_STAT 	= 0xFFFF;
}

/*********************************************************************//**
 * @brief		Setting up the type of interrupt sources to EVRT
 * @param[in]	EVRTx	EVRT peripheral selected, should be: LPC_EVRT
 * @param[in]	EVRT_Src 	EVRT source, should be:
 * 					- EVRT_SRC_WAKEUP0			:WAKEUP0 event
 * 					- EVRT_SRC_WAKEUP1			:WAKEUP1 event
 * 					- EVRT_SRC_WAKEUP2			:WAKEUP2 event
 * 					- EVRT_SRC_WAKEUP3			:WAKEUP3 event
 * 					- EVRT_SRC_ATIMER			:Alarm timer eveny
 * 					- EVRT_SRC_RTC				:RTC event
 * 					- EVRT_SRC_BOD				:BOD event
 * 					- EVRT_SRC_WWDT				:WWDT event
 * 					- EVRT_SRC_ETHERNET			:ETHERNET event
 * 					- EVRT_SRC_USB0				:USB0 event
 * 					- EVRT_SRC_USB1				:USB1 event
 * 					- EVRT_SRC_CCAN				:CCAN event
 * 					- EVRT_SRC_COMBINE_TIMER2	:Combined timer output 2 event
 * 					- EVRT_SRC_COMBINE_TIMER6	:Combined timer output 6 event
 * 					- EVRT_SRC_QEI				:QEI event
 * 					- EVRT_SRC_COMBINE_TIMER14	:Combined timer output 14 event
 * 					- EVRT_SRC_RESET			:RESET event
 * 				type	Active type, should be:
 * 					- EVRT_SRC_ACTIVE_LOW_LEVEL		:Active low level
 * 					- EVRT_SRC_ACTIVE_HIGH_LEVEL	:Active high level
 * 					- EVRT_SRC_ACTIVE_FALLING_EDGE	:Active falling edge
 * 					- EVRT_SRC_ACTIVE_RISING_EDGE	:Active rising edge
 * @param[in]	type	EVRT source active type, should be:
 * 					- 	EVRT_SRC_ACTIVE_LOW_LEVEL		:Active low level
 *					-	EVRT_SRC_ACTIVE_HIGH_LEVEL		:Active high level
 *					- 	EVRT_SRC_ACTIVE_FALLING_EDGE	:Active falling edge
 *					- 	EVRT_SRC_ACTIVE_RISING_EDGE		:Active rising edge
 * @return 		None
 **********************************************************************/
void EVRT_ConfigIntSrcActiveType(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src, EVRT_SRC_ACTIVE_TYPE type)
{
	CHECK_PARAM(PARAM_EVRTx(EVRTx));
	CHECK_PARAM(PARAM_EVRT_SOURCE(EVRT_Src));
	CHECK_PARAM(PARAM_EVRT_SOURCE_ACTIVE_TYPE(type));

	switch (type)
	{
		case EVRT_SRC_ACTIVE_LOW_LEVEL:
			EVRTx->HILO &= ~(1<<(uint8_t)EVRT_Src);
			EVRTx->EDGE &= ~(1<<(uint8_t)EVRT_Src);
			break;
		case EVRT_SRC_ACTIVE_HIGH_LEVEL:
			EVRTx->HILO |= (1<<(uint8_t)EVRT_Src);
			EVRTx->EDGE &= ~(1<<(uint8_t)EVRT_Src);
			break;
		case EVRT_SRC_ACTIVE_FALLING_EDGE:
			EVRTx->HILO &= ~(1<<(uint8_t)EVRT_Src);
			EVRTx->EDGE |= (1<<(uint8_t)EVRT_Src);
			break;
		case EVRT_SRC_ACTIVE_RISING_EDGE:
			EVRTx->HILO |= (1<<(uint8_t)EVRT_Src);
			EVRTx->EDGE |= (1<<(uint8_t)EVRT_Src);
			break;
		default:
			break;
	}
}

/*********************************************************************//**
 * @brief		Enable or disable interrupt sources to EVRT
 * @param[in]	EVRTx	EVRT peripheral selected, should be LPC_EVRT
 * @param[in]	EVRT_Src EVRT source, should be:
 * 					- EVRT_SRC_WAKEUP0			:WAKEUP0 event
 * 					- EVRT_SRC_WAKEUP1			:WAKEUP1 event
 * 					- EVRT_SRC_WAKEUP2			:WAKEUP2 event
 * 					- EVRT_SRC_WAKEUP3			:WAKEUP3 event
 * 					- EVRT_SRC_ATIMER			:Alarm timer eveny
 * 					- EVRT_SRC_RTC				:RTC event
 * 					- EVRT_SRC_BOD				:BOD event
 * 					- EVRT_SRC_WWDT				:WWDT event
 * 					- EVRT_SRC_ETHERNET			:ETHERNET event
 * 					- EVRT_SRC_USB0				:USB0 event
 * 					- EVRT_SRC_USB1				:USB1 event
 * 					- EVRT_SRC_CCAN				:CCAN event
 * 					- EVRT_SRC_COMBINE_TIMER2	:Combined timer output 2 event
 * 					- EVRT_SRC_COMBINE_TIMER6	:Combined timer output 6 event
 * 					- EVRT_SRC_QEI				:QEI event
 * 					- EVRT_SRC_COMBINE_TIMER14	:Combined timer output 14 event
 * 					- EVRT_SRC_RESET			:RESET event
 * @param[in]	state	ENABLE or DISABLE
 * @return 		None
 **********************************************************************/
void EVRT_SetUpIntSrc(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src, FunctionalState state)
{
	CHECK_PARAM(PARAM_EVRTx(EVRTx));
	CHECK_PARAM(PARAM_EVRT_SOURCE(EVRT_Src));

	if(state == ENABLE)
		EVRTx->SET_EN = (1<<(uint8_t)EVRT_Src);
	else
		EVRTx->CLR_EN = (1<<(uint8_t)EVRT_Src);
}

/*********************************************************************//**
 * @brief		Check if a source is sending interrupt to EVRT
 * @param[in]	EVRTx	EVRT peripheral selected, should be LPC_EVRT
 * @param[in]	EVRT_Src	EVRT source, should be:
 * 					- EVRT_SRC_WAKEUP0			:WAKEUP0 event
 * 					- EVRT_SRC_WAKEUP1			:WAKEUP1 event
 * 					- EVRT_SRC_WAKEUP2			:WAKEUP2 event
 * 					- EVRT_SRC_WAKEUP3			:WAKEUP3 event
 * 					- EVRT_SRC_ATIMER			:Alarm timer eveny
 * 					- EVRT_SRC_RTC				:RTC event
 * 					- EVRT_SRC_BOD				:BOD event
 * 					- EVRT_SRC_WWDT				:WWDT event
 * 					- EVRT_SRC_ETHERNET			:ETHERNET event
 * 					- EVRT_SRC_USB0				:USB0 event
 * 					- EVRT_SRC_USB1				:USB1 event
 * 					- EVRT_SRC_CCAN				:CCAN event
 * 					- EVRT_SRC_COMBINE_TIMER2	:Combined timer output 2 event
 * 					- EVRT_SRC_COMBINE_TIMER6	:Combined timer output 6 event
 * 					- EVRT_SRC_QEI				:QEI event
 * 					- EVRT_SRC_COMBINE_TIMER14	:Combined timer output 14 event
 * 					- EVRT_SRC_RESET			:RESET event
 * @return 		TRUE or FALSE
 **********************************************************************/
Bool EVRT_IsSourceInterrupting(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src)
{
	CHECK_PARAM(PARAM_EVRTx(EVRTx));
	CHECK_PARAM(PARAM_EVRT_SOURCE(EVRT_Src));

	if(EVRTx->STATUS & (1<<(uint8_t)EVRT_Src))
		return TRUE;
	else return FALSE;
}

/*********************************************************************//**
 * @brief		Clear pending interrupt EVRT source
 * @param[in]	EVRTx	EVRT peripheral selected, should be LPC_EVRT
 * @param[in]	EVRT_Src	EVRT source, should be:
 * 					- EVRT_SRC_WAKEUP0			:WAKEUP0 event
 * 					- EVRT_SRC_WAKEUP1			:WAKEUP1 event
 * 					- EVRT_SRC_WAKEUP2			:WAKEUP2 event
 * 					- EVRT_SRC_WAKEUP3			:WAKEUP3 event
 * 					- EVRT_SRC_ATIMER			:Alarm timer eveny
 * 					- EVRT_SRC_RTC				:RTC event
 * 					- EVRT_SRC_BOD				:BOD event
 * 					- EVRT_SRC_WWDT				:WWDT event
 * 					- EVRT_SRC_ETHERNET			:ETHERNET event
 * 					- EVRT_SRC_USB0				:USB0 event
 * 					- EVRT_SRC_USB1				:USB1 event
 * 					- EVRT_SRC_CCAN				:CCAN event
 * 					- EVRT_SRC_COMBINE_TIMER2	:Combined timer output 2 event
 * 					- EVRT_SRC_COMBINE_TIMER6	:Combined timer output 6 event
 * 					- EVRT_SRC_QEI				:QEI event
 * 					- EVRT_SRC_COMBINE_TIMER14	:Combined timer output 14 event
 * 					- EVRT_SRC_RESET			:RESET event
 * @return 		none
 **********************************************************************/
void EVRT_ClrPendIntSrc(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src)
{
	CHECK_PARAM(PARAM_EVRTx(EVRTx));
	CHECK_PARAM(PARAM_EVRT_SOURCE(EVRT_Src));

	EVRTx->CLR_STAT = (1<<(uint8_t)EVRT_Src);
}

/**
 * @}
 */



/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */

