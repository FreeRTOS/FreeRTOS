/**********************************************************************
* $Id$		lpc18xx_rtc.c		2011-06-02
*//**
* @file		lpc18xx_rtc.c
* @brief	Contains all functions support for RTC firmware library on LPC18xx
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
/** @addtogroup RTC
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_rtc.h"
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


#ifdef _RTC

/* Public Functions ----------------------------------------------------------- */
/** @addtogroup RTC_Public_Functions
 * @{
 */

/********************************************************************//**
 * @brief		Initializes the RTC peripheral.
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @return 		None
 *********************************************************************/
void RTC_Init (LPC_RTC_Type *RTCx)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	// Configure clock to RTC
	LPC_CREG->CREG0 &= ~((1<<3)|(1<<2));					// Reset 32Khz oscillator
	LPC_CREG->CREG0 |= (1<<1)|(1<<0);						// Enable 32 kHz & 1 kHz on osc32k and release reset
	LPC_SCU->SFSCLK_0 = 1 | (0x3<<2);						// function 1; CGU clk out, pull down
	LPC_CGU->BASE_OUT_CLK = (CGU_CLKSRC_32KHZ_OSC<<24) |(1<<11);		// base clock out use 32KHz crystal and auto block
	do
	{
		/* Reset RTC clock*/
		RTCx->CCR = RTC_CCR_CTCRST | RTC_CCR_CCALEN;
	}
	while(RTCx->CCR!=(RTC_CCR_CTCRST | RTC_CCR_CCALEN));
	do
	{
		/* Finish resetting RTC clock*/
		RTCx->CCR = RTC_CCR_CCALEN;
	}
	while(RTCx->CCR != RTC_CCR_CCALEN);
	/* Clear counter increment and alarm interrupt */
	RTCx->ILR = RTC_IRL_RTCCIF | RTC_IRL_RTCALF;
	while(RTCx->ILR!=0);
	// Clear all register to be default
	RTCx->CIIR = 0x00;
	RTCx->AMR = 0xFF;
	RTCx->CALIBRATION = 0x00;
}


/*********************************************************************//**
 * @brief		De-initializes the RTC peripheral registers to their
*                  default reset values.
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @return 		None
 **********************************************************************/
void RTC_DeInit(LPC_RTC_Type *RTCx)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	RTCx->CCR = 0x00;
}

/*********************************************************************//**
 * @brief 		Reset clock tick counter in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @return 		None
 **********************************************************************/
void RTC_ResetClockTickCounter(LPC_RTC_Type *RTCx)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	RTCx->CCR |= RTC_CCR_CTCRST;
	RTCx->CCR &= (~RTC_CCR_CTCRST) & RTC_CCR_BITMASK;
}

/*********************************************************************//**
 * @brief 		Start/Stop RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	NewState New State of this function, should be:
 * 					- ENABLE	:The time counters are enabled
 * 					- DISABLE	:The time counters are disabled
 * @return 		None
 **********************************************************************/
void RTC_Cmd (LPC_RTC_Type *RTCx, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_FUNCTIONALSTATE(NewState));

	if (NewState == ENABLE)
	{
		do
		{
		RTCx->CCR |= RTC_CCR_CLKEN;
		}
		while((RTCx->CCR&RTC_CCR_CLKEN)==0);
	}
	else
	{
		RTCx->CCR &= (~RTC_CCR_CLKEN) & RTC_CCR_BITMASK;
	}
}


/*********************************************************************//**
 * @brief 		Enable/Disable Counter increment interrupt for each time type
 * 				in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	CntIncrIntType: Counter Increment Interrupt type,
 * 				an increment of this type value below will generates
 * 				an interrupt, should be:
 * 					- RTC_TIMETYPE_SECOND
 * 					- RTC_TIMETYPE_MINUTE
 * 					- RTC_TIMETYPE_HOUR
 * 					- RTC_TIMETYPE_DAYOFWEEK
 * 					- RTC_TIMETYPE_DAYOFMONTH
 * 					- RTC_TIMETYPE_DAYOFYEAR
 * 					- RTC_TIMETYPE_MONTH
 * 					- RTC_TIMETYPE_YEAR
 * @param[in]	NewState New State of this function, should be:
 * 					- ENABLE: Counter Increment interrupt for this time type are enabled
 * 					- DISABLE: Counter Increment interrupt for this time type are disabled
 * @return 		None
 **********************************************************************/
void RTC_CntIncrIntConfig (LPC_RTC_Type *RTCx, uint32_t CntIncrIntType, \
								FunctionalState NewState)
{
	uint32_t tem;

	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_FUNCTIONALSTATE(NewState));
	CHECK_PARAM(PARAM_RTC_TIMETYPE(CntIncrIntType));

	switch (CntIncrIntType)
	{
	case RTC_TIMETYPE_SECOND:
		tem = RTC_CIIR_IMSEC;
		break;
	case RTC_TIMETYPE_MINUTE:
		tem = RTC_CIIR_IMMIN;
		break;
	case RTC_TIMETYPE_HOUR:
		tem = RTC_CIIR_IMHOUR;
		break;
	case RTC_TIMETYPE_DAYOFWEEK:
		tem = RTC_CIIR_IMDOW;
		break;
	case RTC_TIMETYPE_DAYOFMONTH:
		tem = RTC_CIIR_IMDOM;
		break;
	case RTC_TIMETYPE_DAYOFYEAR:
		tem = RTC_CIIR_IMDOY;
		break;
	case RTC_TIMETYPE_MONTH:
		tem = RTC_CIIR_IMMON;
		break;
	case RTC_TIMETYPE_YEAR:
		tem = RTC_CIIR_IMYEAR;
		break;
	}
	if (NewState ==  ENABLE)
	{
		//do
		{
			RTCx->CIIR |= tem;
		}
		//while((RTCx->CIIR & tem)== 0);
	}
	else
	{
		//do
		{
			RTCx->CIIR &= (~tem) & RTC_CIIR_BITMASK;
		}
		//while(RTCx->CIIR & tem);
	}
}


/*********************************************************************//**
 * @brief 		Enable/Disable Alarm interrupt for each time type
 * 				in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	AlarmTimeType: Alarm Time Interrupt type,
 * 				an matching of this type value below with current time
 * 				in RTC will generates an interrupt, should be:
 * 					- RTC_TIMETYPE_SECOND
 * 					- RTC_TIMETYPE_MINUTE
 * 					- RTC_TIMETYPE_HOUR
 * 					- RTC_TIMETYPE_DAYOFWEEK
 * 					- RTC_TIMETYPE_DAYOFMONTH
 * 					- RTC_TIMETYPE_DAYOFYEAR
 * 					- RTC_TIMETYPE_MONTH
 * 					- RTC_TIMETYPE_YEAR
 * @param[in]	NewState New State of this function, should be:
 * 					- ENABLE: Alarm interrupt for this time type are enabled
 * 					- DISABLE: Alarm interrupt for this time type are disabled
 * @return 		None
 **********************************************************************/
void RTC_AlarmIntConfig (LPC_RTC_Type *RTCx, uint32_t AlarmTimeType, \
								FunctionalState NewState)
{
	uint32_t tem;

	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_FUNCTIONALSTATE(NewState));
	CHECK_PARAM(PARAM_RTC_TIMETYPE(AlarmTimeType));

	switch (AlarmTimeType)
	{
	case RTC_TIMETYPE_SECOND:
		tem = (RTC_AMR_AMRSEC);
		break;
	case RTC_TIMETYPE_MINUTE:
		tem = (RTC_AMR_AMRMIN);
		break;
	case RTC_TIMETYPE_HOUR:
		tem = (RTC_AMR_AMRHOUR);
		break;
	case RTC_TIMETYPE_DAYOFWEEK:
		tem = (RTC_AMR_AMRDOW);
		break;
	case RTC_TIMETYPE_DAYOFMONTH:
		tem = (RTC_AMR_AMRDOM);
		break;
	case RTC_TIMETYPE_DAYOFYEAR:
		tem = (RTC_AMR_AMRDOY);
		break;
	case RTC_TIMETYPE_MONTH:
		tem = (RTC_AMR_AMRMON);
		break;
	case RTC_TIMETYPE_YEAR:
		tem = (RTC_AMR_AMRYEAR);
		break;
	}
	if (NewState == ENABLE)
	{
		//do
		{
			RTCx->AMR &= (~tem) & RTC_AMR_BITMASK;
		}
		//while(RTCx->AMR & tem);
	}
	else
	{
		//do
		{
			RTCx->AMR |= (tem);
		}
		//while((RTCx->AMR & tem)== 0);
	}
}


/*********************************************************************//**
 * @brief 		Set current time value for each time type in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	Timetype Time Type, should be:
 * 					- RTC_TIMETYPE_SECOND
 * 					- RTC_TIMETYPE_MINUTE
 * 					- RTC_TIMETYPE_HOUR
 * 					- RTC_TIMETYPE_DAYOFWEEK
 * 					- RTC_TIMETYPE_DAYOFMONTH
 * 					- RTC_TIMETYPE_DAYOFYEAR
 * 					- RTC_TIMETYPE_MONTH
 * 					- RTC_TIMETYPE_YEAR
 * @param[in]	TimeValue Time value to set
 * @return 		None
 **********************************************************************/
void RTC_SetTime (LPC_RTC_Type *RTCx, uint32_t Timetype, uint32_t TimeValue)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_RTC_TIMETYPE(Timetype));

	switch ( Timetype)
	{
	case RTC_TIMETYPE_SECOND:
		CHECK_PARAM(TimeValue <= RTC_SECOND_MAX);

		RTCx->SEC = TimeValue & RTC_SEC_MASK;
		break;

	case RTC_TIMETYPE_MINUTE:
		CHECK_PARAM(TimeValue <= RTC_MINUTE_MAX);

		RTCx->MIN = TimeValue & RTC_MIN_MASK;
		break;

	case RTC_TIMETYPE_HOUR:
		CHECK_PARAM(TimeValue <= RTC_HOUR_MAX);

		RTCx->HRS = TimeValue & RTC_HOUR_MASK;
		break;

	case RTC_TIMETYPE_DAYOFWEEK:
		CHECK_PARAM(TimeValue <= RTC_DAYOFWEEK_MAX);

		RTCx->DOW = TimeValue & RTC_DOW_MASK;
		break;

	case RTC_TIMETYPE_DAYOFMONTH:
		CHECK_PARAM((TimeValue <= RTC_DAYOFMONTH_MAX) \
				&& (TimeValue >= RTC_DAYOFMONTH_MIN));

		RTCx->DOM = TimeValue & RTC_DOM_MASK;
		break;

	case RTC_TIMETYPE_DAYOFYEAR:
		CHECK_PARAM((TimeValue >= RTC_DAYOFYEAR_MIN) \
				&& (TimeValue <= RTC_DAYOFYEAR_MAX));

		RTCx->DOY = TimeValue & RTC_DOY_MASK;
		break;

	case RTC_TIMETYPE_MONTH:
		CHECK_PARAM((TimeValue >= RTC_MONTH_MIN) \
				&& (TimeValue <= RTC_MONTH_MAX));

		RTCx->MONTH = TimeValue & RTC_MONTH_MASK;
		break;

	case RTC_TIMETYPE_YEAR:
		CHECK_PARAM(TimeValue <= RTC_YEAR_MAX);

		RTCx->YEAR = TimeValue & RTC_YEAR_MASK;
		break;
	}
}

/*********************************************************************//**
 * @brief 		Get current time value for each type time type
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	Timetype Time Type, should be:
 * 					- RTC_TIMETYPE_SECOND
 * 					- RTC_TIMETYPE_MINUTE
 * 					- RTC_TIMETYPE_HOUR
 * 					- RTC_TIMETYPE_DAYOFWEEK
 * 					- RTC_TIMETYPE_DAYOFMONTH
 * 					- RTC_TIMETYPE_DAYOFYEAR
 * 					- RTC_TIMETYPE_MONTH
 * 					- RTC_TIMETYPE_YEAR
 * @return 		Value of time according to specified time type
 **********************************************************************/
uint32_t RTC_GetTime(LPC_RTC_Type *RTCx, uint32_t Timetype)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_RTC_TIMETYPE(Timetype));

	switch (Timetype)
	{
	case RTC_TIMETYPE_SECOND:
		return (RTCx->SEC & RTC_SEC_MASK);
	case RTC_TIMETYPE_MINUTE:
		return (RTCx->MIN & RTC_MIN_MASK);
	case RTC_TIMETYPE_HOUR:
		return (RTCx->HRS & RTC_HOUR_MASK);
	case RTC_TIMETYPE_DAYOFWEEK:
		return (RTCx->DOW & RTC_DOW_MASK);
	case RTC_TIMETYPE_DAYOFMONTH:
		return (RTCx->DOM & RTC_DOM_MASK);
	case RTC_TIMETYPE_DAYOFYEAR:
		return (RTCx->DOY & RTC_DOY_MASK);
	case RTC_TIMETYPE_MONTH:
		return (RTCx->MONTH & RTC_MONTH_MASK);
	case RTC_TIMETYPE_YEAR:
		return (RTCx->YEAR & RTC_YEAR_MASK);
	default:
		return (0);
	}
}


/*********************************************************************//**
 * @brief 		Set full of time in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	pFullTime Pointer to a RTC_TIME_Type structure that
 * 				contains time value in full.
 * @return 		None
 **********************************************************************/
void RTC_SetFullTime (LPC_RTC_Type *RTCx, RTC_TIME_Type *pFullTime)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	RTCx->DOM = pFullTime->DOM & RTC_DOM_MASK;
	RTCx->DOW = pFullTime->DOW & RTC_DOW_MASK;
	RTCx->DOY = pFullTime->DOY & RTC_DOY_MASK;
	RTCx->HRS = pFullTime->HOUR & RTC_HOUR_MASK;
	RTCx->MIN = pFullTime->MIN & RTC_MIN_MASK;
	RTCx->SEC = pFullTime->SEC & RTC_SEC_MASK;
	RTCx->MONTH = pFullTime->MONTH & RTC_MONTH_MASK;
	RTCx->YEAR = pFullTime->YEAR & RTC_YEAR_MASK;
}


/*********************************************************************//**
 * @brief 		Get full of time in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	pFullTime Pointer to a RTC_TIME_Type structure that
 * 				will be stored time in full.
 * @return 		None
 **********************************************************************/
void RTC_GetFullTime (LPC_RTC_Type *RTCx, RTC_TIME_Type *pFullTime)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	pFullTime->DOM = RTCx->DOM & RTC_DOM_MASK;
	pFullTime->DOW = RTCx->DOW & RTC_DOW_MASK;
	pFullTime->DOY = RTCx->DOY & RTC_DOY_MASK;
	pFullTime->HOUR = RTCx->HRS & RTC_HOUR_MASK;
	pFullTime->MIN = RTCx->MIN & RTC_MIN_MASK;
	pFullTime->SEC = RTCx->SEC & RTC_SEC_MASK;
	pFullTime->MONTH = RTCx->MONTH & RTC_MONTH_MASK;
	pFullTime->YEAR = RTCx->YEAR & RTC_YEAR_MASK;
}


/*********************************************************************//**
 * @brief 		Set alarm time value for each time type
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	Timetype Time Type, should be:
 * 					- RTC_TIMETYPE_SECOND
 * 					- RTC_TIMETYPE_MINUTE
 * 					- RTC_TIMETYPE_HOUR
 * 					- RTC_TIMETYPE_DAYOFWEEK
 * 					- RTC_TIMETYPE_DAYOFMONTH
 * 					- RTC_TIMETYPE_DAYOFYEAR
 * 					- RTC_TIMETYPE_MONTH
 * 					- RTC_TIMETYPE_YEAR
 * @param[in]	ALValue Alarm time value to set
 * @return 		None
 **********************************************************************/
void RTC_SetAlarmTime (LPC_RTC_Type *RTCx, uint32_t Timetype, uint32_t ALValue)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	switch (Timetype)
	{
	case RTC_TIMETYPE_SECOND:
		CHECK_PARAM(ALValue <= RTC_SECOND_MAX);

		RTCx->ASEC = ALValue & RTC_SEC_MASK;
		break;

	case RTC_TIMETYPE_MINUTE:
		CHECK_PARAM(ALValue <= RTC_MINUTE_MAX);

		RTCx->AMIN = ALValue & RTC_MIN_MASK;
		break;

	case RTC_TIMETYPE_HOUR:
		CHECK_PARAM(ALValue <= RTC_HOUR_MAX);

		RTCx->AHRS = ALValue & RTC_HOUR_MASK;
		break;

	case RTC_TIMETYPE_DAYOFWEEK:
		CHECK_PARAM(ALValue <= RTC_DAYOFWEEK_MAX);

		RTCx->ADOW = ALValue & RTC_DOW_MASK;
		break;

	case RTC_TIMETYPE_DAYOFMONTH:
		CHECK_PARAM((ALValue <= RTC_DAYOFMONTH_MAX) \
				&& (ALValue >= RTC_DAYOFMONTH_MIN));

		RTCx->ADOM = ALValue & RTC_DOM_MASK;
		break;

	case RTC_TIMETYPE_DAYOFYEAR:
		CHECK_PARAM((ALValue >= RTC_DAYOFYEAR_MIN) \
				&& (ALValue <= RTC_DAYOFYEAR_MAX));

		RTCx->ADOY = ALValue & RTC_DOY_MASK;
		break;

	case RTC_TIMETYPE_MONTH:
		CHECK_PARAM((ALValue >= RTC_MONTH_MIN) \
				&& (ALValue <= RTC_MONTH_MAX));

		RTCx->AMON = ALValue & RTC_MONTH_MASK;
		break;

	case RTC_TIMETYPE_YEAR:
		CHECK_PARAM(ALValue <= RTC_YEAR_MAX);

		RTCx->AYRS = ALValue & RTC_YEAR_MASK;
		break;
	}
}



/*********************************************************************//**
 * @brief 		Get alarm time value for each time type
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	Timetype Time Type, should be:
 * 					- RTC_TIMETYPE_SECOND
 * 					- RTC_TIMETYPE_MINUTE
 * 					- RTC_TIMETYPE_HOUR
 * 					- RTC_TIMETYPE_DAYOFWEEK
 * 					- RTC_TIMETYPE_DAYOFMONTH
 * 					- RTC_TIMETYPE_DAYOFYEAR
 * 					- RTC_TIMETYPE_MONTH
 * 					- RTC_TIMETYPE_YEAR
  * @return 	Value of Alarm time according to specified time type
 **********************************************************************/
uint32_t RTC_GetAlarmTime (LPC_RTC_Type *RTCx, uint32_t Timetype)
{
	switch (Timetype)
	{
	case RTC_TIMETYPE_SECOND:
		return (RTCx->ASEC & RTC_SEC_MASK);
	case RTC_TIMETYPE_MINUTE:
		return (RTCx->AMIN & RTC_MIN_MASK);
	case RTC_TIMETYPE_HOUR:
		return (RTCx->AHRS & RTC_HOUR_MASK);
	case RTC_TIMETYPE_DAYOFWEEK:
		return (RTCx->ADOW & RTC_DOW_MASK);
	case RTC_TIMETYPE_DAYOFMONTH:
		return (RTCx->ADOM & RTC_DOM_MASK);
	case RTC_TIMETYPE_DAYOFYEAR:
		return (RTCx->ADOY & RTC_DOY_MASK);
	case RTC_TIMETYPE_MONTH:
		return (RTCx->AMON & RTC_MONTH_MASK);
	case RTC_TIMETYPE_YEAR:
		return (RTCx->AYRS & RTC_YEAR_MASK);
	default:
		return (0);
	}
}


/*********************************************************************//**
 * @brief 		Set full of alarm time in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	pFullTime Pointer to a RTC_TIME_Type structure that
 * 				contains alarm time value in full.
 * @return 		None
 **********************************************************************/
void RTC_SetFullAlarmTime (LPC_RTC_Type *RTCx, RTC_TIME_Type *pFullTime)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	RTCx->ADOM = pFullTime->DOM & RTC_DOM_MASK;
	RTCx->ADOW = pFullTime->DOW & RTC_DOW_MASK;
	RTCx->ADOY = pFullTime->DOY & RTC_DOY_MASK;
	RTCx->AHRS = pFullTime->HOUR & RTC_HOUR_MASK;
	RTCx->AMIN = pFullTime->MIN & RTC_MIN_MASK;
	RTCx->ASEC = pFullTime->SEC & RTC_SEC_MASK;
	RTCx->AMON = pFullTime->MONTH & RTC_MONTH_MASK;
	RTCx->AYRS = pFullTime->YEAR & RTC_YEAR_MASK;
}


/*********************************************************************//**
 * @brief 		Get full of alarm time in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	pFullTime Pointer to a RTC_TIME_Type structure that
 * 				will be stored alarm time in full.
 * @return 		None
 **********************************************************************/
void RTC_GetFullAlarmTime (LPC_RTC_Type *RTCx, RTC_TIME_Type *pFullTime)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));

	pFullTime->DOM = RTCx->ADOM & RTC_DOM_MASK;
	pFullTime->DOW = RTCx->ADOW & RTC_DOW_MASK;
	pFullTime->DOY = RTCx->ADOY & RTC_DOY_MASK;
	pFullTime->HOUR = RTCx->AHRS & RTC_HOUR_MASK;
	pFullTime->MIN = RTCx->AMIN & RTC_MIN_MASK;
	pFullTime->SEC = RTCx->ASEC & RTC_SEC_MASK;
	pFullTime->MONTH = RTCx->AMON & RTC_MONTH_MASK;
	pFullTime->YEAR = RTCx->AYRS & RTC_YEAR_MASK;
}


/*********************************************************************//**
 * @brief 		Check whether if specified Location interrupt in
 * 				RTC peripheral is set or not
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	IntType Interrupt location type, should be:
 * 					- RTC_INT_COUNTER_INCREASE: Counter Increment Interrupt block generated an interrupt.
 * 					- RTC_INT_ALARM: Alarm generated an interrupt.
 * @return 		New state of specified Location interrupt in RTC peripheral
 * 					- SET
 * 					- RESET
 **********************************************************************/
IntStatus RTC_GetIntPending (LPC_RTC_Type *RTCx, uint32_t IntType)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_RTC_INT(IntType));

	return ((RTCx->ILR & IntType) ? SET : RESET);
}


/*********************************************************************//**
 * @brief 		Clear specified Location interrupt pending in
 * 				RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	IntType Interrupt location type, should be:
 * 					- RTC_INT_COUNTER_INCREASE	:Clear Counter Increment Interrupt pending.
 * 					- RTC_INT_ALARM				:Clear alarm interrupt pending
 * @return 		None
 **********************************************************************/
void RTC_ClearIntPending (LPC_RTC_Type *RTCx, uint32_t IntType)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_RTC_INT(IntType));

	RTCx->ILR = IntType;
}

/*********************************************************************//**
 * @brief 		Enable/Disable calibration counter in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	NewState New State of this function, should be:
 * 					- ENABLE	:The calibration counter is enabled and counting
 * 					- DISABLE	:The calibration counter is disabled and reset to zero
 * @return 		None
 **********************************************************************/
void RTC_CalibCounterCmd(LPC_RTC_Type *RTCx, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_FUNCTIONALSTATE(NewState));

	if (NewState == ENABLE)
	{
		do
		{
		RTCx->CCR &= (~RTC_CCR_CCALEN) & RTC_CCR_BITMASK;
		}while(RTCx->CCR&RTC_CCR_CCALEN);
	}
	else
	{
		RTCx->CCR |= RTC_CCR_CCALEN;
	}
}


/*********************************************************************//**
 * @brief 		Configures Calibration in RTC peripheral
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	CalibValue Calibration value, should be in range from
 * 					0 to 131,072
 * @param[in]	CalibDir Calibration Direction, should be:
 * 					- RTC_CALIB_DIR_FORWARD		:Forward calibration
 * 					- RTC_CALIB_DIR_BACKWARD	:Backward calibration
 * @return 		None
 **********************************************************************/
void RTC_CalibConfig(LPC_RTC_Type *RTCx, uint32_t CalibValue, uint8_t CalibDir)
{
	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_RTC_CALIB_DIR(CalibDir));
	CHECK_PARAM(CalibValue < RTC_CALIBRATION_MAX);

	RTCx->CALIBRATION = ((CalibValue - 1) & RTC_CALIBRATION_CALVAL_MASK) \
			| ((CalibDir == RTC_CALIB_DIR_BACKWARD) ? RTC_CALIBRATION_LIBDIR : 0);
}


/*********************************************************************//**
 * @brief 		Write value to General purpose registers
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	Channel General purpose registers Channel number,
 * 				should be in range from 0 to 63.
 * @param[in]	Value Value to write
 * @return 		None
 * Note: These General purpose registers can be used to store important
 * information when the main power supply is off. The value in these
 * registers is not affected by chip reset.
 **********************************************************************/
void RTC_WriteGPREG (LPC_RTC_Type *RTCx, uint8_t Channel, uint32_t Value)
{
	uint32_t *preg;

	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_RTC_GPREG_CH(Channel));

	preg = (uint32_t *)RTC_GPREG_BASE;
	preg += Channel;
	*preg = Value;
}


/*********************************************************************//**
 * @brief 		Read value from General purpose registers
 * @param[in]	RTCx	RTC peripheral selected, should be LPC_RTC
 * @param[in]	Channel General purpose registers Channel number,
 * 				should be in range from 0 to 4.
 * @return 		Read Value
 * Note: These General purpose registers can be used to store important
 * information when the main power supply is off. The value in these
 * registers is not affected by chip reset.
 **********************************************************************/
uint32_t RTC_ReadGPREG (LPC_RTC_Type *RTCx, uint8_t Channel)
{
	uint32_t *preg;
	uint32_t value;

	CHECK_PARAM(PARAM_RTCx(RTCx));
	CHECK_PARAM(PARAM_RTC_GPREG_CH(Channel));

	preg = (uint32_t *)RTC_GPREG_BASE;
	preg += Channel;
	value = *preg;
	return (value);
}

/**
 * @}
 */

#endif /* _RTC */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */

