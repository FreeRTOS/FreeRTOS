/**********************************************************************
* $Id$		lpc18xx_timer.c		2011-06-02
*//**
* @file		lpc18xx_timer.c
* @brief	Contains all functions support for Timer firmware library on LPC18xx
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
/** @addtogroup TIMER
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_timer.h"
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

#ifdef _TIM

/* Private Functions ---------------------------------------------------------- */

static uint32_t getPClock (uint32_t timernum);
static uint32_t converUSecToVal (uint32_t timernum, uint32_t usec);
static uint32_t converPtrToTimeNum (LPC_TIMERn_Type *TIMx);


/*********************************************************************//**
 * @brief 		Get peripheral clock of each timer controller
 * @param[in]	timernum Timer number, should be: 0..3
 * @return 		Peripheral clock of timer
 **********************************************************************/
extern uint32_t M3Frequency;
static uint32_t getPClock (uint32_t timernum)
{
	uint32_t clkdlycnt;
	switch (timernum)
	{
	case 0:
		clkdlycnt = /*CGU_GetPCLK (CGU_PCLKSEL_TIMER0)*/ CGU_GetPCLKFrequency(CGU_PERIPHERAL_TIMER0);
		break;

	case 1:
		clkdlycnt = /*CGU_GetPCLK (CGU_PCLKSEL_TIMER1)*/ CGU_GetPCLKFrequency(CGU_PERIPHERAL_TIMER1);
		break;

	case 2:
		clkdlycnt = /*CGU_GetPCLK (CGU_PCLKSEL_TIMER2)*/ CGU_GetPCLKFrequency(CGU_PERIPHERAL_TIMER2);
		break;

	case 3:
		clkdlycnt = /*CGU_GetPCLK (CGU_PCLKSEL_TIMER3)*/ CGU_GetPCLKFrequency(CGU_PERIPHERAL_TIMER3);
		break;
	}
	return clkdlycnt;
}


/*********************************************************************//**
 * @brief 		Convert a time to a timer count value
 * @param[in]	timernum Timer number, should be: 0..3
 * @param[in]	usec Time in microseconds
 * @return 		The number of required clock ticks to give the time delay
 **********************************************************************/
uint32_t converUSecToVal (uint32_t timernum, uint32_t usec)
{
	uint64_t clkdlycnt;

	// Get Pclock of timer
	clkdlycnt = (uint64_t) getPClock(timernum);

	clkdlycnt = (clkdlycnt * usec) / 1000000;
	return (uint32_t) clkdlycnt;
}


/*********************************************************************//**
 * @brief 		Convert a timer register pointer to a timer number
 * @param[in]	TIMx Pointer to LPC_TIMERn_Type, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @return 		The timer number (0 to 3) or -1 if register pointer is bad
 **********************************************************************/
uint32_t converPtrToTimeNum (LPC_TIMERn_Type *TIMx)
{
	uint32_t tnum = 0xFFFFFFFF;

	if (TIMx == LPC_TIMER0)
	{
		tnum = 0;
	}
	else if (TIMx == LPC_TIMER1)
	{
		tnum = 1;
	}
	else if (TIMx == LPC_TIMER2)
	{
		tnum = 2;
	}
	else if (TIMx == LPC_TIMER3)
	{
		tnum = 3;
	}

	return tnum;
}

/* End of Private Functions ---------------------------------------------------- */


/* Public Functions ----------------------------------------------------------- */
/** @addtogroup TIM_Public_Functions
 * @{
 */

/*********************************************************************//**
 * @brief 		Get Interrupt Status
 * @param[in]	TIMx Timer selection, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	IntFlag: interrupt type, should be:
 * 					- TIM_MR0_INT	:Interrupt for Match channel 0
 * 					- TIM_MR1_INT	:Interrupt for Match channel 1
 * 					- TIM_MR2_INT	:Interrupt for Match channel 2
 * 					- TIM_MR3_INT	:Interrupt for Match channel 3
 * 					- TIM_CR0_INT	:Interrupt for Capture channel 0
 * 					- TIM_CR1_INT	:Interrupt for Capture channel 1
 * @return 		FlagStatus
 * 					- SET 	:interrupt
 * 					- RESET :no interrupt
 **********************************************************************/
FlagStatus TIM_GetIntStatus(LPC_TIMERn_Type *TIMx, TIM_INT_TYPE IntFlag)
{
	uint8_t temp;
	CHECK_PARAM(PARAM_TIMx(TIMx));
	CHECK_PARAM(PARAM_TIM_INT_TYPE(IntFlag));
	temp = (TIMx->IR)& TIM_IR_CLR(IntFlag);
	if (temp)
		return SET;

	return RESET;

}
/*********************************************************************//**
 * @brief 		Get Capture Interrupt Status
 * @param[in]	TIMx Timer selection, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	IntFlag: interrupt type, should be:
 * 					- TIM_MR0_INT	:Interrupt for Match channel 0
 * 					- TIM_MR1_INT	:Interrupt for Match channel 1
 * 					- TIM_MR2_INT	:Interrupt for Match channel 2
 * 					- TIM_MR3_INT	:Interrupt for Match channel 3
 * 					- TIM_CR0_INT	:Interrupt for Capture channel 0
 * 					- TIM_CR1_INT	:Interrupt for Capture channel 1
 * @return 		FlagStatus
 * 					- SET 	:interrupt
 * 					- RESET :no interrupt
 **********************************************************************/
FlagStatus TIM_GetIntCaptureStatus(LPC_TIMERn_Type *TIMx, TIM_INT_TYPE IntFlag)
{
	uint8_t temp;
	CHECK_PARAM(PARAM_TIMx(TIMx));
	CHECK_PARAM(PARAM_TIM_INT_TYPE(IntFlag));
	temp = (TIMx->IR) & (1<<(4+IntFlag));
	if(temp)
		return SET;
	return RESET;
}
/*********************************************************************//**
 * @brief 		Clear Interrupt pending
 * @param[in]	TIMx Timer selection, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	IntFlag: interrupt type, should be:
 * 					- TIM_MR0_INT	:Interrupt for Match channel 0
 * 					- TIM_MR1_INT	:Interrupt for Match channel 1
 * 					- TIM_MR2_INT	:Interrupt for Match channel 2
 * 					- TIM_MR3_INT	:Interrupt for Match channel 3
 * 					- TIM_CR0_INT	:Interrupt for Capture channel 0
 * 					- TIM_CR1_INT	:Interrupt for Capture channel 1
 * @return 		None
 **********************************************************************/
void TIM_ClearIntPending(LPC_TIMERn_Type *TIMx, TIM_INT_TYPE IntFlag)
{
	CHECK_PARAM(PARAM_TIMx(TIMx));
	CHECK_PARAM(PARAM_TIM_INT_TYPE(IntFlag));
	TIMx->IR = TIM_IR_CLR(IntFlag);
}

/*********************************************************************//**
 * @brief 		Clear Capture Interrupt pending
 * @param[in]	TIMx Timer selection, should be
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	IntFlag interrupt type, should be:
 * 					- TIM_MR0_INT	:Interrupt for Match channel 0
 * 					- TIM_MR1_INT	:Interrupt for Match channel 1
 * 					- TIM_MR2_INT	:Interrupt for Match channel 2
 * 					- TIM_MR3_INT	:Interrupt for Match channel 3
 * 					- TIM_CR0_INT	:Interrupt for Capture channel 0
 * 					- TIM_CR1_INT	:Interrupt for Capture channel 1
 * @return 		None
 **********************************************************************/
void TIM_ClearIntCapturePending(LPC_TIMERn_Type *TIMx, TIM_INT_TYPE IntFlag)
{
	CHECK_PARAM(PARAM_TIMx(TIMx));
	CHECK_PARAM(PARAM_TIM_INT_TYPE(IntFlag));
	TIMx->IR = (1<<(4+IntFlag));
}

/*********************************************************************//**
 * @brief 		Configuration for Timer at initial time
 * @param[in] 	TimerCounterMode timer counter mode, should be:
 * 					- TIM_TIMER_MODE			:Timer mode
 * 					- TIM_COUNTER_RISING_MODE	:Counter rising mode
 * 					- TIM_COUNTER_FALLING_MODE	:Counter falling mode
 * 					- TIM_COUNTER_ANY_MODE		:Counter on both edges
 * @param[in] 	TIM_ConfigStruct pointer to TIM_TIMERCFG_Type or
 * 				TIM_COUNTERCFG_Type
 * @return 		None
 **********************************************************************/
void TIM_ConfigStructInit(TIM_MODE_OPT TimerCounterMode, void *TIM_ConfigStruct)
{
	if (TimerCounterMode == TIM_TIMER_MODE )
	{
		TIM_TIMERCFG_Type * pTimeCfg = (TIM_TIMERCFG_Type *)TIM_ConfigStruct;
		pTimeCfg->PrescaleOption = TIM_PRESCALE_USVAL;
		pTimeCfg->PrescaleValue = 1;
	}
	else
	{
		TIM_COUNTERCFG_Type * pCounterCfg = (TIM_COUNTERCFG_Type *)TIM_ConfigStruct;
		pCounterCfg->CountInputSelect = TIM_COUNTER_INCAP0;
	}
}

/*********************************************************************//**
 * @brief 		Initial Timer/Counter device
 * 				 	Set Clock frequency for Timer
 * 					Set initial configuration for Timer
 * @param[in]	TIMx  Timer selection, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	TimerCounterMode Timer counter mode, should be:
 * 					- TIM_TIMER_MODE			:Timer mode
 * 					- TIM_COUNTER_RISING_MODE	:Counter rising mode
 * 					- TIM_COUNTER_FALLING_MODE	:Counter falling mode
 * 					- TIM_COUNTER_ANY_MODE		:Counter on both edges
 * @param[in]	TIM_ConfigStruct pointer to TIM_TIMERCFG_Type
 * 				that contains the configuration information for the
 *                    specified Timer peripheral.
 * @return 		None
 **********************************************************************/
void TIM_Init(LPC_TIMERn_Type *TIMx, TIM_MODE_OPT TimerCounterMode, void *TIM_ConfigStruct)
{
	TIM_TIMERCFG_Type *pTimeCfg;
	TIM_COUNTERCFG_Type *pCounterCfg;

	CHECK_PARAM(PARAM_TIMx(TIMx));
	CHECK_PARAM(PARAM_TIM_MODE_OPT(TimerCounterMode));

	//set power
	if (TIMx== LPC_TIMER0)
	{

	}
	else if (TIMx== LPC_TIMER1)
	{

	}

	else if (TIMx== LPC_TIMER2)
	{

	}
	else if (TIMx== LPC_TIMER3)
	{

	}

	TIMx->CCR &= ~TIM_CTCR_MODE_MASK;
	TIMx->CCR |= TIM_TIMER_MODE;

	TIMx->TC =0;
	TIMx->PC =0;
	TIMx->PR =0;
	TIMx->TCR |= (1<<1); //Reset Counter
	TIMx->TCR &= ~(1<<1); //release reset
	if (TimerCounterMode == TIM_TIMER_MODE )
	{
		pTimeCfg = (TIM_TIMERCFG_Type *)TIM_ConfigStruct;
		if (pTimeCfg->PrescaleOption  == TIM_PRESCALE_TICKVAL)
		{
			TIMx->PR   = pTimeCfg->PrescaleValue -1  ;
		}
		else
		{
			TIMx->PR   = converUSecToVal (converPtrToTimeNum(TIMx),pTimeCfg->PrescaleValue)-1;
		}
	}
	else
	{

		pCounterCfg = (TIM_COUNTERCFG_Type *)TIM_ConfigStruct;
		TIMx->CCR  &= ~TIM_CTCR_INPUT_MASK;
		if (pCounterCfg->CountInputSelect == TIM_COUNTER_INCAP1)
			TIMx->CCR |= _BIT(2);
	}

	// Clear interrupt pending
	TIMx->IR = 0xFFFFFFFF;

}

/*********************************************************************//**
 * @brief 		Close Timer/Counter device
 * @param[in]	TIMx  Pointer to timer device, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @return 		None
 **********************************************************************/
void TIM_DeInit (LPC_TIMERn_Type *TIMx)
{
	CHECK_PARAM(PARAM_TIMx(TIMx));
	// Disable timer/counter
	TIMx->TCR = 0x00;

}

/*********************************************************************//**
 * @brief	 	Start/Stop Timer/Counter device
 * @param[in]	TIMx Pointer to timer device, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	NewState
 * 					- ENABLE  	:Set timer enable
 * 					- DISABLE 	:Disable timer
 * @return 		None
 **********************************************************************/
void TIM_Cmd(LPC_TIMERn_Type *TIMx, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_TIMx(TIMx));
	if (NewState == ENABLE)
	{
		TIMx->TCR	|=  TIM_ENABLE;
	}
	else
	{
		TIMx->TCR &= ~TIM_ENABLE;
	}
}

/*********************************************************************//**
 * @brief 		Reset Timer/Counter device,
 * 					Make TC and PC are synchronously reset on the next
 * 					positive edge of PCLK
 * @param[in]	TIMx Pointer to timer device, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @return 		None
 **********************************************************************/
void TIM_ResetCounter(LPC_TIMERn_Type *TIMx)
{
	CHECK_PARAM(PARAM_TIMx(TIMx));
	TIMx->TCR |= TIM_RESET;
	TIMx->TCR &= ~TIM_RESET;
}

/*********************************************************************//**
 * @brief 		Configuration for Match register
 * @param[in]	TIMx Pointer to timer device, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]   TIM_MatchConfigStruct Pointer to TIM_MATCHCFG_Type
 * 					- MatchChannel 	: choose channel 0 or 1
 * 					- IntOnMatch	: if SET, interrupt will be generated when MRxx match
 * 									the value in TC
 * 					- StopOnMatch	: if SET, TC and PC will be stopped whenM Rxx match
 * 									the value in TC
 * 					- ResetOnMatch 	: if SET, Reset on MR0 when MRxx match
 * 									the value in TC
 * 					-ExtMatchOutputType: Select output for external match
 * 						 +	 0:	Do nothing for external output pin if match
 *						 +   1:	Force external output pin to low if match
 *						 + 	 2: Force external output pin to high if match
 *						 + 	 3: Toggle external output pin if match
 *					MatchValue: Set the value to be compared with TC value
 * @return 		None
 **********************************************************************/
void TIM_ConfigMatch(LPC_TIMERn_Type *TIMx, TIM_MATCHCFG_Type *TIM_MatchConfigStruct)
{

	CHECK_PARAM(PARAM_TIMx(TIMx));
	CHECK_PARAM(PARAM_TIM_EXTMATCH_OPT(TIM_MatchConfigStruct->ExtMatchOutputType));

	switch(TIM_MatchConfigStruct->MatchChannel)
	{
	case 0:
		TIMx->MR[0] = TIM_MatchConfigStruct->MatchValue;
		break;
	case 1:
		TIMx->MR[1] = TIM_MatchConfigStruct->MatchValue;
		break;
	case 2:
		TIMx->MR[2] = TIM_MatchConfigStruct->MatchValue;
		break;
	case 3:
		TIMx->MR[3] = TIM_MatchConfigStruct->MatchValue;
		break;
	default:
		//Error match value
		//Error loop
		while(1);
	}
	//interrupt on MRn
	TIMx->MCR &=~TIM_MCR_CHANNEL_MASKBIT(TIM_MatchConfigStruct->MatchChannel);

	if (TIM_MatchConfigStruct->IntOnMatch)
		TIMx->MCR |= TIM_INT_ON_MATCH(TIM_MatchConfigStruct->MatchChannel);

	//reset on MRn
	if (TIM_MatchConfigStruct->ResetOnMatch)
		TIMx->MCR |= TIM_RESET_ON_MATCH(TIM_MatchConfigStruct->MatchChannel);

	//stop on MRn
	if (TIM_MatchConfigStruct->StopOnMatch)
		TIMx->MCR |= TIM_STOP_ON_MATCH(TIM_MatchConfigStruct->MatchChannel);

	// match output type

	TIMx->EMR 	&= ~TIM_EM_MASK(TIM_MatchConfigStruct->MatchChannel);
	TIMx->EMR   |= TIM_EM_SET(TIM_MatchConfigStruct->MatchChannel,TIM_MatchConfigStruct->ExtMatchOutputType);
}
/*********************************************************************//**
 * @brief 		Update Match value
 * @param[in]	TIMx Pointer to timer device, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	MatchChannel	Match channel, should be: 0..3
 * @param[in]	MatchValue		updated match value
 * @return 		None
 **********************************************************************/
void TIM_UpdateMatchValue(LPC_TIMERn_Type *TIMx,uint8_t MatchChannel, uint32_t MatchValue)
{
	CHECK_PARAM(PARAM_TIMx(TIMx));
	switch(MatchChannel)
	{
	case 0:
		TIMx->MR[0] = MatchValue;
		break;
	case 1:
		TIMx->MR[1] = MatchValue;
		break;
	case 2:
		TIMx->MR[2] = MatchValue;
		break;
	case 3:
		TIMx->MR[3] = MatchValue;
		break;
	default:
		//Error Loop
		while(1);
	}

}
/*********************************************************************//**
 * @brief 		Configuration for Capture register
 * @param[in]	TIMx Pointer to timer device, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]   TIM_CaptureConfigStruct	Pointer to TIM_CAPTURECFG_Type
 * @return 		None
 **********************************************************************/
void TIM_ConfigCapture(LPC_TIMERn_Type *TIMx, TIM_CAPTURECFG_Type *TIM_CaptureConfigStruct)
{

	CHECK_PARAM(PARAM_TIMx(TIMx));
	TIMx->CCR &= ~TIM_CCR_CHANNEL_MASKBIT(TIM_CaptureConfigStruct->CaptureChannel);

	if (TIM_CaptureConfigStruct->RisingEdge)
		TIMx->CCR |= TIM_CAP_RISING(TIM_CaptureConfigStruct->CaptureChannel);

	if (TIM_CaptureConfigStruct->FallingEdge)
		TIMx->CCR |= TIM_CAP_FALLING(TIM_CaptureConfigStruct->CaptureChannel);

	if (TIM_CaptureConfigStruct->IntOnCaption)
		TIMx->CCR |= TIM_INT_ON_CAP(TIM_CaptureConfigStruct->CaptureChannel);
}

/*********************************************************************//**
 * @brief 		Read value of capture register in timer/counter device
 * @param[in]	TIMx Pointer to timer/counter device, should be:
 * 					- LPC_TIM0	:TIMER0 peripheral
 * 					- LPC_TIM1	:TIMER1 peripheral
 * 					- LPC_TIM2	:TIMER2 peripheral
 * 					- LPC_TIM3	:TIMER3 peripheral
 * @param[in]	CaptureChannel: capture channel number, should be:
 * 				- TIM_COUNTER_INCAP0: CAPn.0 input pin for TIMERn
 * 				- TIM_COUNTER_INCAP1: CAPn.1 input pin for TIMERn
 * 				- TIM_COUNTER_INCAP1: CAPn.2 input pin for TIMERn
 * 				- TIM_COUNTER_INCAP1: CAPn.3 input pin for TIMERn
 * @return 		Value of capture register
 **********************************************************************/
uint32_t TIM_GetCaptureValue(LPC_TIMERn_Type *TIMx, TIM_COUNTER_INPUT_OPT CaptureChannel)
{
	CHECK_PARAM(PARAM_TIMx(TIMx));
	CHECK_PARAM(PARAM_TIM_COUNTER_INPUT_OPT(CaptureChannel));

	switch(CaptureChannel){
		case 0: return TIMx->CR[0];
		case 1:	return TIMx->CR[1];
		case 2:	return TIMx->CR[2];
		case 3:	return TIMx->CR[3];
	}
	return 0;
}
/*---------------Advanced TIMER functions -----------------------------------------*/
/*********************************************************************//**
 * @brief 		Timer wait (microseconds)
 * @param[in]	time	number of microseconds waiting
 * @return 		None
 **********************************************************************/
void TIM_Waitus(uint32_t time)
{
	TIM_MATCHCFG_Type MatchConfigStruct;
	LPC_TIMER0->IR = 0xFFFFFFFF;

	MatchConfigStruct.MatchChannel = 0;
	MatchConfigStruct.IntOnMatch = ENABLE;
	MatchConfigStruct.ResetOnMatch = ENABLE;
	MatchConfigStruct.StopOnMatch = ENABLE;
	MatchConfigStruct.ExtMatchOutputType = 0;
	MatchConfigStruct.MatchValue = time;

	TIM_ConfigMatch(LPC_TIMER0, &MatchConfigStruct);
	TIM_Cmd(LPC_TIMER0,ENABLE);
	//wait until interrupt flag occur
	while(!(LPC_TIMER0->IR & 0x01));
	TIM_ResetCounter(LPC_TIMER0);
}
/*********************************************************************//**
 * @brief 		Timer wait (milliseconds)
 * @param[in]	time	number of millisecond waiting
 * @return 		None
 **********************************************************************/
void TIM_Waitms(uint32_t time)
{
	TIM_Waitus(time * 1000);
}
/**
 * @}
 */

#endif /* _TIMER */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
