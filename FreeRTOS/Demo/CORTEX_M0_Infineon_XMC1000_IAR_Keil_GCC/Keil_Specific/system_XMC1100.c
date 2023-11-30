/******************************************************************************
 * @file     system_XMC1100.c
 * @brief    Device specific initialization for the XMC1100-Series according 
 * to CMSIS
 * @version  V1.4
 * @date     01 Feb 2013
 *
 * @note
 * Copyright (C) 2012-2013 Infineon Technologies AG. All rights reserved.

 *
 * @par
 * Infineon Technologies AG (Infineon) is supplying this software for use with 
 * Infineon’s microcontrollers.
 *   
 * This file can be freely distributed within development tools that are 
 * supporting such microcontrollers.
 *  
 *
 * @par
 * THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
 * OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
 * INFINEON SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL,
 * OR CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
 *
 ******************************************************************************/
/*
 * *************************** Change history ********************************
 * V1.2, 13 Dec 2012, PKB : Created change history table
 * V1.3, 20 Dec 2012, PKB : Fixed SystemCoreClock computation
 * V1.3, 01 Feb 2013, PKB : SCU_CLOCK -> SCU_CLK
 */

#include "system_XMC1100.h"
#include <XMC1100.h>

/*---------------------------------------------------------------------------
 Extern definitions 
 *--------------------------------------------------------------------------*/
extern uint32_t AllowClkInitByStartup(void);

/*----------------------------------------------------------------------------
  Clock Global defines
 *----------------------------------------------------------------------------*/
#define DCO_DCLK                  64000000UL
#define DCO_DCLK_MULTIPLIER       16384000UL
#define DCO_DCLK_DIVIDER          9UL
#define MCLK_MHZ                  32000000UL
#define KHZ_MULTIPLIER            1000UL
#define FRACBITS                  8UL
/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
/*!< System Clock Frequency (Core Clock) (MCLK on TIMM1) */
uint32_t SystemCoreClock;

/*----------------------------------------------------------------------------
  Fixed point math definitions
 *----------------------------------------------------------------------------*/
typedef int32_t Q_24_8;
typedef int32_t Q_15_0;

/**
  * @brief  Setup the microcontroller system.
  * @param  None
  * @retval None
  */
void SystemInit(void)
{    

  /*
   * Clock tree setup by CMSIS routines is allowed only in the absence of DAVE
   * Clock app.
   */ 
  if(AllowClkInitByStartup()){ 
  /* Do not change default values of IDIV,FDIV and RTCCLKSEL */
  /* ====== Default configuration ======= */
  /*
   * MCLK    = DCO_DCLK
   * PCLK    = MCLK
   * RTC CLK = Standby clock
   */
  }
}

/**
  * @brief  Update SystemCoreClock according to Clock Register Values
  * @note   -  
  * @param  None
  * @retval None
  */
void SystemCoreClockUpdate(void)
{
  uint32_t IDIV, FDIV, CLKCR, Clock;

  CLKCR = SCU_CLK -> CLKCR;
  IDIV = (CLKCR & SCU_CLK_CLKCR_IDIV_Msk) >> SCU_CLK_CLKCR_IDIV_Pos;
  FDIV = (CLKCR & SCU_CLK_CLKCR_FDIV_Msk) >> SCU_CLK_CLKCR_FDIV_Pos;
  
  if(IDIV)
  {
    /* Divider is enabled and used */
    if(0 == FDIV)
     {
       /* No fractional divider, so MCLK = DCO_Clk / (2 * IDIV) */
       Clock = MCLK_MHZ / IDIV;
     }
    else
     {
       /* Both integer and fractional divider must be considered */
       /* 1. IDIV + FDIV/256 */
       Q_24_8 FDiv_IDiv_Sum = (IDIV << FRACBITS) + FDIV;  

       /* 2. Fixed point division Q24.8 / Q9.8 = Q15.0 */
       Q_15_0 ClockVal = (DCO_DCLK_MULTIPLIER << FRACBITS)/ FDiv_IDiv_Sum;
       Clock = ((uint32_t)ClockVal) * KHZ_MULTIPLIER;
       Clock = Clock >> DCO_DCLK_DIVIDER;
     }
  }
  else
  {
    /* Divider bypassed. Simply divide DCO_DCLK by 2 */
    Clock = MCLK_MHZ;
  }

  /* Finally with the math class over, update SystemCoreClock */
  SystemCoreClock = Clock;  
}

