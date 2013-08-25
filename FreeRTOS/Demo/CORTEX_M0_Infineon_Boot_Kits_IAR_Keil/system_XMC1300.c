/******************************************************************************
 * @file     system_XMC1300.c
 * @brief    Device specific initialization for the XMC1300-Series according 
 * to CMSIS
 * @version  V1.2
 * @date     13 Dec 2012
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
 * ************************** Change history *********************************
 * V1.2, 13 Dec 2012, PKB, Created this table, Changed System_ to system_
 */

#include "system_XMC1300.h"
#include <XMC1300.h>

/*---------------------------------------------------------------------------
 Extern definitions 
 *--------------------------------------------------------------------------*/
extern uint32_t AllowClkInitByStartup(void);

/*----------------------------------------------------------------------------
  Clock Global defines
 *----------------------------------------------------------------------------*/
#define DCO_DCLK       64000000UL

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
/*!< System Clock Frequency (Core Clock)*/
uint32_t SystemCoreClock;


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
  uint32_t IDIV, CLKCR;

  CLKCR = SCU_CLOCK -> CLKCR;
  
  IDIV = (CLKCR & SCU_CLOCK_CLKCR_IDIV_Msk) >> SCU_CLOCK_CLKCR_IDIV_Pos;
  
  if(IDIV)
  {
    SystemCoreClock = DCO_DCLK / (2 * IDIV );
  }
  else
  {
    /* Divider bypassed */
    SystemCoreClock = DCO_DCLK;
  }
}

