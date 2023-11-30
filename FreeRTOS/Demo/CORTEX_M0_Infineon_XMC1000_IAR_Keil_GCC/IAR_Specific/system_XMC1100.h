/******************************************************************************
 * @file     system_XMC1100.h
 * @brief    Device specific initialization for the XMC1100-Series according 
 * to CMSIS
 * @version  V1.1
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
 * *************************** Change history ********************************
 * V1.1, 13 Dec 2012, PKB : Created change history table, extern reference
 */
#include <stdint.h>

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
extern uint32_t SystemCoreClock;

/**
  * @brief  Setup the microcontroller system.
  *         Initialize the PLL and update the 
  *         SystemCoreClock variable.
  * @param  None
  * @retval None
  */
void SystemInit(void);

/**
  * @brief  Update SystemCoreClock according to Clock Register Values
  * @note   -  
  * @param  None
  * @retval None
  */
void SystemCoreClockUpdate(void);

