/******************************************************************************
 * @file     system_XMC1100.h
 * @brief    Device specific initialization for the XMC1300-Series according 
 * to CMSIS
 * @version  V1.2
 * @date     19 Jul 2013
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
 * *************************** Change history *********************************
 * V1.1, 13 Dec 2012, PKB, Created this table, added extern and stdint
 * V1.2, 19 Jul 2013, PKB, Added header guard, BootROM header, C++ support
 */
#ifndef SYSTEM_XMC1100_H
#define SYSTEM_XMC1100_H

/*******************************************************************************
 * HEADER FILES
 *******************************************************************************/

#include <stdint.h>

/*******************************************************************************
 * GLOBAL VARIABLES
 *******************************************************************************/

extern uint32_t SystemCoreClock;

/*******************************************************************************
 * API PROTOTYPES
 *******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Initialize the system
 *
 */
void SystemInit(void);

/**
 * @brief Initialize CPU settings
 *
 */
void SystemCoreSetup(void);

/**
 * @brief Initialize clock
 *
 */
void SystemCoreClockSetup(void);

/**
 * @brief Update SystemCoreClock variable
 *
 */
void SystemCoreClockUpdate(void);

#ifdef __cplusplus
}
#endif

#endif
