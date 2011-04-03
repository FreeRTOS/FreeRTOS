/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 *  SmartFusion A2FxxxM3 CMSIS system initialization.
 *
 * SVN $Revision: 2064 $
 * SVN $Date: 2010-01-27 15:05:58 +0000 (Wed, 27 Jan 2010) $
 */

#ifndef __SYSTEM_A2FM3FXX_H__
#define __SYSTEM_A2FM3FXX_H__

#ifdef __cplusplus
extern "C" {
#endif 

/* Standard CMSIS global variables. */
extern uint32_t SystemFrequency;    /*!< System Clock Frequency (Core Clock) */
extern uint32_t SystemCoreClock;          /*!< System Clock Frequency (Core Clock) */

/* SmartFusion specific clocks. */
extern uint32_t g_FrequencyPCLK0;   /*!< Clock frequency of APB bus 0. */  
extern uint32_t g_FrequencyPCLK1;   /*!< Clock frequency of APB bus 1. */
extern uint32_t g_FrequencyACE;     /*!< Clock frequency of Analog Compute Engine. */
extern uint32_t g_FrequencyFPGA;    /*!< Clock frequecny of FPGA fabric */

/***************************************************************************//**
 * The SystemInit() is a standard CMSIS function called during system startup.
 * It is meant to perform low level hardware setup such as configuring PLLs. In
 * the case of SmartFusion these hardware setup operations are performed by the
 * chip boot which executed before the application started. Therefore this
 * function does not need to perform any hardware setup.
 */
void SystemInit(void);

/***************************************************************************//**
 * The SystemCoreClockUpdate() is a standard CMSIS function which can be called
 * by the application in order to ensure that the SystemCoreClock global
 * variable contains the up to date Cortex-M3 core frequency. Calling this
 * function also updates the global variables containing the frequencies of the
 * APB busses connecting the peripherals and the ACE frequency.
 */
void SystemCoreClockUpdate(void);

#ifdef __cplusplus
}
#endif

#endif
