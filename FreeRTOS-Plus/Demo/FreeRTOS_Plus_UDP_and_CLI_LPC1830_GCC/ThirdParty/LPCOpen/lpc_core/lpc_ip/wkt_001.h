/*
 * @brief Self Wakeup Timer (WKT) registers and functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __WKT_001_H_
#define __WKT_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_WKT_001 IP: Self Wakeup Timer (WKT) register block and driver
 * @ingroup IP_Drivers
 * Self Wakeup Timer
 * @{
 */

/**
 * @brief Self wake-up timer register block structure
 */
typedef struct {
	__IO uint32_t  CTRL;	/*!< Offset: 0x000 Alarm/Wakeup Timer Control register */
	uint32_t  Reserved[2];
	__IO uint32_t  COUNT;	/*!< Offset: 0x000C Alarm/Wakeup Timer Counter register */
} IP_WKT_001_T;

/**
 * WKT Control register bit fields & masks
 */
#define WKT_CTRL_CLKSEL        ((uint32_t) (1 << 0))	/*!< Select the self wake-up timer clock source */
#define WKT_CTRL_ALARMFLAG     ((uint32_t) (1 << 1))	/*!< Wake-up or alarm timer flag */
#define WKT_CTRL_CLEARCTR      ((uint32_t) (1 << 2))	/*!< Clears the self wake-up timer */

/**
 * WKT Clock source values enum
 */
typedef enum IP_WKT_CLKSRC {
	IP_WKT_CLKSRC_DIVIRC = 0,	/*!< Divided IRC clock - runs at 750kHz */
	IP_WKT_CLKSRC_10KHZ = 1	    /*!< Low power clock - runs at 10kHz */
} IP_WKT_CLKSRC_T;

/**
 * @brief	Clear WKT interrupt status
 * @param   pWKT    :   Pointer to WKT register block
 * @return	Nothing
 */
STATIC INLINE void IP_WKT_ClearIntStatus(IP_WKT_001_T *pWKT)
{
	if ( pWKT->CTRL & WKT_CTRL_ALARMFLAG ) {
		pWKT->CTRL |= WKT_CTRL_ALARMFLAG;
	}
}

/**
 * @brief	Clear and stop WKT counter
 * @param   pWKT    :   Pointer to WKT register block
 * @return	Nothing
 */
STATIC INLINE void IP_WKT_Stop(IP_WKT_001_T *pWKT)
{
	pWKT->CTRL |= WKT_CTRL_CLEARCTR;
}

/**
 * @brief	Set the WKT clock source
 * @param   pWKT    :   Pointer to WKT register block
 * @param   clkSrc  :   WKT Clock source(WKT_CLKSRC_10KHZ or WKT_CLKSRC_DIVIRC)
 * @return	Nothing
 */
STATIC INLINE void IP_WKT_SetClockSource(IP_WKT_001_T *pWKT, IP_WKT_CLKSRC_T clkSrc)
{
	if (clkSrc == IP_WKT_CLKSRC_10KHZ) {
		pWKT->CTRL |= WKT_CTRL_CLKSEL;	/* using Low Power clock 10kHz */
	}
	else {
		pWKT->CTRL &= ~WKT_CTRL_CLKSEL;	/* using Divided IRC clock 750kHz */
	}
}

/**
 * @brief	Set the WKT counter value & start the counter
 * @param   pWKT    :   Pointer to WKT register block
 * @param   cntVal  :   WKT Counter value
 * @return	Nothing
 */
STATIC INLINE void IP_WKT_Start(IP_WKT_001_T *pWKT, uint32_t cntVal)
{
	pWKT->COUNT = cntVal;
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __WKT_001_H_ */
