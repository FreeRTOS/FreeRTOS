/*
 * @brief Multi-Rate Timer (MRT) registers and driver functions
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

#ifndef __MRT_001_H_
#define __MRT_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_MRT_001 IP: MRT register block and driver
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief MRT register block structure
 */
typedef struct {
	__IO uint32_t INTVAL;	/*!< Timer interval register */
	__O  uint32_t TIMER;	/*!< Timer register */
	__IO uint32_t CTRL;		/*!< Timer control register */
	__IO uint32_t STAT;		/*!< Timer status register */
} IP_MRT_001_T;

/**
 * @brief MRT register bit fields & masks
 */
/* MRT Time interval register bit fields */
#define IP_MRT_001_INTVAL_IVALUE        (0xFFFFFF)
#define IP_MRT_001_INTVAL_LOAD          (1 << 31)

/* MRT Control register bit fields & masks */
#define IP_MRT_001_CTRL_MODE_REPEAT     (0x00)
#define IP_MRT_001_CTRL_MODE_ONESHOT    (0x01)
#define IP_MRT_001_CTRL_INTEN_MASK      (0x01)
#define IP_MRT_001_CTRL_MODE_POS        (0x01)
#define IP_MRT_001_CTRL_MODE_MASK       (0x06)
#define IP_MRT_001_CTRL_MODE_SHIFT(x)   (x << 1)

/* MRT Status register bit fields & masks */
#define IP_MRT_001_STAT_INTFLAG         (0x01)
#define IP_MRT_001_STAT_RUNNING         (0x02)

/**
 * @brief MRT Interrupt Modes enum
 */
typedef enum IP_MRT_001_MODE {
	MRT_MODE_REPEAT = 0,	/*!< MRT Repeat interrupt mode */
	MRT_MODE_ONESHOT = 1	/*!< MRT One-shot interrupt mode */
} IP_MRT_001_MODE_T;

/**
 * @brief	Initializes the MRT
 * @return	Nothing
 */
STATIC INLINE void IP_MRT_Init(void)
{}

/**
 * @brief	De-initializes the MRT Channel
 * @return	Nothing
 */
STATIC INLINE void IP_MRT_DeInit(void)
{}

/**
 * @brief	Returns the timer time interval value
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	The time interval value
 */
STATIC INLINE uint32_t IP_MRT_GetInterval(IP_MRT_001_T *pMRT)
{
	return (uint32_t) pMRT->INTVAL;
}

/**
 * @brief	Sets the timer time interval value
 * @param	pMRT	 : Pointer to selected MRT Channel
 * @param   interval : Time interval value (24-bits)
 * @return	Nothing
 * @note	Setting bit 31 in time interval register causes the time interval
 * to load immediately, otherwise the load will occur on the
 * next timer cycle
 */
STATIC INLINE void IP_MRT_SetInterval(IP_MRT_001_T *pMRT, uint32_t interval)
{
	pMRT->INTVAL = interval;
}

/**
 * @brief	Returns the current timer value
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	The current timer value
 */
STATIC INLINE uint32_t IP_MRT_GetTimer(IP_MRT_001_T *pMRT)
{
	return (uint32_t) pMRT->TIMER;
}

/**
 * @brief	Returns true if the timer is enabled
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	True if enabled, False if not enabled
 */
STATIC INLINE bool IP_MRT_GetEnabled(IP_MRT_001_T *pMRT)
{
	return (bool) (pMRT->CTRL & IP_MRT_001_CTRL_INTEN_MASK);
}

/**
 * @brief	Enables the timer
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	Nothing
 */
STATIC INLINE void IP_MRT_SetEnabled(IP_MRT_001_T *pMRT)
{
	pMRT->CTRL |= IP_MRT_001_CTRL_INTEN_MASK;
}

/**
 * @brief	Returns the timer mode (repeat or one-shot).
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	The mode (repeat or one-shot).
 */
STATIC INLINE IP_MRT_001_MODE_T IP_MRT_GetMode(IP_MRT_001_T *pMRT)
{
	return (IP_MRT_001_MODE_T) ((pMRT->CTRL & IP_MRT_001_CTRL_MODE_MASK) >> 1);
}

/**
 * @brief	Sets the timer mode to be repeat or one-shot.
 * @param	pMRT	: Pointer to selected MRT Channel
 * @param   mode    : 0 = repeat, 1 = one-shot
 * @return	Nothing
 */
STATIC INLINE void IP_MRT_SetMode(IP_MRT_001_T *pMRT, IP_MRT_001_MODE_T mode)
{
	pMRT->CTRL |= IP_MRT_001_CTRL_MODE_SHIFT(mode);
}

/**
 * @brief	Returns true if the timer is configured in repeat mode.
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	True if in repeat mode, False if in one-shot mode
 */
STATIC INLINE bool IP_MRT_IsRepeatMode(IP_MRT_001_T *pMRT)
{
	return ((pMRT->CTRL & IP_MRT_001_CTRL_MODE_MASK) > 0) ? false : true;
}

/**
 * @brief	Returns true if the timer is configured in one-shot mode.
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	True if in one-shot mode, False if in repeat mode.
 */
STATIC INLINE bool IP_MRT_IsOneShotMode(IP_MRT_001_T *pMRT)
{
	return ((pMRT->CTRL & IP_MRT_001_CTRL_MODE_MASK) > 0) ? true : false;
}

/**
 * @brief	Returns true if the timer has an interrupt pending.
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	True if interrupt is pending, False if no interrupt is pending.
 */
STATIC INLINE bool IP_MRT_IntPending(IP_MRT_001_T *pMRT)
{
	return (bool) (pMRT->STAT & IP_MRT_001_STAT_INTFLAG);
}

/**
 * @brief	Clears the pending interrupt (if any).
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	Nothing
 */
STATIC INLINE void IP_MRT_IntClear(IP_MRT_001_T *pMRT)
{
	pMRT->STAT |= IP_MRT_001_STAT_INTFLAG;
}

/**
 * @brief	Returns true if the timer is running.
 * @param	pMRT	: Pointer to selected MRT Channel
 * @return	True if running, False if stopped.
 */
STATIC INLINE bool IP_MRT_Running(IP_MRT_001_T *pMRT)
{
	return (bool) (pMRT->STAT & IP_MRT_001_STAT_RUNNING);
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __MRT_001_H_ */
