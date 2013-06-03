/*
 * @brief GPIO Registers and Functions
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

#ifndef __GPIO_001_H_
#define __GPIO_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_GPIO_001 IP: GPIO register block and driver
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief  GPIO port register block structure
 */
typedef struct {				/*!< GPIO_PORT Structure */
	__IO uint8_t B[128][32];	/*!< Offset 0x0000: Byte pin registers ports 0 to n; pins PIOn_0 to PIOn_31 */
	__IO uint32_t W[32][32];	/*!< Offset 0x1000: Word pin registers port 0 to n */
	__IO uint32_t DIR[32];		/*!< Offset 0x2000: Direction registers port n */
	__IO uint32_t MASK[32];		/*!< Offset 0x2080: Mask register port n */
	__IO uint32_t PIN[32];		/*!< Offset 0x2100: Portpin register port n */
	__IO uint32_t MPIN[32];		/*!< Offset 0x2180: Masked port register port n */
	__IO uint32_t SET[32];		/*!< Offset 0x2200: Write: Set register for port n Read: output bits for port n */
	__O  uint32_t CLR[32];		/*!< Offset 0x2280: Clear port n */
	__O  uint32_t NOT[32];		/*!< Offset 0x2300: Toggle port n */
} IP_GPIO_001_T;

/**
 * @brief	Initialize GPIO block
 * @param	pGPIO	: The Base Address of the GPIO block
 * @return	Nothing
 */
STATIC INLINE void IP_GPIO_Init(IP_GPIO_001_T *pGPIO)
{}

/**
 * @brief	Set a GPIO port/bit state
 * @param	pGPIO	: The Base Address of the GPIO block
 * @param	Port	: GPIO port to set
 * @param	Bit		: GPIO bit to set
 * @param	Setting	: true for high, false for low
 * @return	Nothing
 */
STATIC INLINE void IP_GPIO_WritePortBit(IP_GPIO_001_T *pGPIO, uint32_t Port, uint8_t Bit, bool Setting)
{
	pGPIO->B[Port][Bit] = Setting;
}

/**
 * @brief	Set a GPIO direction
 * @param	pGPIO	: The Base Address of the GPIO block
 * @param	Port	: GPIO port to set
 * @param	Bit		: GPIO bit to set
 * @param	Setting	: true for output, false for input
 * @return	Nothing
 */
STATIC INLINE void IP_GPIO_WriteDirBit(IP_GPIO_001_T *pGPIO, uint32_t Port, uint8_t Bit, bool Setting)
{
	if (Setting) {
		pGPIO->DIR[Port] |= 1UL << Bit;
	}
	else {
		pGPIO->DIR[Port] &= ~(1UL << Bit);
	}
}

/**
 * @brief	Read a GPIO state
 * @param	pGPIO	: The Base Address of the GPIO block
 * @param	Port	: GPIO port to read
 * @param	Bit		: GPIO bit to read
 * @return	true of the GPIO is high, false if low
 */
STATIC INLINE bool IP_GPIO_ReadPortBit(IP_GPIO_001_T *pGPIO, uint32_t Port, uint8_t Bit)
{
	return (bool) pGPIO->B[Port][Bit];
}

/**
 * @brief	Read a GPIO direction (out or in)
 * @param	pGPIO	: The Base Address of the GPIO block
 * @param	Port	: GPIO port to read
 * @param	Bit		: GPIO bit to read
 * @return	true of the GPIO is an output, false if input
 */
STATIC INLINE bool IP_GPIO_ReadDirBit(IP_GPIO_001_T *pGPIO, uint32_t Port, uint8_t Bit)
{
	return (bool) (((pGPIO->DIR[Port]) >> Bit) & 1);
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __GPIO_001_H_ */
