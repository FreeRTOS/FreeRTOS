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

#ifndef __GPIO_003_H_
#define __GPIO_003_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_GPIO_003 IP: GPIO register block and driver (003)
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief  GPIO port register block structure
 */
typedef struct {				/*!< GPIO_PORT Structure */
	__IO uint32_t DATA[4096];			/*!< Offset: 0x0000 to 0x3FFC Data address masking register (R/W) */
	uint32_t RESERVED1[4096];
	__IO uint32_t DIR;					/*!< Offset: 0x8000 Data direction register (R/W) */
	__IO uint32_t IS;					/*!< Offset: 0x8004 Interrupt sense register (R/W) */
	__IO uint32_t IBE;					/*!< Offset: 0x8008 Interrupt both edges register (R/W) */
	__IO uint32_t IEV;					/*!< Offset: 0x800C Interrupt event register  (R/W) */
	__IO uint32_t IE;					/*!< Offset: 0x8010 Interrupt mask register (R/W) */
	__I  uint32_t RIS;					/*!< Offset: 0x8014 Raw interrupt status register (R/ ) */
	__I  uint32_t MIS;					/*!< Offset: 0x8018 Masked interrupt status register (R/ ) */
	__O  uint32_t IC;					/*!< Offset: 0x801C Interrupt clear register (W) */
} IP_GPIO_003_T;

/**
 * @brief	Initialize GPIO block
 * @param	pGPIO	: the base address of the GPIO block
 * @return	Nothing
 */
STATIC INLINE void IP_GPIO_Init(IP_GPIO_003_T *pGPIO)
{}

/**
 * @brief	Write data to port
 * @param	pGPIO	: the base address of the GPIO block
 * @param	mask	: determines which pins will be written. bits [11:0] address pins PIOn.0~PIOn.11.
 *						If bit's value is 1, the state of the relevant pin  is updated. Otherwise, it is unchanged.
 * @param	val	: bit values.
 * @return	Nothing
 * @note		mask is in range 0~4095.
 */
STATIC INLINE void IP_GPIO_WritePort(IP_GPIO_003_T *pGPIO, uint16_t mask, uint16_t val)
{
	pGPIO->DATA[mask] = val;
}

/**
 * @brief	Set state of pin
 * @param	pGPIO	: the base address of the GPIO block
 * @param	pin		: pin number (0-11)
 * @param	val		: true for high, false for low
 * @return	Nothing
 */
STATIC INLINE void IP_GPIO_WritePortBit(IP_GPIO_003_T *pGPIO, uint8_t pin, bool val)
{
	pGPIO->DATA[1 << pin] = val << pin;
}

/**
 * @brief	Read port state
 * @param	pGPIO	: the base address of the GPIO block
 * @return	Port value. A 1-bit indicate the relevant pins is high.
 */
STATIC INLINE uint32_t IP_GPIO_ReadPort(IP_GPIO_003_T *pGPIO)
{
	return pGPIO->DATA[4095];
}

/**
 * @brief	Read pin state
 * @param	pGPIO	: the base address of the GPIO block
 * @param	pin		: pin number (0-11)
 * @return	true of the GPIO is high, false if low
 */
STATIC INLINE bool IP_GPIO_ReadPortBit(IP_GPIO_003_T *pGPIO, uint8_t pin)
{
	return (bool) ((pGPIO->DATA[1 << pin] >> pin) & 1);
}

/**
 * @brief	Set GPIO direction for a pin
 * @param	pGPIO	: the base address of the GPIO block
 * @param	pin		: pin number (0-11)
 * @param	dir		: true for output, false for input
 * @return	Nothing
 */
STATIC INLINE void IP_GPIO_WriteDirBit(IP_GPIO_003_T *pGPIO, uint8_t pin, bool dir)
{
	if (dir) {
		pGPIO->DIR |= 1UL << pin;
	}
	else {
		pGPIO->DIR &= ~(1UL << pin);
	}
}

/**
 * @brief	Set GPIO direction for a port
 * @param	pGPIO	: the base address of the GPIO block
 * @param	bitVal	: bit value
 * @param	dir		: true for output, false for input
 * @return	Nothing
 */
STATIC INLINE void IP_GPIO_SetDir(IP_GPIO_003_T *pGPIO, uint32_t bitVal, bool dir)
{
	if (dir) {
		pGPIO->DIR |= bitVal;
	}
	else {
		pGPIO->DIR &= ~bitVal;
	}
}

/**
 * @brief	Read a GPIO direction (out or in)
 * @param	pGPIO	: the base address of the GPIO block
 * @param	pin		: pin number (0-11)
 * @return	true of the GPIO is an output, false if input
 */
STATIC INLINE bool IP_GPIO_ReadDirBit(IP_GPIO_003_T *pGPIO, uint8_t pin)
{
	return (bool) (((pGPIO->DIR) >> pin) & 1);
}

typedef enum {
	GPIOPININT_FALLING_EDGE = 0,			/*!<Selects interrupt on pin x to be triggered on FALLING level*/
	GPIOPININT_ACTIVE_LOW_LEVEL = 1,			/*!<Selects interrupt on pin x to be triggered on LOW level*/
	GPIOPININT_RISING_EDGE = (1 << 12),				/*!<Selects interrupt on pin x to be triggered on RISING level*/
	GPIOPININT_ACTIVE_HIGH_LEVEL = 1 | (1 << 12),	/*!<Selects interrupt on pin x to be triggered on HIGH level*/
	GPIOPININT_BOTH_EDGES = (1 << 24),				/*!<Selects interrupt on pin x to be triggered on both edges*/
} IP_GPIOPININT_MODE_T;

/**
 * @brief	Configure GPIO Interrupt
 * @param	pGPIO : pointer to GPIO interrupt register block
 * @param	pin		: GPIO port number interrupt
 * @param	mode	: Interrupt mode.
 * @return	None
 */
void IP_GPIO_IntCmd(IP_GPIO_003_T *pGPIO, uint8_t pin, IP_GPIOPININT_MODE_T mode);

/**
 * @brief	Get GPIO Interrupt Status
 * @param	pGPIO : pointer to GPIO interrupt register block
 * @param	pin		: pin number
 * @return	true if interrupt is pending, otherwise false
 */
STATIC INLINE bool IP_GPIO_IntGetStatus(IP_GPIO_003_T *pGPIO, uint8_t pin)
{
	return (bool) (((pGPIO->RIS) >> pin) & 0x01);
}

/**
 * @brief	Clear GPIO Interrupt (Edge interrupt cases only)
 * @param	pGPIO : pointer to GPIO interrupt register block
 * @param	pin		: pin number
 * @return	None
 */
STATIC INLINE void IP_GPIO_IntClear(IP_GPIO_003_T *pGPIO, uint8_t pin)
{
	pGPIO->IC |= (1 << pin);
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __GPIO_003_H_ */
