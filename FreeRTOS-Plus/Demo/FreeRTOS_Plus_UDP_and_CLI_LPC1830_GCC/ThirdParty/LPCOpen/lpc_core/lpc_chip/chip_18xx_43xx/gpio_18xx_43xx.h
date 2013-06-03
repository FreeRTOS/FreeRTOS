/*
 * @brief LPC18xx/43xx GPIO driver
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

#ifndef __GPIO_18XX_43XX_H_
#define __GPIO_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup GPIO_18XX_43XX CHIP: LPC18xx/43xx GPIO Driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

/**
 * @brief	Initialize GPIO block
 * @param	pGPIO	: The base of GPIO peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void Chip_GPIO_Init(LPC_GPIO_T *pGPIO)
{
	IP_GPIO_Init(pGPIO);
}

/**
 * @brief	Set a GPIO port/bit state
 * @param	pGPIO	: The base of GPIO peripheral on the chip
 * @param	port	: GPIO port to set
 * @param	bit		: GPIO bit to set
 * @param	setting	: true for high, false for low
 * @return	Nothing
 */
STATIC INLINE void Chip_GPIO_WritePortBit(LPC_GPIO_T *pGPIO, uint32_t port, uint8_t bit, bool setting)
{
	IP_GPIO_WritePortBit(pGPIO, port, bit, setting);
}

/**
 * @brief	Seta GPIO direction
 * @param	pGPIO	: The base of GPIO peripheral on the chip
 * @param	port	: GPIO port to set
 * @param	bit		: GPIO bit to set
 * @param	setting	: true for output, false for input
 * @return	Nothing
 */
STATIC INLINE void Chip_GPIO_WriteDirBit(LPC_GPIO_T *pGPIO, uint32_t port, uint8_t bit, bool setting)
{
	IP_GPIO_WriteDirBit(pGPIO, port, bit, setting);
}

/**
 * @brief	Read a GPIO state
 * @param	pGPIO	: The base of GPIO peripheral on the chip
 * @param	port	: GPIO port to read
 * @param	bit		: GPIO bit to read
 * @return	true of the GPIO is high, false if low
 */
STATIC INLINE bool Chip_GPIO_ReadPortBit(LPC_GPIO_T *pGPIO, uint32_t port, uint8_t bit)
{
	return IP_GPIO_ReadPortBit(pGPIO, port, bit);
}

/**
 * @brief	Read a GPIO direction (out or in)
 * @param	pGPIO	: The base of GPIO peripheral on the chip
 * @param	port	: GPIO port to read
 * @param	bit		: GPIO bit to read
 * @return	true of the GPIO is an output, false if input
 */
STATIC INLINE bool Chip_GPIO_ReadDirBit(LPC_GPIO_T *pGPIO, uint32_t port, uint8_t bit)
{
	return IP_GPIO_ReadDirBit(pGPIO, port, bit);
}

/**
 * @brief	Enable GPIO Interrupt
 * @param	pGPIOPinInt		: The base of GPIO pin interrupt peripheral on the chip
 * @param	portNum			: GPIO port number interrupt, should be: 0 to 7
 * @param	bitValue		: GPIO bit to enable (Not used)
 * @param	intMode			: Interrupt mode, should be:
 *							0: Rising edge interrupt mode
 *							1: Falling edge interrupt mode
 *							2: Active-High interrupt mode
 *							3: Active-Low interrupt mode
 * @return	None
 */
STATIC INLINE void Chip_GPIO_IntCmd(LPC_GPIOPININT_T* pGPIOPinInt, uint8_t portNum, uint8_t bitValue, IP_GPIOPININT_MODE_T intMode)
{
	IP_GPIOPININT_IntCmd(pGPIOPinInt, portNum, intMode);
}

/**
 * @brief	Get GPIO Interrupt Status
 * @param	pGPIOPinInt		: The base of GPIO pin interrupt peripheral on the chip
 * @param	portNum			: GPIO port number interrupt, should be: 0 to 7
 * @param	pinNum			: GPIO pin to check (Not used)
 * @param	intMode			: Interrupt mode (Not used)
 * @return	true if interrupt is pending, otherwise false
 */
STATIC INLINE bool Chip_GPIO_IntGetStatus(LPC_GPIOPININT_T* pGPIOPinInt, uint8_t portNum, uint8_t pinNum, uint8_t intMode)
{
	return IP_GPIOPININT_IntGetStatus(pGPIOPinInt, portNum);
}

/**
 * @brief	Clear GPIO Interrupt (Edge interrupt cases only)
 * @param	pGPIOPinInt		: The base of GPIO pin interrupt peripheral on the chip
 * @param	portNum			: GPIO port number interrupt, should be: 0 to 7
 * @param	bitValue		: GPIO bit to clear (Not used)
 * @return	None
 */
STATIC INLINE void Chip_GPIO_IntClear(LPC_GPIOPININT_T* pGPIOPinInt, uint8_t portNum, uint8_t bitValue)
{
	IP_GPIOPININT_IntClear(pGPIOPinInt, portNum);
}

/**
 * @brief	GPIO Group Interrupt Pin Initialization
 * @param	pGPIOGPINT	: Pointer to GPIOIR register block
 * @param	PortComb	: GPIO group combined enable, should be: 0 (OR functionality) and 1 (AND functionality)
 * @param	PortTrigger	: GPIO group interrupt trigger, should be: 0 (Edge-triggered) 1 (Level triggered)
 * @return	None
 */
STATIC INLINE void Chip_GPIOGP_IntInit(IP_GPIOGROUPINT_001_T *pGPIOGPINT, uint8_t PortComb, uint8_t PortTrigger)
{
	IP_GPIOGP_IntInit(pGPIOGPINT, PortComb, PortTrigger);
}

/**
 * @brief	GPIO Group Interrupt Pin Add to Group
 * @param	pGPIOGPINT	: Pointer to GPIOIR register block
 * @param	PortNum		: GPIO port number, should be 0 to 7
 * @param	PinNum		: GPIO pin number, should be 0 to 31
 * @param	ActiveMode	: GPIO active mode, should be 0 (active LOW) and 1 (active HIGH)
 * @return	None
 */
STATIC INLINE void Chip_GPIOGP_IntPinAdd(IP_GPIOGROUPINT_001_T *pGPIOGPINT,
										 uint8_t PortNum,
										 uint8_t PinNum,
										 bool ActiveMode)
{
	IP_GPIOGP_IntPinAdd(pGPIOGPINT, PortNum, PinNum, ActiveMode);
}

/**
 * @brief	GPIO Group Interrupt Pin Remove from Group
 * @param	pGPIOGPINT	: Pointer to GPIOIR register block
 * @param	PortNum		: GPIO port number, should be 0 to 7
 * @param	PinNum		: GPIO pin number, should be 0 to 31
 * @return	None
 */
STATIC INLINE void Chip_GPIOGP_IntPinRemove(IP_GPIOGROUPINT_001_T *pGPIOGPINT, uint8_t PortNum, uint8_t PinNum)
{
	IP_GPIOGP_IntPinRemove(pGPIOGPINT, PortNum, PinNum);
}

/**
 * @brief	Get GPIO Group Interrupt Get Status
 * @param	pGPIOGPINT	: Pointer to GPIOIR register block
 * @return	true if interrupt is pending, otherwise false
 */
STATIC INLINE bool Chip_GPIOGP_IntGetStatus(IP_GPIOGROUPINT_001_T *pGPIOGPINT)
{
	return IP_GPIOGP_IntGetStatus(pGPIOGPINT);
}

/**
 * @brief	Clear GPIO Group Interrupt
 * @param	pGPIOGPINT	: Pointer to GPIOIR register block
 * @return	None
 */
STATIC INLINE void Chip_GPIOGP_IntClear(IP_GPIOGROUPINT_001_T *pGPIOGPINT)
{
	IP_GPIOGP_IntClear(pGPIOGPINT);
}

/**
 * @brief	Set Direction for a GPIO port
 * @param	pGPIO		: The base of GPIO peripheral on the chip
 * @param	portNum		: Port Number
 * @param	bitValue	: GPIO bit to set
 * @param	out			: Direction value, 0 = input, !0 = output
 * @return	None
 * @note	Bits set to '0' are not altered.
 */
void Chip_GPIO_SetDir(LPC_GPIO_T *pGPIO, uint8_t portNum, uint32_t bitValue, uint8_t out);

/**
 * @brief	Set Direction for a GPIO port
 * @param	pGPIO		: The base of GPIO peripheral on the chip
 * @param	portNum		: Port Number
 * @param	bitValue	: GPIO bit to set
 * @param	out			: Direction value, 0 = input, !0 = output
 * @return	None
 * @note	Bits set to '0' are not altered.
 */
STATIC INLINE void Chip_FIO_SetDir(LPC_GPIO_T *pGPIO, uint8_t portNum, uint32_t bitValue, uint8_t out)
{
	/* Same with Chip_GPIO_SetDir() */
	Chip_GPIO_SetDir(pGPIO, portNum, bitValue, out);
}

/**
 * @brief	Set a GPIO port/bit to the high state
 * @param	pGPIO		: The base of GPIO peripheral on the chip
 * @param	portNum		: Port number
 * @param	bitValue	: Bit(s) in the port to set high
 * @return	None
 * @note	Any bit set as a '0' will not have it's state changed. This only
 * applies to ports configured as an output.
 */
STATIC INLINE void Chip_FIO_SetValue(LPC_GPIO_T *pGPIO, uint8_t portNum, uint32_t bitValue)
{
	/* Same with GPIO_SetValue() */
	pGPIO->SET[portNum] = bitValue;
}

/**
 * @brief	Set a GPIO port/bit to the low state
 * @param	pGPIO		: The base of GPIO peripheral on the chip
 * @param	portNum		: Port number
 * @param	bitValue	: Bit(s) in the port to set low
 * @return	None
 * @note	Any bit set as a '0' will not have it's state changed. This only
 * applies to ports configured as an output.
 */
STATIC INLINE void Chip_FIO_ClearValue(LPC_GPIO_T *pGPIO, uint8_t portNum, uint32_t bitValue)
{
	/* Same with GPIO_ClearValue() */
	pGPIO->CLR[portNum] = bitValue;
}

/**
 * @brief	Read current bit states for the selected port
 * @param	pGPIO	: The base of GPIO peripheral on the chip
 * @param	portNum	: Port number to read
 * @return	Current value of GPIO port
 * @note	The current states of the bits for the port are read, regardless of
 * whether the GPIO port bits are input or output.
 */
STATIC INLINE uint32_t Chip_FIO_ReadValue(LPC_GPIO_T *pGPIO, uint8_t portNum)
{
	/* Same with GPIO_ReadValue() */
	return pGPIO->PIN[portNum];
}

/**
 * @brief	Set a GPIO port/bit to the high state
 * @param	pGPIO		: The base of GPIO peripheral on the chip
 * @param	portNum		: Port number
 * @param	bitValue	: Bit(s) in the port to set high
 * @return	None
 * @note	Any bit set as a '0' will not have it's state changed. This only
 * applies to ports configured as an output.
 */
STATIC INLINE void Chip_GPIO_SetValue(LPC_GPIO_T *pGPIO, uint8_t portNum, uint32_t bitValue)
{
	pGPIO->SET[portNum] = bitValue;
}

/**
 * @brief	Set a GPIO port/bit to the low state
 * @param	pGPIO		: The base of GPIO peripheral on the chip
 * @param	portNum		: Port number
 * @param	bitValue	: Bit(s) in the port to set low
 * @return	None
 * @note	Any bit set as a '0' will not have it's state changed. This only
 * applies to ports configured as an output.
 */
STATIC INLINE void Chip_GPIO_ClearValue(LPC_GPIO_T *pGPIO, uint8_t portNum, uint32_t bitValue)
{
	pGPIO->CLR[portNum] = bitValue;
}

/**
 * @brief	Read current bit states for the selected port
 * @param	pGPIO	: The base of GPIO peripheral on the chip
 * @param	portNum	: Port number to read
 * @return	Current value of GPIO port
 * @note	The current states of the bits for the port are read, regardless of
 * whether the GPIO port bits are input or output.
 */
STATIC INLINE uint32_t Chip_GPIO_ReadValue(LPC_GPIO_T *pGPIO, uint8_t portNum)
{
	return pGPIO->PIN[portNum];
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __GPIO_18XX_43XX_H_ */
