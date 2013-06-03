/*
 * @brief LPC18xx/43xx ethernet driver
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

#ifndef __ENET_18XX_43XX_H_
#define __ENET_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup ENET_18XX_43XX CHIP: LPC18xx/43xx Ethernet driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

/** @defgroup ENET_18XX_43XX_OPTIONS CHIP: LPC18xx/43xx Ethernet driver build options
 * @ingroup ENET_18XX_43XX CHIP_18XX_43XX_DRIVER_OPTIONS
 * The ethernet driver has options that configure it's operation at build-time.<br>
 *
 * <b>USE_RMII</b><br>
 * When defined, the driver will be built for RMII operation.<br>
 * When not defined, the driver will be built for MII operation.<br>
 * @{
 */

/**
 * @}
 */

/**
 * @brief	Resets the ethernet interface
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 * @note	Resets the ethernet interface. This should be called prior to
 * Chip_ENET_Init with a small delay after this call.
 */
STATIC INLINE void Chip_ENET_Reset(LPC_ENET_T *pENET)
{
	IP_ENET_Reset(pENET);
}

/**
 * @brief	Sets the address of the interface
 * @param	pENET	: The base of ENET peripheral on the chip
 * @param	macAddr	: Pointer to the 6 bytes used for the MAC address
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_SetADDR(LPC_ENET_T *pENET, const uint8_t *macAddr)
{
	IP_ENET_SetADDR(pENET, macAddr);
}

/**
 * @brief	Sets up the PHY link clock divider and PHY address
 * @param	pENET	: The base of ENET peripheral on the chip
 * @param	div		: Divider index, not a divider value, see user manual
 * @param	addr	: PHY address, used with MII read and write
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_SetupMII(LPC_ENET_T *pENET, uint32_t div, uint8_t addr)
{
	IP_ENET_SetupMII(pENET, div, addr);
}

/**
 * @brief	Starts a PHY write via the MII
 * @param	pENET	: The base of ENET peripheral on the chip
 * @param	reg		: PHY register to write
 * @param	data	: Data to write to PHY register
 * @return	Nothing
 * @note	Start a PHY write operation. Does not block, requires calling
 * IP_ENET_IsMIIBusy to determine when write is complete.
 */
STATIC INLINE void Chip_ENET_StartMIIWrite(LPC_ENET_T *pENET, uint8_t reg, uint16_t data)
{
	IP_ENET_StartMIIWrite(pENET, reg, data);
}

/**
 * @brief	Starts a PHY read via the MII
 * @param	pENET	: The base of ENET peripheral on the chip
 * @param	reg		: PHY register to read
 * @return	Nothing
 * @note	Start a PHY read operation. Does not block, requires calling
 * IP_ENET_IsMIIBusy to determine when read is complete and calling
 * IP_ENET_ReadMIIData to get the data.
 */
STATIC INLINE void Chip_ENET_StartMIIRead(LPC_ENET_T *pENET, uint8_t reg)
{
	IP_ENET_StartMIIRead(pENET, reg);
}

/**
 * @brief	Returns MII link (PHY) busy status
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Returns true if busy, otherwise false
 */
STATIC INLINE bool Chip_ENET_IsMIIBusy(LPC_ENET_T *pENET)
{
	return IP_ENET_IsMIIBusy(pENET);
}

/**
 * @brief	Returns the value read from the PHY
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Read value from PHY
 */
STATIC INLINE uint16_t Chip_ENET_ReadMIIData(LPC_ENET_T *pENET)
{
	return IP_ENET_ReadMIIData(pENET);
}

/**
 * @brief	Enables ethernet transmit
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_TXEnable(LPC_ENET_T *pENET)
{
	IP_ENET_TXEnable(pENET);
}

/**
 * @brief Disables ethernet transmit
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_TXDisable(LPC_ENET_T *pENET)
{
	IP_ENET_TXDisable(pENET);
}

/**
 * @brief	Enables ethernet packet reception
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_RXEnable(LPC_ENET_T *pENET)
{
	IP_ENET_RXEnable(pENET);
}

/**
 * @brief	Disables ethernet packet reception
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_RXDisable(LPC_ENET_T *pENET)
{
	IP_ENET_RXDisable(pENET);
}

/**
 * @brief	Sets full or half duplex for the interface
 * @param	pENET	: The base of ENET peripheral on the chip
 * @param	full	: true to selected full duplex, false for half
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_SetDuplex(LPC_ENET_T *pENET, bool full)
{
	IP_ENET_SetDuplex(pENET, full);
}

/**
 * @brief	Sets speed for the interface
 * @param	pENET		: The base of ENET peripheral on the chip
 * @param	speed100	: true to select 100Mbps mode, false for 10Mbps
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_SetSpeed(LPC_ENET_T *pENET, bool speed100)
{
	IP_ENET_SetSpeed(pENET, speed100);
}

/**
 * @brief	Configures the initial ethernet descriptors
 * @param	pENET		: The base of ENET peripheral on the chip
 * @param	pTXDescs	: Pointer to TX descriptor list
 * @param	pRXDescs	: Pointer to RX descriptor list
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_InitDescriptors(LPC_ENET_T *pENET,
											 IP_ENET_001_ENHTXDESC_T *pTXDescs, IP_ENET_001_ENHRXDESC_T *pRXDescs)
{
	IP_ENET_InitDescriptors(pENET, pTXDescs, pRXDescs);
}

/**
 * @brief	Starts receive polling of RX descriptors
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_RXStart(LPC_ENET_T *pENET)
{
	IP_ENET_RXStart(pENET);
}

/**
 * @brief	Starts transmit polling of TX descriptors
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void Chip_ENET_TXStart(LPC_ENET_T *pENET)
{
	IP_ENET_TXStart(pENET);
}

/**
 * @brief	Initialize ethernet interface
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 * @note	Performs basic initialization of the ethernet interface in a default
 * state. This is enough to place the interface in a usable state, but
 * may require more setup outside this function.
 */
void Chip_ENET_Init(LPC_ENET_T *pENET);

/**
 * @brief	De-initialize the ethernet interface
 * @param	pENET	: The base of ENET peripheral on the chip
 * @return	Nothing
 */
void Chip_ENET_DeInit(LPC_ENET_T *pENET);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __ENET_18XX_43XX_H_ */
