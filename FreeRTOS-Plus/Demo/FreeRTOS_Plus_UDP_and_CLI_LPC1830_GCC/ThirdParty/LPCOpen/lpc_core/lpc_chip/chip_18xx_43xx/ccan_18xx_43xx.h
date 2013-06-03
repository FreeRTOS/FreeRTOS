/*
 * @brief LPC18xx/43xx CCAN driver
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

#ifndef __CCAN_18XX_43XX_H_
#define __CCAN_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

#define CCAN_SEG1_DEFAULT_VAL 5
#define CCAN_SEG2_DEFAULT_VAL 4
#define CCAN_SJW_DEFAULT_VAL 0

/** @defgroup CCAN_18XX_43XX CHIP: LPC18xx/43xx CCAN driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

/**
 * @brief	Enable/Disable CCAN Interrupts
 * @param	pCCAN			: The base of CCAN peripheral on the chip
 * @param	NewState		: New state, ENABLE or DISABLE
 * @return	Nothing
 */
STATIC INLINE void Chip_CCAN_IntEnable(LPC_CCAN_T *pCCAN, FunctionalState NewState)
{
	IP_CCAN_IntEnable(pCCAN, (IP_CCAN_INT_T) (CCAN_MODULE_INT | CCAN_STATUS_CHANGE_INT | CCAN_ERR_INT), NewState);
}

/**
 * @brief	Get the source ID of an interrupt
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @return	Interrupt source ID
 */
STATIC INLINE uint32_t Chip_CCAN_GetIntID(LPC_CCAN_T *pCCAN)
{
	return IP_CCAN_Get_IntID(pCCAN);
}

/**
 * @brief	Get the CCAN status register
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @return	CCAN status register
 */
STATIC INLINE uint32_t Chip_CCAN_GetStatus(LPC_CCAN_T *pCCAN)
{
	return IP_CCAN_GetStatus(pCCAN);
}

/**
 * @brief	Get a message object in message RAM into the message buffer
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	msg_num		: The number of message object in message RAM to be get
 * @param	msg_buf		: Pointer of the message buffer
 * @return	Nothing
 */
STATIC INLINE void Chip_CCAN_GetMsgObject(LPC_CCAN_T *pCCAN, uint8_t msg_num, message_object *msg_buf)
{
	IP_CCAN_GetMsgObject(LPC_C_CAN0, IF2, msg_num, msg_buf);
}

/**
 * @brief	Initialize the CCAN peripheral, free all message object in RAM
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @return	Nothing
 */
void Chip_CCAN_Init(LPC_CCAN_T *pCCAN);

/**
 * @brief	De-initialize the CCAN peripheral
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @return	Nothing
 */
void Chip_CCAN_DeInit(LPC_CCAN_T *pCCAN);

/**
 * @brief	Select bit rate for CCAN bus
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	bitRate	: Bit rate to be set
 * @return	Nothing
 */
void Chip_CCAN_SetBitRate(LPC_CCAN_T *pCCAN, uint32_t bitRate);

/**
 * @brief	Clear the status of CCAN bus
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @param	status	: Status to be cleared
 * @return	Nothing
 */
void Chip_CCAN_ClearStatus(LPC_CCAN_T *pCCAN, IP_CCAN_STATUS_T status);

/**
 * @brief	Clear the pending interrupt
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @param	msg_num	: Message number
 * @param	TRxMode	: Select transmit or receive interrupt to be cleared
 * @return	Nothing
 */
void Chip_CCAN_ClearIntPend(LPC_CCAN_T *pCCAN, uint8_t msg_num, uint8_t TRxMode);

/**
 * @brief	Send a message
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	RemoteEnable: Enable/Disable passives transmit by using remote frame
 * @param	msg_ptr		: Message to be transmitted
 * @return	Nothing
 */
void Chip_CCAN_Send (LPC_CCAN_T *pCCAN, uint32_t RemoteEnable, message_object *msg_ptr);

/**
 * @brief	Register a message ID for receiving
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	rev_id		: Received message ID
 * @return	Nothing
 */
void Chip_CCAN_AddReceiveID(LPC_CCAN_T *pCCAN, uint32_t rev_id);

/**
 * @brief	Remove a registered message ID from receiving
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	rev_id		: Received message ID to be removed
 * @return	Nothing
 */
void Chip_CCAN_DeleteReceiveID(LPC_CCAN_T *pCCAN, uint32_t rev_id);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __CCAN_18XX_43XX_H_ */
