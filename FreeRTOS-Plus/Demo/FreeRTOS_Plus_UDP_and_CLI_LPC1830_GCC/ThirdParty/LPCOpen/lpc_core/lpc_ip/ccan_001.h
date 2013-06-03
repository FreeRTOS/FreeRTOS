/*
 * @brief CCAN registers and control functions
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

#ifndef __CCAN_001_H_
#define __CCAN_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_CCAN_001 IP: CCAN register block and driver
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief CCAN message interface register block structure
 */
typedef struct {	/*!< C_CAN message interface Structure       */
	__IO uint32_t IF_CMDREQ;			/*!< Message interface command request  */
	union {
		__IO uint32_t IF_CMDMSK_R;		/*!< Message interface command mask (read direction) */
		__IO uint32_t IF_CMDMSK_W;		/*!< Message interface command mask (write direction) */
	};

	__IO uint32_t IF_MSK1;				/*!< Message interface mask 1 */
	__IO uint32_t IF_MSK2;				/*!< Message interface mask 2 */
	__IO uint32_t IF_ARB1;				/*!< Message interface arbitration 1 */
	__IO uint32_t IF_ARB2;				/*!< Message interface arbitration 2 */
	__IO uint32_t IF_MCTRL;			/*!< Message interface message control */
	__IO uint32_t IF_DA1;				/*!< Message interface data A1 */
	__IO uint32_t IF_DA2;				/*!< Message interface data A2 */
	__IO uint32_t IF_DB1;				/*!< Message interface data B1 */
	__IO uint32_t IF_DB2;				/*!< Message interface data B2 */
	__I  uint32_t  RESERVED[13];
} IP_CCAN_001_IF_T;

/**
 * @brief CCAN Controller Area Network register block structure
 */
typedef struct {						/*!< C_CAN Structure       */
	__IO uint32_t CNTL;					/*!< CAN control            */
	__IO uint32_t STAT;					/*!< Status register        */
	__I  uint32_t EC;					/*!< Error counter          */
	__IO uint32_t BT;					/*!< Bit timing register    */
	__I  uint32_t INT;					/*!< Interrupt register     */
	__IO uint32_t TEST;					/*!< Test register          */
	__IO uint32_t BRPE;					/*!< Baud rate prescaler extension register */
	__I  uint32_t  RESERVED0;
	IP_CCAN_001_IF_T IF[2];
	__I  uint32_t  RESERVED2[8];
	__I  uint32_t TXREQ1;				/*!< Transmission request 1 */
	__I  uint32_t TXREQ2;				/*!< Transmission request 2 */
	__I  uint32_t  RESERVED3[6];
	__I  uint32_t ND1;					/*!< New data 1             */
	__I  uint32_t ND2;					/*!< New data 2             */
	__I  uint32_t  RESERVED4[6];
	__I  uint32_t IR1;					/*!< Interrupt pending 1    */
	__I  uint32_t IR2;					/*!< Interrupt pending 2    */
	__I  uint32_t  RESERVED5[6];
	__I  uint32_t MSGV1;				/*!< Message valid 1        */
	__I  uint32_t MSGV2;				/*!< Message valid 2        */
	__I  uint32_t  RESERVED6[6];
	__IO uint32_t CLKDIV;				/*!< CAN clock divider register */
} IP_CCAN_001_T;

typedef enum IP_CCAN_TEST_MODE {
	CCAN_BASIC_TEST_MODE = 1 << 2,
	CCAN_SILENT_TEST_MODE = 1 << 3,
	CCAN_LOOPBACK_TEST_MODE = 1 << 4
} IP_CCAN_TEST_MODE_T;

typedef enum IP_CCAN_INT {
	CCAN_MODULE_INT = 1 << 1,
	CCAN_STATUS_CHANGE_INT = 1 << 2,
	CCAN_ERR_INT = 1 << 3
} IP_CCAN_INT_T;

/**
 * @brief CAN message object structure
 */
typedef struct {
	uint32_t    id;		/**< ID of message, if bit 30 is set then this is extended frame */
	uint32_t    dlc;	/**< Message data length */
	uint8_t data[8];	/**< Message data */
} message_object;
typedef enum IP_CCAN_MSG_INTERFACE {
	IF1 = 0x00,
	IF2 = 1,
} IP_CCAN_MSG_INTERFACE_T;
typedef enum IP_CCAN_STATUS {
	CCAN_STAT_LEC       = (0x7 << 0),
	CCAN_STAT_TXOK      = (1 << 3),
	CCAN_STAT_RXOK      = (1 << 4),
	CCAN_STAT_EPASS = (1 << 5),
	CCAN_STAT_EWARN = (1 << 6),
	CCAN_STAT_BOFF      = (1 << 7)
} IP_CCAN_STATUS_T;

/**
 * @brief I2S transmit/receive mode for configuration
 */
typedef enum IP_CCAN_TRX_MODE {
	CCAN_TX_MODE,
	CCAN_RX_MODE,
} IP_CCAN_TRX_MODE_T;
/* Private Macros ---------------------------------------------------------- */
#ifndef __GNUC__
/* Macro for reading and writing to CCAN IF registers */
#define CCAN_IF_Read(LPCx, reg, IFsel) (( ## LPCx ## ->IF ## [IFsel] ## . ## IF ## _ ## reg))
#define CCAN_IF_Write(LPCx, reg, IFsel, val) (( ## LPCx ## ->IF ## [IFsel] ## . ## IF ## _ ## reg) = (val))
#else
#define CCAN_IF_Read(LPCx, reg, IFsel) (LPCx->IF[IFsel].IF ## _ ## reg)
#define CCAN_IF_Write(LPCx, reg, IFsel, val) (LPCx->IF[IFsel].IF ## _ ## reg = val)
#endif

#define CCAN_STATUS_INT 0x8000

#define CCAN_TX_DIR 1UL
#define CCAN_RX_DIR 0UL

/* bit field of IF command mask register */
#define CCAN_DATAB      (1 << 0)	/* 1 is transfer data byte 4-7 to message object, 0 is not */
#define CCAN_DATAA      (1 << 1)	/* 1 is transfer data byte 0-3 to message object, 0 is not */
#define CCAN_NEWDAT     (1 << 2)	/* Clear NEWDAT bit in the message object */
#define CCAN_CLRINTPND  (1 << 3)
#define CCAN_CTRL       (1 << 4)	/* 1 is transfer the CTRL bit to the message object, 0 is not */
#define CCAN_ARB        (1 << 5)	/* 1 is transfer the ARB bits to the message object, 0 is not */
#define CCAN_MASK       (1 << 6)	/* 1 is transfer the MASK bit to the message object, 0 is not */
#define CCAN_RW(n)      (((n) & 1UL) << 7)	/* 0 is READ, 1 is WRITE */
#define CCAN_WR 1UL
#define CCAN_RD 0UL

/* bit field of IF mask 2 register */
#define CCAN_MASK_MXTD  (1 << 15)		/* 1 extended identifier bit is used in the RX filter unit, 0 is not */
#define CCAN_MASK_MDIR(n)   (((n) & 0x01) <<  14)		/* 1 direction bit is used in the RX filter unit, 0 is not */

/* bit field of IF identifier 2 register */
#define CCAN_ID_MVAL    (1 << 15)		/* Message valid bit, 1 is valid in the MO handler, 0 is ignored */
#define CCAN_ID_MTD     (1 << 14)		/* 1 extended identifier bit is used in the RX filter unit, 0 is not */
#define CCAN_ID_DIR(n)  (((n) & 0x01) << 13)	/* 1 direction bit is used in the RX filter unit, 0 is not */

/* bit field of IF message control register */
#define CCAN_NEWD       (1 << 15)		/* 1 indicates new data is in the message buffer.  */
#define CCAN_MLST       (1 << 14)		/* 1 indicates a message loss. */
#define CCAN_INTP       (1 << 13)		/* 1 indicates message object is an interrupt source */
#define CCAN_UMSK       (1 << 12)		/* 1 is to use the mask for the receive filter mask. */
#define CCAN_TXIE       (1 << 11)		/* 1 is TX interrupt enabled */
#define CCAN_RXIE       (1 << 10)		/* 1 is RX interrupt enabled */

#define CCAN_RMTEN(n)       (((n) & 1UL) << 9)	/* 1 is remote frame enabled */

#define CCAN_TXRQ       (1 << 8)		/* 1 is TxRqst enabled */
#define CCAN_EOB        (1 << 7)		/* End of buffer, always write to 1 */
#define CCAN_DLC        0x000F			/* bit mask for DLC */

#define CCAN_ID_STD_MASK    0x07FF
#define CCAN_ID_EXT_MASK    0x1FFFFFFF
#define CCAN_DLC_MASK       0x0F

/* bit field of IF command request n register */
#define CCAN_IFCREQ_BUSY               0x8000	/* 1 is writing is progress, cleared when
												   RD/WR done */
/* CAN CTRL register */
#define CCAN_CTRL_INIT      (1 << 0)
#define CCAN_CTRL_IE            (1 << 1)
#define CCAN_CTRL_SIE       (1 << 2)
#define CCAN_CTRL_EIE       (1 << 3)
#define CCAN_CTRL_DAR       (1 << 5)
#define CCAN_CTRL_CCE       (1 << 6)
#define CCAN_CTRL_TEST      (1 << 7)

/**
 * @brief	Configure the bit timing for CCAN bus
 * @param	pCCAN				: The base of CCAN peripheral on the chip
 * @param	ClkDiv				: Set the clock divider
 * @param	BaudRatePrescaler	: Set the baud rate Prescaler
 * @param	SynJumpWidth		: Set the synchronization jump width
 * @param	Tseg1				: Set the Phase buffer segment 1
 * @param	Tseg2				: Set the Phase buffer segment 2
 * @return	Nothing
 */
void IP_CCAN_TimingCfg (IP_CCAN_001_T *pCCAN,
						uint32_t ClkDiv,
						uint32_t BaudRatePrescaler,
						uint8_t SynJumpWidth,
						uint8_t Tseg1,
						uint8_t Tseg2);

/**
 * @brief	Initialize the CAN controller
 * @param	pCCAN			: The base of CCAN peripheral on the chip
 * @param	NewState		: New state, ENABLE for starting initialization, DISABLE for normal operation
 * @return	Nothing
 */
void IP_CCAN_SWInit (IP_CCAN_001_T *pCCAN, FunctionalState NewState);

/**
 * @brief	Enable/Disable CCAN Interrupts
 * @param	pCCAN			: The base of CCAN peripheral on the chip
 * @param	Int_type		: Type of interrupt
 * @param	NewState		: New state, ENABLE or DISABLE
 * @return	Nothing
 */
void IP_CCAN_IntEnable (IP_CCAN_001_T *pCCAN, IP_CCAN_INT_T Int_type, FunctionalState NewState);

/**
 * @brief	Enable/Disable automatic retransmission
 * @param	pCCAN			: The base of CCAN peripheral on the chip
 * @param	NewState		: New state, ENABLE or DISABLE
 * @return	Nothing
 */
void IP_CCAN_AutoRetransmitEnable (IP_CCAN_001_T *pCCAN, FunctionalState NewState);

/**
 * @brief	Get the current value of the transmit/receive error counter
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @param	TRMode	: Transmit/Receive mode, should be CCAN_TX_MODE or CCAN_RX_MODE
 * @return	Current value of the transmit/receive error counter
 */
uint8_t IP_CCAN_GetErrCounter (IP_CCAN_001_T *pCCAN, IP_CCAN_TRX_MODE_T TRMode);

/**
 * @brief	Get the CCAN status register
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @return	CCAN status register
 */
uint32_t IP_CCAN_GetStatus (IP_CCAN_001_T *pCCAN);

/**
 * @brief	Set the CCAN status
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @param	val		: Value to be set for status register
 * @return	Nothing
 */
void IP_CCAN_SetStatus (IP_CCAN_001_T *pCCAN, uint32_t val);

/**
 * @brief	Get the source ID of an interrupt
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @return	Interrupt source ID
 */
uint32_t IP_CCAN_Get_IntID (IP_CCAN_001_T *pCCAN);

/**
 * @brief	Enable/Disable test mode in CCAN
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	test_mode	: Selected mode, the different test functions may be combined
 * @param	NewState	: New state, ENABLE or DISABLE
 * @return	Nothing
 */
void IP_CCAN_TestModeEnable(IP_CCAN_001_T *pCCAN, IP_CCAN_TEST_MODE_T test_mode, FunctionalState NewState);

/**
 * @brief	Clear interrupt pending bit in the message object
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @param	IFsel	: The Message interface to be used
 * @param	msg_num	: Message number
 * @return	Nothing
 */
void IP_CCAN_ClearIntPend (IP_CCAN_001_T *pCCAN, IP_CCAN_MSG_INTERFACE_T IFsel, uint8_t msg_num);

/**
 * @brief	Clear new data flag bit in the message object
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @param	IFsel	: The Message interface to be used
 * @param	msg_num	: Message number
 * @return	Nothing
 */
void IP_CCAN_Clear_NewDataFlag (IP_CCAN_001_T *pCCAN, IP_CCAN_MSG_INTERFACE_T IFsel, uint8_t msg_num);

/**
 * @brief	Enable/Disable the message object to valid
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @param	IFsel	: The Message interface to be used
 * @param	msg_num	: Message number
 * @param	NewState: New state, ENABLE or DISABLE
 * @return	Nothing
 */
void IP_CCAN_SetValidMsg(IP_CCAN_001_T *pCCAN, IP_CCAN_MSG_INTERFACE_T IFsel, uint8_t msg_num, FunctionalState NewState);

/**
 * @brief	Check the message objects is valid or not
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @return	A 32 bits value, each bit corresponds to a message objects form 0 to 31 (1 is valid, 0 is invalid)
 */
uint32_t IP_CCAN_GetValidMsg(IP_CCAN_001_T *pCCAN);

/**
 * @brief	Get the transmit repuest bit in all message objects
 * @param	pCCAN	: The base of CCAN peripheral on the chip
 * @return	A 32 bits value, each bit corresponds to transmit request bit in message objects
 */
uint32_t IP_CCAN_GetTxRQST(IP_CCAN_001_T *pCCAN);

/**
 * @brief	Set a message into the message object in message RAM
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	IFsel		: The Message interface to be used
 * @param	direction	: Select the message object is used for transmiting or receiving, should be CCAN_TX_DIR or CCAN_RX_DIR
 * @param	RemoteEnable: Enable/Disable passives transmit by using remote frame
 * @param	msg_num		: Message number
 * @param	msg_ptr		: Pointer of message to be set
 * @return	Nothing
 */
void IP_CCAN_SetMsgObject (IP_CCAN_001_T *pCCAN,
						   IP_CCAN_MSG_INTERFACE_T IFsel,
						   uint8_t direction,
						   uint32_t RemoteEnable,
						   uint8_t msg_num,
						   const message_object *msg_ptr);

/**
 * @brief	Get a message object in message RAM into the message buffer
 * @param	pCCAN		: The base of CCAN peripheral on the chip
 * @param	IFsel		: The Message interface to be used
 * @param	msg_num		: The number of message object in message RAM to be get
 * @param	msg_buf		: Pointer of the message buffer
 * @return	Nothing
 */
void IP_CCAN_GetMsgObject (IP_CCAN_001_T *pCCAN,
						   IP_CCAN_MSG_INTERFACE_T IFsel,
						   uint8_t msg_num,
						   message_object *msg_buf);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __CCAN_001_H_ */
