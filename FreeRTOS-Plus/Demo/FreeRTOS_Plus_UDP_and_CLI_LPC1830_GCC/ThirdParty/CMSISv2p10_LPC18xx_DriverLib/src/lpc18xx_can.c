/**********************************************************************
* $Id$		lpc18xx_can.c		2011-06-02
*//**
* @file		lpc18xx_can.c
* @brief	Contains all functions support for C CAN firmware library
* 			on LPC18xx
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

/* Peripheral group ----------------------------------------------------------- */
/** @addtogroup C_CAN
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc18xx_can.h"
#include "lpc18xx_cgu.h"

/* If this source file built with example, the LPC18xx FW library configuration
 * file in each example directory ("lpc18xx_libcfg.h") must be included,
 * otherwise the default FW library configuration file must be included instead
 */
#ifdef __BUILD_WITH_EXAMPLE__
#include "lpc18xx_libcfg.h"
#else
#include "lpc18xx_libcfg_default.h"
#endif /* __BUILD_WITH_EXAMPLE__ */

#ifdef _C_CAN

/* Private Macros ---------------------------------------------------------- */
#ifndef __GNUC__
/* Macro for reading and writing to CCAN IF registers */
#define CAN_IF_Read(reg, IFsel) (LPC_C_CAN0->##IFsel##_##reg)
#define CAN_IF_Write(reg, IFsel, val) (LPC_C_CAN0->##IFsel##_##reg=val)

/* Macro for writing IF to specific RAM message object */
#define CAN_IF_readBuf(IFsel,msg) \
  LPC_C_CAN0->##IFsel##_##CMDMSK_W=RD|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB; \
  LPC_C_CAN0->##IFsel##_##CMDREQ=msg; \
  while (LPC_C_CAN0->##IFsel##_##CMDREQ & IFCREQ_BUSY );

/* Macro for reading specific RAM message object to IF */
#define CAN_IF_writeBuf(IFsel,msg) \
  LPC_C_CAN0->##IFsel##_##CMDMSK_W=WR|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB; \
  LPC_C_CAN0->##IFsel##_##CMDREQ=msg; \
  while (LPC_C_CAN0->##IFsel##_##CMDREQ & IFCREQ_BUSY );
#else
#define CAN_IF_Read(reg, IFsel) (LPC_C_CAN0->IFsel##_##reg)
#define CAN_IF_Write(reg, IFsel, val) (LPC_C_CAN0->IFsel ## _ ## reg = val)

/* Macro for writing IF to specific RAM message object */
#define CAN_IF_readBuf(IFsel,msg) \
  LPC_C_CAN0->IFsel##_##CMDMSK_W=RD|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB; \
  LPC_C_CAN0->IFsel##_##CMDREQ=msg; \
  while (LPC_C_CAN0->IFsel##_##CMDREQ & IFCREQ_BUSY );

/* Macro for reading specific RAM message object to IF */
#define CAN_IF_writeBuf(IFsel,msg) \
  LPC_C_CAN0->IFsel##_##CMDMSK_W=WR|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB; \
  LPC_C_CAN0->IFsel##_##CMDREQ=msg; \
  while (LPC_C_CAN0->IFsel##_##CMDREQ & IFCREQ_BUSY );
#endif

#define IF1	0
#define IF2	1

#define CAN_STATUS_INTERRUPT      0x8000    /* 0x0001-0x0020 are the # of the message
										    object */
                                            /* 0x8000 is the status interrupt */

/* CAN Message interface register definitions */
/* bit field of IF command request n register */
#define IFCREQ_BUSY               0x8000    /* 1 is writing is progress, cleared when
                                            RD/WR done */
/* CAN CTRL register */
#define CTRL_INIT		(1 << 0)
#define CTRL_IE			(1 << 1)
#define CTRL_SIE		(1 << 2)
#define CTRL_EIE		(1 << 3)
#define CTRL_DAR		(1 << 5)
#define CTRL_CCE		(1 << 6)
#define CTRL_TEST		(1 << 7)

/* CAN Test register */
#define TEST_BASIC		(1 << 2)
#define TEST_SILENT		(1 << 3)
#define TEST_LBACK		(1 << 4)

/* CAN Status register */
#define STAT_LEC		(0x7 << 0)
#define STAT_TXOK		(1 << 3)
#define STAT_RXOK		(1 << 4)
#define STAT_EPASS		(1 << 5)
#define STAT_EWARN		(1 << 6)
#define STAT_BOFF		(1 << 7)

#define NO_ERR		0 	// No Error
#define STUFF_ERR	1	// Stuff Error : More than 5 equal bits in a sequence have occurred in a part
						// of a received message where this is not allowed.
#define FORM_ERR	2	// Form Error : A fixed format part of a received frame has the wrong format.
#define ACK_ERR		3 	// AckError : The message this CAN Core transmitted was not acknowledged
						// by another node.
#define BIT1_ERR	4 	// Bit1Error : During the transmission of a message (with the exception of
						// the arbitration field), the device wanted to send a recessive level (bit of
						// logical value �1�), but the monitored bus value was dominant.
#define BIT0_ERR	5 	// Bit0Error : During the transmission of a message (or acknowledge bit,
						// or active error flag, or overload flag), the device wanted to send a
						// LOW/dominant level (data or identifier bit logical value �0�), but the
						// monitored Bus value was HIGH/recessive. During busoff recovery this
						// status is set each time a
						// sequence of 11 HIGH/recessive bits has been monitored. This enables
						// the CPU to monitor the proceeding of the busoff recovery sequence
						// (indicating the bus is not stuck at LOW/dominant or continuously
						// disturbed).
#define CRC_ERR		6 	// CRCError: The CRC checksum was incorrect in the message received.


/* bit field of IF command mask register */
#define	DATAB		(1 << 0)   /* 1 is transfer data byte 4-7 to message object, 0 is not */
#define	DATAA		(1 << 1)   /* 1 is transfer data byte 0-3 to message object, 0 is not */
#define	NEWDAT		(1 << 2)   /* Clear NEWDAT bit in the message object */
#define	CLRINTPND	(1 << 3)
#define	CTRL		(1 << 4)   /* 1 is transfer the CTRL bit to the message object, 0 is not */
#define	ARB			(1 << 5)   /* 1 is transfer the ARB bits to the message object, 0 is not */
#define	MASK		(1 << 6)   /* 1 is transfer the MASK bit to the message object, 0 is not */
#define	WR			(1 << 7)   /* 0 is READ, 1 is WRITE */
#define RD      	0x0000

/* bit field of IF mask 2 register */
#define	MASK_MXTD	(1 << 15)     /* 1 extended identifier bit is used in the RX filter unit, 0 is not */
#define	MASK_MDIR	(1 << 14)     /* 1 direction bit is used in the RX filter unit, 0 is not */

/* bit field of IF identifier 2 register */
#define	ID_MVAL		(1 << 15)     /* Message valid bit, 1 is valid in the MO handler, 0 is ignored */
#define	ID_MTD		(1 << 14)     /* 1 extended identifier bit is used in the RX filter unit, 0 is not */
#define	ID_DIR		(1 << 13)     /* 1 direction bit is used in the RX filter unit, 0 is not */

/* bit field of IF message control register */
#define	NEWD		(1 << 15)     /* 1 indicates new data is in the message buffer.  */
#define	MLST		(1 << 14)     /* 1 indicates a message loss. */
#define	INTP		(1 << 13)     /* 1 indicates message object is an interrupt source */
#define UMSK    	(1 << 12)     /* 1 is to use the mask for the receive filter mask. */
#define	TXIE		(1 << 11)     /* 1 is TX interrupt enabled */
#define	RXIE		(1 << 10)     /* 1 is RX interrupt enabled */

#if REMOTE_ENABLE
	#define	RMTEN		(1 << 9)  /* 1 is remote frame enabled */
#else
	#define	RMTEN		0
#endif

#define TXRQ    	(1 << 8)      /* 1 is TxRqst enabled */
#define	EOB			(1 << 7)      /* End of buffer, always write to 1 */
#define	DLC			0x000F        /* bit mask for DLC */

#define ID_STD_MASK		0x07FF
#define ID_EXT_MASK		0x1FFFFFFF
#define DLC_MASK		0x0F

/* Private Variables ---------------------------------------------------------- */
/* Statistics of all the interrupts */
/* Buss off status counter */
volatile uint32_t BOffCnt = 0;
/* Warning status counter. 	At least one of the error counters
 in the EML has reached the error warning limit of 96 */
volatile uint32_t EWarnCnt = 0;
/* More than 5 equal bits in a sequence in received message */
volatile uint32_t StuffErrCnt = 0;
/* Wrong format of fixed format part of a received frame */
volatile uint32_t FormErrCnt = 0;
/* Transmitted message not acknowledged. */
volatile uint32_t AckErrCnt = 0;
/* Send a HIGH/recessive level, but monitored LOW/dominant */
volatile uint32_t Bit1ErrCnt = 0;
/* Send a LOW/dominant level, but monitored HIGH/recessive */
volatile uint32_t Bit0ErrCnt = 0;
/* The CRC checksum was incorrect in the message received */
volatile uint32_t CRCErrCnt = 0;
/* Message object new data error counter */
volatile uint32_t ND1ErrCnt = 0;

MSG_CB TX_cb, RX_cb;

message_object can_buff[CAN_MSG_OBJ_MAX];
message_object recv_buff;

#if CAN_DEBUG
uint32_t CANStatusLog[100];
uint32_t CANStatusLogCount = 0;
#endif

//#ifdef __GNUC__
//uint32_t CAN_IF_Read(uint32_t reg,uint32_t IFsel){
//	if(IFsel == IF1){
//		return (LPC_C_CAN0->IF1_reg);
//	}else{
//		return (LPC_C_CAN0->IF2_reg);
//	}
//}
//void CAN_IF_Write(uint32_t reg, uint32_t IFsel,uint32_t val){
//	if(IFsel == IF1){
//	(LPC_C_CAN0->IF1_reg=val);
//	}else{
//		(LPC_C_CAN0->IF2_reg=val);
//	}
//}
//
///* Macro for writing IF to specific RAM message object */
//void CAN_IF_readBuf(uint32_t IFsel,uint32_t msg){
//	if(IFsel == IF1){
//	LPC_C_CAN0->IF1_CMDMSK_W=RD|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB;
//	LPC_C_CAN0->IF1_CMDREQ=msg;
//	while (LPC_C_CAN0->IF1_CMDREQ & IFCREQ_BUSY );
//	}else{
//	  LPC_C_CAN0->IF2_CMDMSK_W=RD|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB;
//	  LPC_C_CAN0->IF2_CMDREQ=msg;
//	  while (LPC_C_CAN0->IF2_CMDREQ & IFCREQ_BUSY );
//  }
//
//}
//
///* Macro for reading specific RAM message object to IF */
//void CAN_IF_writeBuf(uint32_t IFsel,uint32_t msg){
//	if(IFsel == IF1){
//  LPC_C_CAN0->IF1_CMDMSK_W=WR|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB;
//  LPC_C_CAN0->IF1_CMDREQ=msg;
//  while (LPC_C_CAN0->IF1_CMDREQ & IFCREQ_BUSY );
//	}else{
//		  LPC_C_CAN0->IF2_CMDMSK_W=WR|MASK|ARB|CTRL|CLRINTPND|DATAA|DATAB;
//		  LPC_C_CAN0->IF2_CMDREQ=msg;
//		  while (LPC_C_CAN0->IF2_CMDREQ & IFCREQ_BUSY );
//	}
//}
//#endif

/*********************************************************************//**
 * @brief		Handle valid received message
 * @param[in]	msg_no Message Object number
 * @return 		None
 **********************************************************************/
void CAN_RxInt_MessageProcess( uint8_t msg_no )
{
	uint32_t msg_id;
	uint32_t *p_add;
	uint32_t reg1, reg2;

	/* Import message object to IF2 */
 	CAN_IF_readBuf(IF2, msg_no);					/* Read the message into the IF registers */

	p_add = (uint32_t *)&recv_buff;

	if( CAN_IF_Read(ARB2, IF2) & ID_MTD )			/* bit 28-0 is 29 bit extended frame */
	{
		/* mask off MsgVal and Dir */
		reg1 = CAN_IF_Read(ARB1, IF2);
		reg2 = CAN_IF_Read(ARB2, IF2);
		msg_id = (reg1|(reg2<<16));
	}
	else
	{
		/* bit 28-18 is 11-bit standard frame */
		msg_id = (CAN_IF_Read(ARB2, IF2) &0x1FFF) >> 2;
	}

	p_add[0] = msg_id;
	p_add[1] = CAN_IF_Read(MCTRL, IF2) & 0x000F;	/* Get Msg Obj Data length */
	p_add[2] = (CAN_IF_Read(DA2, IF2)<<16) | CAN_IF_Read(DA1, IF2);
	p_add[3] = (CAN_IF_Read(DB2, IF2)<<16) | CAN_IF_Read(DB1, IF2);

	/* Clear interrupt pending bit */
	CAN_IF_Write(MCTRL, IF2, UMSK|RXIE|EOB|CAN_DLC_MAX);
	/* Save changes to message RAM */
	CAN_IF_writeBuf(IF2, msg_no);

	return;
}
/*********************************************************************//**
 * @brief		Handle valid transmit message
 * @param[in]	msg_no Message Object number
 * @return 		None
 **********************************************************************/
void CAN_TxInt_MessageProcess( uint8_t msg_no )
{
	/* Clear interrupt pending bit */
	CAN_IF_Write(MCTRL, IF2, UMSK|RXIE|EOB|CAN_DLC_MAX);
	/* Save changes to message RAM */
	CAN_IF_writeBuf(IF2,msg_no);
	return;
}

/*********************************************************************//**
 * @brief		CAN interrupt handler
 * @param[in]	None
 * @return 		None
 **********************************************************************/
volatile uint32_t nd_tmp;
void CAN_IRQHandler(void)
{
	uint32_t canstat = 0;
	uint32_t can_int, msg_no;

	while ( (can_int = LPC_C_CAN0->INT) != 0 )	/* While interrupt is pending */
	{
		canstat = LPC_C_CAN0->STAT;				/* Read CAN status register */

		if ( can_int & CAN_STATUS_INTERRUPT )
		{
			/* Passive state monitored frequently in main. */

			if ( canstat & STAT_EWARN )
			{
				EWarnCnt++;
				return;
			}
			if ( canstat & STAT_BOFF )
			{
				BOffCnt++;
				return;
			}

			switch (canstat&STAT_LEC)	/* LEC Last Error Code (Type of the last error to occur on the CAN bus) */
			{
				case NO_ERR:
					break;
				case STUFF_ERR:
					StuffErrCnt++;
					break;
				case FORM_ERR:
					FormErrCnt++;
					break;
				case ACK_ERR:
					AckErrCnt++;
					break;
				case BIT1_ERR:
					Bit1ErrCnt++;
					break;
				case BIT0_ERR:
					Bit0ErrCnt++;
					break;
				case CRC_ERR:
					CRCErrCnt++;
					break;
				default:
					break;
			}

			/* Clear all warning/error states except RXOK/TXOK */
			LPC_C_CAN0->STAT &= STAT_RXOK|STAT_TXOK;
		}
		else
		{
			if ( (canstat & STAT_LEC) == 0 ) 	/* NO ERROR */
			{
				msg_no = can_int & 0x7FFF;
				if((msg_no >= 1 ) && (msg_no <= 16))
				{
					LPC_C_CAN0->STAT &= ~STAT_RXOK;
					/* Check if message number is correct by reading NEWDAT registers.
					 By reading out the NEWDAT bits, the CPU can check for which Message
					 Object the data portion was updated
					 Only first 16 message object used for receive : only use ND1 */
					if((1<<(msg_no-1)) != LPC_C_CAN0->ND1)
					{
						/* message object does not contain new data! */
						ND1ErrCnt++;
						break;
					}
					CAN_RxInt_MessageProcess(msg_no);
					RX_cb(msg_no);
				}
				else
				{
				 	LPC_C_CAN0->STAT &= ~STAT_TXOK;
					CAN_TxInt_MessageProcess(msg_no);
					TX_cb(msg_no);
				}
			}
		}
	}
	return;
}

/*********************************************************************//**
 * @brief		Initialize CAN peripheral
 * @param[in]	BitClk CAN bit clock setting
 * @param[in]	ClkDiv CAN bit clock setting
 * @param[in]	Tx_cb point to call-back function when transmitted
 * @param[in]	Rx_cb point to call-back function when received
 * @return 		None
 **********************************************************************/
void CAN_Init( uint32_t BitClk, CCAN_CLKDIV_Type ClkDiv , MSG_CB Tx_cb, MSG_CB Rx_cb)
{

	RX_cb = Rx_cb;
	TX_cb = Tx_cb;
	if ( !(LPC_C_CAN0->CNTL & CTRL_INIT) )
	{
		/* If it's in normal operation already, stop it, reconfigure
		 everything first, then restart.  */
		LPC_C_CAN0->CNTL |= CTRL_INIT;	/* Default state */
	}

	LPC_C_CAN0->CLKDIV = ClkDiv;			/* Divider for CAN VPB3 clock */
	LPC_C_CAN0->CNTL |= CTRL_CCE;		/* Start configuring bit timing */
	LPC_C_CAN0->BT = BitClk;
	LPC_C_CAN0->BRPE = 0x0000;
	LPC_C_CAN0->CNTL &= ~CTRL_CCE;		/* Stop configuring bit timing */

	LPC_C_CAN0->CNTL &= ~CTRL_INIT;		/* Initialization finished, normal operation now. */
	while ( LPC_C_CAN0->CNTL & CTRL_INIT );

	/* By default, auto TX is enabled, enable all related interrupts */
	LPC_C_CAN0->CNTL |= (CTRL_IE|CTRL_SIE|CTRL_EIE);
	return;
}

/*********************************************************************//**
 * @brief		Send a message to the CAN port
 * @param[in]	msg_no message object number
 * @param[in]	msg_ptr msg buffer pointer
 * @return 		None
 **********************************************************************/
void CAN_Send(uint8_t msg_no, uint32_t *msg_ptr )
{
	uint32_t tx_id, Length;

	if(msg_ptr == NULL) return;

	/* first is the ID, second is length, the next four are data */
	tx_id = *msg_ptr++;
	Length = *msg_ptr++;

	if(Length>CAN_DLC_MAX)Length = CAN_DLC_MAX;
	CAN_IF_Write(MCTRL, IF1, UMSK|TXIE|TXRQ|EOB|RMTEN|(Length & DLC_MASK));
	CAN_IF_Write(DA1, IF1, *msg_ptr);			/* Lower two bytes of message pointer */
	CAN_IF_Write(DA2, IF1, (*msg_ptr++)>>16);	/* Upper two bytes of message pointer */
	CAN_IF_Write(DB1, IF1, *msg_ptr);			/* Lower two bytes of message pointer */
	CAN_IF_Write(DB2, IF1, (*msg_ptr)>>16);		/* Upper two bytes of message pointer */

	/* Configure arbitration */
	if(!(tx_id & (0x1<<30)))					/* bit 30 is 0, standard frame */
	{
		/* Mxtd: 0, Mdir: 1, Mask is 0x7FF */
		CAN_IF_Write(MSK2, IF1, MASK_MDIR | (ID_STD_MASK << 2));
		CAN_IF_Write(MSK1, IF1, 0x0000);

		/* MsgVal: 1, Mtd: 0, Dir: 1, ID = 0x200 */
		CAN_IF_Write(ARB1, IF1, 0x0000);
		CAN_IF_Write(ARB2, IF1, ID_MVAL| ID_DIR | (tx_id << 2));
	}
	else										/* Extended frame */
	{
		/* Mxtd: 1, Mdir: 1, Mask is 0x7FF */
		CAN_IF_Write(MSK2, IF1, MASK_MXTD | MASK_MDIR | (ID_EXT_MASK >> 16));
		CAN_IF_Write(MSK1, IF1, ID_EXT_MASK & 0x0000FFFF);

		/* MsgVal: 1, Mtd: 1, Dir: 1, ID = 0x200000 */
		CAN_IF_Write(ARB1, IF1, tx_id & 0x0000FFFF);
		CAN_IF_Write(ARB2, IF1, ID_MVAL|ID_MTD | ID_DIR | (tx_id >> 16));
	}

  	/* Write changes to message RAM */
	CAN_IF_writeBuf(IF1, msg_no);

	return;
}

/*********************************************************************//**
 * @brief		Listen for a message on CAN bus
 * @param[in]	msg_no message object number
 * @param[in]	msg_ptr msg buffer pointer
 * @param[in]	RemoteEnable Enable/disable remote frame support, should be:
 * 					- TRUE:	 enable
 * 					- FALSE: disable
 * @return 		None
 **********************************************************************/
void CAN_Recv(uint8_t msg_no, uint32_t *msg_ptr, Bool RemoteEnable)
{
	uint32_t rx_id = *msg_ptr;
	uint32_t rmten = 0;
	if(RemoteEnable){
		rmten = 1<<8;
	}
	if(!(rx_id & (0x1<<30))){ /* standard frame */

 		/* Mxtd: 0, Mdir: 0, Mask is 0x7FF */
	  	CAN_IF_Write(MSK1, IF1, 0x0000);
		CAN_IF_Write(MSK2, IF1, ID_STD_MASK << 2);
		/* MsgVal: 1, Mtd: 0, Dir: 0 */
		CAN_IF_Write(ARB1, IF1, 0x0000);
		CAN_IF_Write(MCTRL, IF1, rmten|UMSK|RXIE|EOB|CAN_DLC_MAX);
		CAN_IF_Write(DA1, IF1, 0x0000);
		CAN_IF_Write(DA2, IF1, 0x0000);
		CAN_IF_Write(DB1, IF1, 0x0000);
		CAN_IF_Write(DB2, IF1, 0x0000);
		CAN_IF_Write(ARB2, IF1, ID_MVAL | ((rx_id) << 2));
		/* Transfer data to message RAM */
		CAN_IF_writeBuf(IF1, msg_no);
	}

	else{
		rx_id &= (0x1<<30)-1 ; /* Mask ID bit */
		/* Mxtd: 1, Mdir: 0, Mask is 0x1FFFFFFF */
		CAN_IF_Write(MSK1, IF1, ID_EXT_MASK & 0xFFFF);
		CAN_IF_Write(MSK2, IF1, MASK_MXTD | (ID_EXT_MASK >> 16));
		/* MsgVal: 1, Mtd: 1, Dir: 0 */
		CAN_IF_Write(ARB1, IF1, (rx_id) & 0xFFFF);
		CAN_IF_Write(MCTRL, IF1, rmten|UMSK|RXIE|EOB|CAN_DLC_MAX);
		CAN_IF_Write(DA1, IF1, 0x0000);
		CAN_IF_Write(DA2, IF1, 0x0000);
		CAN_IF_Write(DB1, IF1, 0x0000);
		CAN_IF_Write(DB2, IF1, 0x0000);
		CAN_IF_Write(ARB2, IF1, ID_MVAL | ID_MTD | ((rx_id) >> 16));
		/* Transfer data to message RAM */
		CAN_IF_writeBuf(IF1, msg_no);
	}
	return;
}

/*********************************************************************//**
 * @brief		Read a message from Message RAM to buffer
 * @param[in]	msg_no message object number
 * @param[in]	buff msg buffer pointer
 * @return 		None
 **********************************************************************/
void CAN_ReadMsg(uint32_t msg_no, message_object* buff){
	int i;
	buff->id = recv_buff.id;
	buff->dlc = recv_buff.dlc;
	if(recv_buff.dlc>CAN_DLC_MAX) recv_buff.dlc = CAN_DLC_MAX;
	for(i=0;i<recv_buff.dlc;i++)
		buff->data[i] = recv_buff.data[i];
}

#endif /* _C_CAN*/
/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */


