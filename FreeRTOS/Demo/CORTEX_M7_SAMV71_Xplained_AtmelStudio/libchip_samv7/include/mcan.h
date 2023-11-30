/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 *  \file
 *
 *  \section Purpose
 *
 *  Interface for configuring and using Timer Counter (TC) peripherals.
 *
 *  \section Usage
 *  -# Optionally, use TC_FindMckDivisor() to let the program find the best
 *     TCCLKS field value automatically.
 *  -# Configure a Timer Counter in the desired mode using TC_Configure().
 *  -# Start or stop the timer clock using TC_Start() and TC_Stop().
 */

#ifndef _MCAN_
#define _MCAN_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Global functions
 *------------------------------------------------------------------------------*/

#ifdef __cplusplus
 extern "C" {
#endif

typedef enum
{
	CAN_STD_ID = 0,
	CAN_EXT_ID = 1
} MCan_IdType;
   
typedef enum
{
	CAN_DLC_0 = 0,
	CAN_DLC_1 = 1,
	CAN_DLC_2 = 2,
	CAN_DLC_3 = 3,
	CAN_DLC_4 = 4,
	CAN_DLC_5 = 5,
	CAN_DLC_6 = 6,
	CAN_DLC_7 = 7,
	CAN_DLC_8 = 8,
	CAN_DLC_12 = 9,
	CAN_DLC_16 = 10,
	CAN_DLC_20 = 11,
	CAN_DLC_24 = 12,
	CAN_DLC_32 = 13,
	CAN_DLC_48 = 14,
	CAN_DLC_64 = 15
} MCan_DlcType;

typedef enum
{
	CAN_FIFO_0 = 0,
	CAN_FIFO_1 = 1
} MCan_FifoType;

typedef enum
{
	CAN_INTR_LINE_0 = 0,
	CAN_INTR_LINE_1 = 1
} MCan_IntrLineType;

typedef struct MailboxInfoTag
{
	uint32_t   id;
	uint32_t   length;
	uint32_t   timestamp;
} MailboxInfoType;


typedef struct MailBox8Tag
{
	MailboxInfoType info;
	uint8_t         data[8];
} Mailbox8Type;

typedef struct MailBox12Tag
{
	MailboxInfoType info;
	uint8_t         data[12];
} Mailbox12Type;

typedef struct MailBox16Tag
{
	MailboxInfoType info;
	uint8_t         data[16];
} Mailbox16Type;

typedef struct MailBox20Tag
{
	MailboxInfoType info;
	uint8_t         data[20];
} Mailbox20Type;

typedef struct MailBox24Tag
{
	MailboxInfoType info;
	uint8_t         data[24];
} Mailbox24Type;

typedef struct MailBox32Tag
{
	MailboxInfoType info;
	uint8_t         data[32];
} Mailbox32ype;

typedef struct MailBox48Tag
{
	MailboxInfoType info;
	uint8_t         data[48];
} Mailbox48Type;

typedef struct MailBox64Tag
{
	MailboxInfoType info;
	uint8_t         data[64];
} Mailbox64Type;



typedef struct MCan_MsgRamPntrsTag
{
	uint32_t * pStdFilts;
	uint32_t * pExtFilts;
	uint32_t * pRxFifo0;
	uint32_t * pRxFifo1;
	uint32_t * pRxDedBuf;
	uint32_t * pTxEvtFifo;
	uint32_t * pTxDedBuf;
	uint32_t * pTxFifoQ;
} MCan_MsgRamPntrs;

typedef struct MCan_ConfigTag
{
	Mcan            * pMCan;
	uint32_t          bitTiming;
	uint32_t          fastBitTiming;
	uint32_t          nmbrStdFilts;
	uint32_t          nmbrExtFilts;  
	uint32_t          nmbrFifo0Elmts;
	uint32_t          nmbrFifo1Elmts;
	uint32_t          nmbrRxDedBufElmts;
	uint32_t          nmbrTxEvtFifoElmts;
	uint32_t          nmbrTxDedBufElmts;
	uint32_t          nmbrTxFifoQElmts;  
	uint32_t          rxFifo0ElmtSize;
	uint32_t          rxFifo1ElmtSize;
	uint32_t          rxBufElmtSize;   
	// Element sizes and data sizes (encoded element size)  
	uint32_t          txBufElmtSize;    
	// Element size and data size (encoded element size)
	MCan_MsgRamPntrs  msgRam;
} MCan_ConfigType;   

extern const MCan_ConfigType mcan0Config;
extern const MCan_ConfigType mcan1Config;

__STATIC_INLINE uint32_t MCAN_IsTxComplete( 
	const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	return ( mcan->MCAN_IR & MCAN_IR_TC );
}

__STATIC_INLINE void MCAN_ClearTxComplete( 
	const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_IR = MCAN_IR_TC;
}

__STATIC_INLINE uint32_t MCAN_IsMessageStoredToRxDedBuffer( 
	const MCan_ConfigType * mcanConfig )
{
  Mcan * mcan = mcanConfig->pMCan;

  return ( mcan->MCAN_IR & MCAN_IR_DRX );  
}

__STATIC_INLINE void MCAN_ClearMessageStoredToRxBuffer( 
	const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_IR = MCAN_IR_DRX;
}

__STATIC_INLINE uint32_t MCAN_IsMessageStoredToRxFifo0( 
	const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	return ( mcan->MCAN_IR & MCAN_IR_RF0N );  
}

__STATIC_INLINE void MCAN_ClearMessageStoredToRxFifo0( 
	const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_IR = MCAN_IR_RF0N;
}

__STATIC_INLINE uint32_t MCAN_IsMessageStoredToRxFifo1( 
	const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	return ( mcan->MCAN_IR & MCAN_IR_RF1N );  
}

__STATIC_INLINE void MCAN_ClearMessageStoredToRxFifo1( 
	const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_IR = MCAN_IR_RF1N;
}

void MCAN_Init( 
	const MCan_ConfigType * mcanConfig );

void MCAN_InitFdEnable( 
	const MCan_ConfigType * mcanConfig );

void MCAN_InitFdBitRateSwitchEnable( 
	const MCan_ConfigType * mcanConfig );

void MCAN_InitTxQueue( 
	const MCan_ConfigType * mcanConfig );

void MCAN_InitLoopback( 
	const MCan_ConfigType * mcanConfig );

void MCAN_Enable( 
	const MCan_ConfigType * mcanConfig );

void MCAN_RequestIso11898_1( 
	const MCan_ConfigType * mcanConfig );

void MCAN_RequestFd( 
	const MCan_ConfigType * mcanConfig );

void MCAN_RequestFdBitRateSwitch( 
	const MCan_ConfigType * mcanConfig );

void MCAN_LoopbackOn( 
	const MCan_ConfigType * mcanConfig );

void MCAN_LoopbackOff( 
	const MCan_ConfigType * mcanConfig );

void MCAN_IEnableMessageStoredToRxDedBuffer( 
	const MCan_ConfigType * mcanConfig, 
	MCan_IntrLineType line );

uint8_t  * MCAN_ConfigTxDedBuffer( 
	const MCan_ConfigType * mcanConfig, 
	uint8_t buffer, 
	uint32_t id, 
	MCan_IdType idType, 
	MCan_DlcType dlc );

void MCAN_SendTxDedBuffer( 
	const MCan_ConfigType * mcanConfig, 
	uint8_t buffer );

uint32_t MCAN_AddToTxFifoQ( 
	const MCan_ConfigType * mcanConfig, 
	uint32_t id, MCan_IdType idType, 
	MCan_DlcType dlc, uint8_t * data );

uint8_t MCAN_IsBufferTxd( 
	const MCan_ConfigType * mcanConfig, 
	uint8_t buffer );

void MCAN_ConfigRxBufferFilter( 
	const MCan_ConfigType * mcanConfig, 
	uint32_t buffer, 
	uint32_t filter, 
	uint32_t id, 
	MCan_IdType idType);

void MCAN_ConfigRxClassicFilter( 
	const MCan_ConfigType * mcanConfig,
	MCan_FifoType fifo, 
	uint8_t filter, 
	uint32_t id, 
	MCan_IdType idType, 
	uint32_t mask );

uint8_t MCAN_IsNewDataInRxDedBuffer( 
	const MCan_ConfigType * mcanConfig, 
	uint8_t buffer );

void MCAN_GetRxDedBuffer( 
	const MCan_ConfigType * mcanConfig, 
	uint8_t buffer, 
	Mailbox64Type * pRxMailbox );

uint32_t MCAN_GetRxFifoBuffer( 
	const MCan_ConfigType * mcanConfig, 
	MCan_FifoType fifo, 
	Mailbox64Type * pRxMailbox );

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _MCAN_ */

