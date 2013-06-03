/*
 * @brief SD Card Interface Registers and control functions
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

#ifndef __SDC_001_H_
#define __SDC_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_SDC_001 IP: SDC register block and driver
 * @ingroup IP_Drivers
 * SD/MMC card Interface
 * @{
 */

/**
 * @brief SD/MMC card Interface (SDC) register block structure
 */
typedef struct {
	__IO uint32_t POWER;        /*!< Power Control register */
	__IO uint32_t CLOCK;        /*!< Clock control regsiter */
	__IO uint32_t ARGUMENT;     /*!< Command argument register */
	__IO uint32_t COMMAND;      /*!< Command register */
	__I  uint32_t RESPCMD;      /*!< Command response register */
	__I  uint32_t RESPONSE[4];  /*!< Response registers */
	__IO uint32_t DATATIMER;    /*!< Data timer register */
	__IO uint32_t DATALENGTH;   /*!< Data length register */
	__IO uint32_t DATACTRL;     /*!< Data control register */
	__I  uint32_t DATACNT;      /*!< Data count register */
	__I  uint32_t STATUS;       /*!< Status register */
	__O  uint32_t CLEAR;        /*!< Clear register */
	__IO uint32_t MASK0;        /*!< Mask 0 register */
	uint32_t RESERVED0[2];
	__I  uint32_t FIFOCNT;      /*!< FIFO count register */
	uint32_t RESERVED1[13];
	__IO uint32_t FIFO[16];     /*!< FIFO registers */
} IP_SDC_001_T;

/**
 * @brief SDC Power Control Register bit definitions
 */
/** SDC Power Control Register Bitmask */
#define SDC_PWR_BITMASK         ((uint32_t) 0xC3)
/** SDC Power Control Bit Mask */
#define SDC_PWR_CTRL_BITMASK    (((uint32_t) 0x03) << 0)
/** SDC Power Control */
#define SDC_PWR_CTRL(n)         (((uint32_t) (n & 0x03)) << 0)
/** SD_CMD Output Control */
#define SDC_PWR_OPENDRAIN       (((uint32_t) 1) << 6)
/** Rod Control */
#define SDC_PWR_ROD             (((uint32_t) 1) << 7)

/**
 * @brief SDC Clock Control Register bit definitions
 */
/** SDC Clock Control Register Bitmask */
#define SDC_CLOCK_BITMASK       ((uint32_t) 0xFFF)
/** SDC Clock Divider Bitmask */
#define SDC_CLOCK_CLKDIV_BITMASK    (((uint32_t) 0xFF ) << 0)
/** Set SDC Clock Divide value */
#define SDC_CLOCK_CLKDIV(n)     (((uint32_t) (n & 0x0FF)) << 0)

/**
 * @brief SDC Command Register bit definitions
 */
/** SDC Command Register Bitmask */
#define SDC_COMMAND_BITMASK     ((uint32_t) 0x7FF)
/** SDC Command Index Bitmask */
#define SDC_COMMAND_INDEX_BITMASK   ((uint32_t) 0x3F)
/** Set SDC Command Index */
#define SDC_COMMAND_INDEX(n)        ((uint32_t) n & 0x3F)
/** No response is expected */
#define SDC_COMMAND_NO_RSP          (((uint32_t) 0 ) << 6)
/** Short response is expected */
#define SDC_COMMAND_SHORT_RSP       (((uint32_t) 1 ) << 6)
/** Long response is expected */
#define SDC_COMMAND_LONG_RSP        (((uint32_t) 3 ) << 6)
/** Response bit mask */
#define SDC_COMMAND_RSP_BITMASK     (((uint32_t) 3 ) << 6)
/** Mark that command timer is disabled and CPSM waits for interrupt request */
#define SDC_COMMAND_INTERRUPT       (((uint32_t) 1 ) << 8)
/** Mark that CPSM waits for CmdPend before starting sending a command*/
#define SDC_COMMAND_PENDING     (((uint32_t) 1 ) << 9)
/** Enable CPSM */
#define SDC_COMMAND_ENABLE          (((uint32_t) 1 ) << 10)

/**
 * @brief SDC Command Response Register bit definitions
 */
/** SDC Command Response value */
#define SDC_RESPCOMMAND_VAL(n)      ((uint32_t) n & 0x3F)

/**
 * @brief SDC Data Length Register bit definitions
 */
/** SDC Data Length set */
#define SDC_DATALENGTH_LEN(n)       ((uint32_t) n & 0xFFFF)

/**
 * @brief SDC Data Control Register bit definitions
 */
/** SDC Data Control Register Bitmask */
#define SDC_DATACTRL_BITMASK        ((uint32_t) 0xFF)
/** Enable Data Transfer */
#define SDC_DATACTRL_ENABLE             (((uint32_t) 1 ) << 0)
/** Mark that Data is transfer from card to controller */
#define SDC_DATACTRL_DIR_FROMCARD       (((uint32_t) 1 ) << 1)
/** Mark that Data is transfer from controller to card */
#define SDC_DATACTRL_DIR_TOCARD         ((uint32_t) 0)
/** Mark that the transfer mode is Stream Data Transfer */
#define SDC_DATACTRL_XFER_MODE_STREAM   (((uint32_t) 1 ) << 2)
/** Mark that the transfer mode is Block Data Transfer */
#define SDC_DATACTRL_XFER_MODE_BLOCK    ((uint32_t) 0)
/** Enable DMA */
#define SDC_DATACTRL_DMA_ENABLE         (((uint32_t) 1 ) << 3)
/** Set Data Block size */
#define SDC_DATACTRL_BLOCKSIZE(n)       (((uint32_t) (n & 0x0F) ) << 4)
/** Get Data Block size value */
#define SDC_DATACTRL_BLOCKSIZE_VAL(n)   (((uint32_t) 1) << n)

/**
 * @brief SDC Data Counter Register bit definitions
 */
#define SDC_DATACNT_VAL(n)          ((uint32_t) n & 0xFFFF)

/**
 * @brief SDC Status Register bit definitions
 */
/** Command Response received (CRC check failed) */
#define SDC_STATUS_CMDCRCFAIL     (((uint32_t) 1 ) << 0)
/** Data block sent/received (CRC check failed). */
#define SDC_STATUS_DATACRCFAIL     (((uint32_t) 1 ) << 1)
/** Command response timeout.. */
#define SDC_STATUS_CMDTIMEOUT     (((uint32_t) 1 ) << 2)
/** Data timeout. */
#define SDC_STATUS_DATATIMEOUT     (((uint32_t) 1 ) << 3)
/** Transmit FIFO underrun error. */
#define SDC_STATUS_TXUNDERRUN     (((uint32_t) 1 ) << 4)
/** Receive FIFO overrun error. */
#define SDC_STATUS_RXOVERRUN     (((uint32_t) 1 ) << 5)
/** Command response received (CRC check passed). */
#define SDC_STATUS_CMDRESPEND     (((uint32_t) 1 ) << 6)
/** Command sent (no response required).*/
#define SDC_STATUS_CMDSENT     (((uint32_t) 1 ) << 7)
/** Data end (data counter is zero).*/
#define SDC_STATUS_DATAEND     (((uint32_t) 1 ) << 8)
/** Start bit not detected on all data signals in wide bus mode..*/
#define SDC_STATUS_STARTBITERR     (((uint32_t) 1 ) << 9)
/** Data block sent/received (CRC check passed).*/
#define SDC_STATUS_DATABLOCKEND     (((uint32_t) 1 ) << 10)
/** Command transfer in progress.*/
#define SDC_STATUS_CMDACTIVE     (((uint32_t) 1 ) << 11)
/** Data transmit in progress.*/
#define SDC_STATUS_TXACTIVE     (((uint32_t) 1 ) << 12)
/** Data receive in progress.*/
#define SDC_STATUS_RXACTIVE     (((uint32_t) 1 ) << 13)
/** Transmit FIFO half empty.*/
#define SDC_STATUS_TXFIFOHALFEMPTY     (((uint32_t) 1 ) << 14)
/** Receive FIFO half full.*/
#define SDC_STATUS_RXFIFOHALFFULL     (((uint32_t) 1 ) << 15)
/** Transmit FIFO full.*/
#define SDC_STATUS_TXFIFOFULL     (((uint32_t) 1 ) << 16)
/** Receive FIFO full.*/
#define SDC_STATUS_RXFIFOFULL     (((uint32_t) 1 ) << 17)
/** Transmit FIFO empty.*/
#define SDC_STATUS_TXFIFOEMPTY     (((uint32_t) 1 ) << 18)
/** Receive FIFO empty.*/
#define SDC_STATUS_RXFIFOEMPTY     (((uint32_t) 1 ) << 19)
/** Data available in transmit FIFO.*/
#define SDC_STATUS_TXDATAAVLBL     (((uint32_t) 1 ) << 20)
/** Data available in receive FIFO.*/
#define SDC_STATUS_RXDATAAVLBL     (((uint32_t) 1 ) << 21)
/** Command Error Status */
#define SDC_STATUS_CMDERR    (SDC_STATUS_CMDCRCFAIL | SDC_STATUS_CMDTIMEOUT | SDC_STATUS_STARTBITERR)
/** Data Error Status */
#define SDC_STATUS_DATAERR    (SDC_STATUS_DATACRCFAIL | SDC_STATUS_DATATIMEOUT | SDC_STATUS_TXUNDERRUN \
							   | SDC_STATUS_RXOVERRUN | SDC_STATUS_STARTBITERR)
/** FIFO Status*/
#define SDC_STATUS_FIFO    (SDC_STATUS_TXFIFOHALFEMPTY | SDC_STATUS_RXFIFOHALFFULL \
							| SDC_STATUS_TXFIFOFULL  | SDC_STATUS_RXFIFOFULL \
							| SDC_STATUS_TXFIFOEMPTY | SDC_STATUS_RXFIFOEMPTY \
							| SDC_STATUS_DATABLOCKEND)

/** Data Transfer Status*/
#define SDC_STATUS_DATA    (SDC_STATUS_DATAEND )

/**
 * @brief SDC Clear Register bit definitions
 */
/** Clear all status flag*/
#define SDC_CLEAR_ALL       ((uint32_t) 0x7FF)
/** Clears CmdCrcFail flag.*/
#define SDC_CLEAR_CMDCRCFAIL     (((uint32_t) 1 ) << 0)
/** Clears DataCrcFail flag. */
#define SDC_CLEAR_DATACRCFAIL     (((uint32_t) 1 ) << 1)
/** Clears CmdTimeOut flag. */
#define SDC_CLEAR_CMDTIMEOUT     (((uint32_t) 1 ) << 2)
/** Clears DataTimeOut flag. */
#define SDC_CLEAR_DATATIMEOUT     (((uint32_t) 1 ) << 3)
/** Clears TxUnderrun flag. */
#define SDC_CLEAR_TXUNDERRUN     (((uint32_t) 1 ) << 4)
/**Clears RxOverrun flag. */
#define SDC_CLEAR_RXOVERRUN     (((uint32_t) 1 ) << 5)
/** Clears CmdRespEnd flag. */
#define SDC_CLEAR_CMDRESPEND     (((uint32_t) 1 ) << 6)
/** Clears CmdSent flag.*/
#define SDC_CLEAR_CMDSENT     (((uint32_t) 1 ) << 7)
/**Clears DataEnd flag.*/
#define SDC_CLEAR_DATAEND     (((uint32_t) 1 ) << 8)
/** Clears StartBitErr flag.*/
#define SDC_CLEAR_STARTBITERR     (((uint32_t) 1 ) << 9)
/** Clears DataBlockEnd flag.*/
#define SDC_CLEAR_DATABLOCKEND     (((uint32_t) 1 ) << 10)

/**
 * @brief SDC Interrupt Mask Register bit definitions
 */
/** Mask CmdCrcFail flag.*/
#define SDC_MASK0_CMDCRCFAIL     (((uint32_t) 1 ) << 0)
/** Mask DataCrcFail flag. */
#define SDC_MASK0_DATACRCFAIL     (((uint32_t) 1 ) << 1)
/** Mask CmdTimeOut flag. */
#define SDC_MASK0_CMDTIMEOUT     (((uint32_t) 1 ) << 2)
/** Mask DataTimeOut flag. */
#define SDC_MASK0_DATATIMEOUT     (((uint32_t) 1 ) << 3)
/** Mask TxUnderrun flag. */
#define SDC_MASK0_TXUNDERRUN     (((uint32_t) 1 ) << 4)
/** Mask RxOverrun flag. */
#define SDC_MASK0_RXOVERRUN     (((uint32_t) 1 ) << 5)
/** Mask CmdRespEnd flag. */
#define SDC_MASK0_CMDRESPEND     (((uint32_t) 1 ) << 6)
/** Mask CmdSent flag.*/
#define SDC_MASK0_CMDSENT     (((uint32_t) 1 ) << 7)
/** Mask DataEnd flag.*/
#define SDC_MASK0_DATAEND     (((uint32_t) 1 ) << 8)
/** Mask StartBitErr flag.*/
#define SDC_MASK0_STARTBITERR     (((uint32_t) 1 ) << 9)
/** Mask DataBlockEnd flag.*/
#define SDC_MASK0_DATABLOCKEND     (((uint32_t) 1 ) << 10)
/** Mask CmdActive flag.*/
#define SDC_MASK0_CMDACTIVE     (((uint32_t) 1 ) << 11)
/** Mask TxActive flag.*/
#define SDC_MASK0_TXACTIVE     (((uint32_t) 1 ) << 12)
/** Mask RxActive flag.*/
#define SDC_MASK0_RXACTIVE     (((uint32_t) 1 ) << 13)
/** Mask TxFifoHalfEmpty flag.*/
#define SDC_MASK0_TXFIFOHALFEMPTY     (((uint32_t) 1 ) << 14)
/** Mask RxFifoHalfFull flag.*/
#define SDC_MASK0_RXFIFOHALFFULL     (((uint32_t) 1 ) << 15)
/** Mask TxFifoFull flag.*/
#define SDC_MASK0_TXFIFOFULL     (((uint32_t) 1 ) << 16)
/** Mask RxFifoFull flag.*/
#define SDC_MASK0_RXFIFOFULL     (((uint32_t) 1 ) << 17)
/** Mask TxFifoEmpty flag.*/
#define SDC_MASK0_TXFIFOEMPTY     (((uint32_t) 1 ) << 18)
/** Mask RxFifoEmpty flag.*/
#define SDC_MASK0_RXFIFOEMPTY     (((uint32_t) 1 ) << 19)
/** Mask TxDataAvlbl flag.*/
#define SDC_MASK0_TXDATAAVLBL     (((uint32_t) 1 ) << 20)
/** Mask RxDataAvlbl flag.*/
#define SDC_MASK0_RXDATAAVLBL     (((uint32_t) 1 ) << 21)
/** CMD error interrupt mask */
#define SDC_MASK0_CMDERR    (SDC_MASK0_CMDCRCFAIL | SDC_MASK0_CMDTIMEOUT | SDC_MASK0_STARTBITERR)
/** Data Transmit Error interrupt mask */
#define SDC_MASK0_TXDATAERR    (SDC_MASK0_DATACRCFAIL | SDC_MASK0_DATATIMEOUT | SDC_MASK0_TXUNDERRUN | \
								SDC_MASK0_STARTBITERR)

/** Data Receive Error interrupt mask */
#define SDC_MASK0_RXDATAERR    (SDC_MASK0_DATACRCFAIL | SDC_MASK0_DATATIMEOUT | SDC_MASK0_RXOVERRUN | \
								SDC_MASK0_STARTBITERR)
/** TX FIFO interrupt mask*/
#define SDC_MASK0_TXFIFO    (SDC_MASK0_TXFIFOHALFEMPTY | SDC_MASK0_DATABLOCKEND )
/** RX FIFO interrupt mask*/
#define SDC_MASK0_RXFIFO    (SDC_MASK0_RXFIFOHALFFULL  | SDC_MASK0_DATABLOCKEND )

/** Data Transfer interrupt mask*/
#define SDC_MASK0_DATA    (SDC_MASK0_DATAEND | SDC_MASK0_DATABLOCKEND )

/**
 * @brief SDC FIFO Counter Register bit definitions
 */
#define SDC_FIFOCNT_VAL(n)          ((uint32_t) n & 0x7FFF)

/* The number of bytes used to store card status*/
#define SDC_CARDSTATUS_BYTENUM              ((uint32_t) 4)

/**
 * @brief SDC Power Control Options
 */
typedef enum IP_SDC_001_PWR_CTRL {
	SDC_POWER_OFF = 0,		/*!< Power-off */
	SDC_POWER_UP = 2,		/*!< Power-up */
	SDC_POWER_ON = 3,		/*!< Power-on */
} IP_SDC_001_PWR_CTRL_T;

/**
 * @brief SDC Clock Control Options
 */
typedef enum IP_SDC_001_CLOCK_CTRL {
	SDC_CLOCK_ENABLE = 8,		   /*!< Enable SD Card Bus Clock */
	SDC_CLOCK_POWER_SAVE = 9,	   /*!< Disable SD_CLK output when bus is idle */
	SDC_CLOCK_DIVIDER_BYPASS = 10, /*!< Enable bypass of clock divide logic */
	SDC_CLOCK_WIDEBUS_MODE = 11,   /*!< Enable wide bus mode (SD_DAT[3:0] is used instead of SD_DAT[0]) */
} IP_SDC_001_CLOCK_CTRL_T;

/**
 * @brief SDC Response type
 */
typedef enum IP_SDC_001_RESPONSE {
	SDC_NO_RESPONSE = SDC_COMMAND_NO_RSP,       /*!< No response */
	SDC_SHORT_RESPONSE = SDC_COMMAND_SHORT_RSP, /*!< Short response */
	SDC_LONG_RESPONSE = SDC_COMMAND_LONG_RSP,   /*!< Long response */
} IP_SDC_001_RESPONSE_T;

/**
 * @brief SDC Data Transfer Direction definitions
 */
typedef enum IP_SDC_001_TRANSFER_DIR {
	SDC_TRANSFER_DIR_FROMCARD = SDC_DATACTRL_DIR_FROMCARD, /*!< Transfer from card */
	SDC_TRANSFER_DIR_TOCARD = SDC_DATACTRL_DIR_TOCARD,     /*!< Transfer to card */
} IP_SDC_001_TRANSFER_DIR_T;

/**
 * @brief SDC Data Transfer Mode definitions
 */
typedef enum IP_SDC_001_TRANSFER_MODE {
	SDC_TRANSFER_MODE_STREAM = SDC_DATACTRL_XFER_MODE_STREAM, /*!< Stream transfer mode */
	SDC_TRANSFER_MODE_BLOCK = SDC_DATACTRL_XFER_MODE_BLOCK,   /*!< Block transfer mode */
} IP_SDC_001_TRANSFER_MODE_T;

/**
 * @brief SDC Data Block size definitions (in bytes)
 */
typedef enum IP_SDC_001_BLOCK_SIZE {
	SDC_BLOCK_SIZE_1 = 0,     /*!< Block size - 1 byte */
	SDC_BLOCK_SIZE_2,         /*!< Block size - 2 bytes */ 
	SDC_BLOCK_SIZE_4,         /*!< Block size - 4 bytes */
	SDC_BLOCK_SIZE_8,         /*!< Block size - 8 bytes */
	SDC_BLOCK_SIZE_16,        /*!< Block size - 16 bytes */
	SDC_BLOCK_SIZE_32,        /*!< Block size - 32 bytes */
	SDC_BLOCK_SIZE_64,        /*!< Block size - 64 bytes */
	SDC_BLOCK_SIZE_128,       /*!< Block size - 128 bytes */
	SDC_BLOCK_SIZE_256,       /*!< Block size - 256 bytes */
	SDC_BLOCK_SIZE_512,       /*!< Block size - 512 bytes */
	SDC_BLOCK_SIZE_1024,      /*!< Block size - 1024 bytes */
	SDC_BLOCK_SIZE_2048,      /*!< Block size - 2048 bytes */
} IP_SDC_001_BLOCK_SIZE_T;

/**
 * @brief SDC Command Response structure
 */
typedef struct {
	uint8_t CmdIndex;			            /*!< Command Index of the command response received */
	uint32_t Data[SDC_CARDSTATUS_BYTENUM];	/* Card Status which can be stored in 1 or 4 bytes */
} IP_SDC_001_RESP_T;

/**
 * @brief SDC Data Transfer Setup structure
 */
typedef struct {
	uint16_t BlockNum;						/*!< The number of block which will be transfered */
	IP_SDC_001_BLOCK_SIZE_T BlockSize;		/*!< Data Block Length */
	IP_SDC_001_TRANSFER_DIR_T Dir;			/*!< Direction */
	IP_SDC_001_TRANSFER_MODE_T  Mode;		/*!< Mode */
	bool     DMAUsed;						/*!< true: DMA used */
	uint32_t Timeout;						/*!< Data Transfer timeout periods (in Card Bus Clock)*/
} IP_SDC_001_DATA_TRANSFER_T;

/**
 * @brief	Set the power state of SDC peripheral
 * @param	pSDC	: Pointer to SDC register block
 * @param	pwrMode	: Power mode
 * @param	flag	: Output control flag
 * @return	Nothing
 * @note	When the external power supply is switched on, the software first enters the power-up
 *  state, and waits until the supply output is stable before moving to the power-on state.
 *  During the power-up state, SD_PWR is set HIGH. The card bus outlets are disabled
 *  during both states.
 *  flag is or-ed bit value of SDC_PWR_OPENDRAIN and SDC_PWR_ROD
 */
void IP_SDC_PowerControl(IP_SDC_001_T *pSDC, IP_SDC_001_PWR_CTRL_T pwrMode, uint32_t flag);

/**
 * @brief	Set clock divider value for SDC peripheral
 * @param	pSDC	: Pointer to SDC register block
 * @param	div		: clock divider
 * @return	Nothing
 * @note	While the SD card interface is in identification mode, the SD_CLK frequency must be less
 *  than 400 kHz. The clock frequency can be changed to the maximum card bus frequency
 *  when relative card addresses are assigned to all cards.
 *	SD_CLK frequency = MCLK / [2x(ClkDiv+1)].
 */
void IP_SDC_SetClockDiv(IP_SDC_001_T *pSDC, uint8_t div);

/**
 * @brief	Set or Reset clock control of SDC peripheral
 * @param	pSDC		: Pointer to SDC register block
 * @param	ctrlType	: Clock Control type
 * @param	NewState	: New State to set
 * @return	Nothing
 */
void IP_SDC_ClockControl(IP_SDC_001_T *pSDC, IP_SDC_001_CLOCK_CTRL_T ctrlType,
						 FunctionalState NewState);

/**
 * @brief	Set SDC Command Information
 * @param	pSDC	: Pointer to SDC register block
 * @param	Cmd	    : Command value
 * @param   Arg     : Argument for the command
 * @return	Nothing
 */
void IP_SDC_SetCommand(IP_SDC_001_T *pSDC, uint32_t Cmd, uint32_t Arg);

/**
 * @brief	Reset SDC Command Information
 * @param	pSDC	: Pointer to SDC register block
 * @return	Nothing
 */
void IP_SDC_ResetCommand(IP_SDC_001_T *pSDC);

/**
 * @brief	Get SDC Response
 * @param	pSDC	: Pointer to SDC register block
 * @param	pResp	: Pointer to buffer storing response data
 * @return	Nothing
 */
void IP_SDC_GetResp(IP_SDC_001_T *pSDC, IP_SDC_001_RESP_T *pResp);

/**
 * @brief	Set SDC Data Timeout Period
 * @param	pSDC	: Pointer to SDC register block
 * @param	timeout	: Data timeout value in card bus clock periods
 * @return	Nothing
 */
STATIC INLINE void IP_SDC_SetDataTimer(IP_SDC_001_T *pSDC, uint32_t timeout)
{
	pSDC->DATATIMER = timeout;
}

/**
 * @brief	Set SDC Data Transfer Information
 * @param	pSDC		: Pointer to SDC register block
 * @param	pTransfer	: Pointer to Data Transfer structure
 * @return	Nothing
 */
void IP_SDC_SetDataTransfer(IP_SDC_001_T *pSDC, IP_SDC_001_DATA_TRANSFER_T *pTransfer);

/**
 * @brief	Write Data to FIFO
 * @param	pSDC		: Pointer to SDC register block
 * @param	pSrc		: Pointer to data buffer
 * @param	bFirstHalf	: true (write to the first half of FIFO) false (write to the second half of FIFO)
 * @return	Nothing
 */
void IP_SDC_WriteFIFO(IP_SDC_001_T *pSDC, uint32_t *pSrc, bool bFirstHalf);

/**
 * @brief	Write Data to FIFO
 * @param	pSDC	: Pointer to SDC register block
 * @param	pDst	: The buffer hold the data read
 * @param	bFirstHalf : true (read the first half of FIFO) false (read the second half of FIFO)
 * @return	Nothing
 */
void IP_SDC_ReadFIFO(IP_SDC_001_T *pSDC, uint32_t *pDst, bool bFirstHalf);

/**
 * @brief	Get status of SDC Peripheral
 * @param	pSDC	: Pointer to SDC register block
 * @return	Status (Or-ed bit value of SDC_STATUS_*)
 */
STATIC INLINE uint32_t IP_SDC_GetStatus(IP_SDC_001_T *pSDC)
{
	return pSDC->STATUS;
}

/**
 * @brief	Clear status of SDC Peripheral
 * @param	pSDC	: Pointer to SDC register block
 * @param	flag	: Status flag(s) to be cleared (Or-ed bit value of SDC_CLEAR_*)
 * @return	None
 */
STATIC INLINE void IP_SDC_ClearStatus(IP_SDC_001_T *pSDC, uint32_t flag)
{
	pSDC->CLEAR = flag;
}

/**
 * @brief	Set interrupt mask for SDC Peripheral
 * @param	pSDC	: Pointer to SDC register block
 * @param	mask	: Interrupt mask (Or-ed bit value of SDC_MASK0_*)
 * @return	None
 */
STATIC INLINE void IP_SDC_SetIntMask(IP_SDC_001_T *pSDC, uint32_t mask)
{
	pSDC->MASK0 = mask;
}

/**
 * @brief	Initialize the SDC card controller
 * @param	pSDC	: Pointer to SDC register block
 * @return	None
 */
void IP_SDC_Init(IP_SDC_001_T *pSDC);

/**
 * @brief	Deinitialise the SDC peripheral
 * @param	pSDC	: Pointer to SDC register block
 * @return	None
 */
STATIC INLINE void IP_SDC_DeInit(IP_SDC_001_T *pSDC)
{
	IP_SDC_PowerControl(pSDC, SDC_POWER_OFF, 0);
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __SDC_001_H_ */
