/**********************************************************************
* $Id$		lpc18xx_can.h			2011-06-02
*//**
* @file		lpc18xx_can.h
* @brief	Contains all macro definitions and function prototypes
* 			support for CAN firmware library on LPC18xx
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
/** @defgroup C_CAN C_CAN (Controller Area Network)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef __LPC18XX_CAN_H
#define __LPC18XX_CAN_H

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"


#ifdef __cplusplus
extern "C"
{
#endif

/* Public Macros -------------------------------------------------------------- */
/** @defgroup C_CAN_Public_Macros  C_CAN Public Macros
 * @{
 */

/** In BASIC_MODE IF1 registers are used directly as TX buffer, IF2 registers are used as RX buffer.
 * If not BASIC_MODE use message objects and IF registers to communicate with message buffers
 */
#define BASIC_MODE 		0

/** In Silent Mode, the CAN controller is able to receive valid data frames and valid remote
 * frames, but it sends only recessive bits on the CAN bus, and it cannot start a transmission
 */
#define SILENT_MODE		0

/** In Loop-back Mode, the CAN Core treats its own transmitted messages as received messages
 * and stores them (if they pass acceptance filtering) into a Receive Buffer.
 */
#define LOOPBACK_MODE	0

/** Enables receiving remote frame requests */
#define REMOTE_ENABLE	1

/**
 * @}
 */

/* Private Macros -------------------------------------------------------------- */
/** @defgroup C_CAN_Private_Macros  C_CAN Private Macros
 * @{
 */

/** MAX CAN message obj */
#define CAN_MSG_OBJ_MAX			0x0020
/** MAX data length */
#define CAN_DLC_MAX				8

/********************************************************************//**
 *  BRP+1 = Fpclk/(CANBitRate * QUANTAValue)
 * QUANTAValue = 1 + (Tseg1+1) + (Tseg2+1)
 * QUANTA value varies based on the Fpclk and sample point
 * e.g. (1) sample point is 87.5%, Fpclk is 48Mhz
 * the QUANTA should be 16
 * 		(2) sample point is 90%, Fpclk is 12.5Mhz
 * the QUANTA should be 10
 * 		 Fpclk = Fclk /APBDIV
 * or
 *  BitRate = Fcclk/(APBDIV * (BRP+1) * ((Tseg1+1)+(Tseg2+1)+1))
 */

/*********************************************************************//**
 * @brief CAN Bit Timing Values definitions at 8Mhz
 **********************************************************************/
/** Bitrate: 100K */
#define CAN_BITRATE100K12MHZ           0x00004509
/** Bitrate: 125K */
#define CAN_BITRATE125K12MHZ           0x00004507
/** Bitrate: 250K */
#define CAN_BITRATE250K12MHZ           0x00004503
/** Bitrate: 500K */
#define CAN_BITRATE500K12MHZ            0x00004501
/** Bitrate: 1000K */
#define CAN_BITRATE1000K12MHZ          0x00004500

/*********************************************************************//**
 * @brief CAN Bit Timing Values definitions at 16Mhz
 **********************************************************************/
/** Bitrate: 100K */
#define CAN_BITRATE100K16MHZ          0x00005809
/** Bitrate: 125K */
#define CAN_BITRATE125K16MHZ          0x00005807
/** Bitrate: 250K */
#define CAN_BITRATE250K16MHZ          0x00005803
/** Bitrate: 500K */
#define CAN_BITRATE500K16MHZ          0x00005801


/*********************************************************************//**
 * @brief CAN Bit Timing Values definitions at 24Mhz
 **********************************************************************/
/** Bitrate: 100K */
#define CAN_BITRATE100K24MHZ          0x00007E09
/** Bitrate: 125K */
#define CAN_BITRATE125K24MHZ          0x0000450F
/** Bitrate: 250K */
#define CAN_BITRATE250K24MHZ          0x00004507
/** Bitrate: 500K */
#define CAN_BITRATE500K24MHZ          0x00004503
/** Bitrate: 1000K */
#define CAN_BITRATE1000K24MHZ         0x00004501

/**
 * @}
 */


/* Public Types --------------------------------------------------------------- */
/** @defgroup CAN_Public_Types CAN Public Types
 * @{
 */

/*********************************************************************//**
 * @brief CAN enumeration
 **********************************************************************/

/**
 * @brief CAN interface register type definition
 */
typedef enum CCAN_IFREG
{
	CMDREQ = 0,				/**< Command request */
	CMDMSK = 1,				/**< Command mask */
	MSK1 = 2,				/**< Mask 1 */
	MSK2 = 3,				/**< Mask 2 */
	ARB1 = 4,				/**< Arbitration 1 */
	ARB2 = 5,				/**< Arbitration 2 */
	MCTRL = 6,				/**< Message control */
	DA1 = 7,				/**< Data A1 */
	DA2 = 8,				/**< Data A2 */
	DB1 = 9,				/**< Data B1 */
	DB2 = 10				/**< Data B2 */
}CCAN_IFREG_Type;

/**
 * @brief CAN Clock division rate type definition
 */
typedef enum CCAN_CLKDIV
{
	CLKDIV1		= 0,
	CLKDIV2		= 1,
	CLKDIV3		= 2,
	CLKDIV5		= 3,
	CLKDIV9		= 4,
	CLKDIV17	= 5,
	CLKDIV33	= 6,
	CLKDIV65	= 7
}CCAN_CLKDIV_Type;


/********************************************************************//**
* @brief Data structure definition for a CAN message
**********************************************************************/
/**
 * @brief CAN message object structure
 */
typedef struct
{
    uint32_t	id;		/**< ID of message, if bit 30 is set then this is extended frame */
    uint32_t 	dlc;	/**< Message data length */
    uint8_t	data[8]; 	/**< Message data */
} message_object;

/**
 * @brief CAN call-back function
 */
typedef void (*MSG_CB)(uint32_t msg_no);

/**
 * @}
 */



/* Public Functions ----------------------------------------------------------- */
/** @defgroup CAN_Public_Functions CAN Public Functions
 * @{
 */

void CAN_IRQHandler (void);
void CAN_Init( uint32_t BitClk, CCAN_CLKDIV_Type ClkDiv , MSG_CB Tx_cb, MSG_CB Rx_cb);

void CAN_ConfigureRxMessageObjects( void );
void CAN_RxInt_MessageProcess( uint8_t MsgObjNo );
void CAN_TxInt_MessageProcess( uint8_t MsgObjNo );

void CAN_Send(uint8_t msg_no, uint32_t *msg_ptr );
void CAN_Recv(uint8_t msg_no, uint32_t *msg_ptr, Bool RemoteEnable);
void CAN_ReadMsg(uint32_t msg_no, message_object* buff);
/**
 * @}
 */

#ifdef __cplusplus
}
#endif


#endif /* __LPC18XX_CAN_H */

/**
 * @}
 */
/*****************************************************************************
**                            End Of File
******************************************************************************/

