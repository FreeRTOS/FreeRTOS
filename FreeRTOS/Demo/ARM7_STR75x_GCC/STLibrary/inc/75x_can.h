/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_can.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      CAN bus software library.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __75x_CAN_H
#define __75x_CAN_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/

/* CAN Init structure define */
typedef struct
{
  u8  CAN_ConfigParameters;
  u32 CAN_Bitrate;
}CAN_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* Standard bitrates available*/
enum
{
  CAN_BITRATE_100K,
  CAN_BITRATE_125K,
  CAN_BITRATE_250K,
  CAN_BITRATE_500K,
  CAN_BITRATE_1M
};

/* Control register*/
#define CAN_CR_TEST            0x0080
#define CAN_CR_CCE             0x0040
#define CAN_CR_DAR             0x0020
#define CAN_CR_EIE             0x0008
#define CAN_CR_SIE             0x0004
#define CAN_CR_IE              0x0002
#define CAN_CR_INIT            0x0001

/* Status register */
#define CAN_SR_BOFF            0x0080
#define CAN_SR_EWARN           0x0040
#define CAN_SR_EPASS           0x0020
#define CAN_SR_RXOK            0x0010
#define CAN_SR_TXOK            0x0008
#define CAN_SR_LEC             0x0007

/* Test register*/
#define CAN_TESTR_RX           0x0080
#define CAN_TESTR_TX1          0x0040
#define CAN_TESTR_TX0          0x0020
#define CAN_TESTR_LBACK        0x0010
#define CAN_TESTR_SILENT       0x0008
#define CAN_TESTR_BASIC        0x0004

/* IFn / Command Request register*/
#define CAN_CRR_BUSY           0x8000

/* IFn / Command Mask register*/
#define CAN_CMR_WRRD           0x0080
#define CAN_CMR_MASK           0x0040
#define CAN_CMR_ARB            0x0020
#define CAN_CMR_CONTROL        0x0010
#define CAN_CMR_CLRINTPND      0x0008
#define CAN_CMR_TXRQSTNEWDAT   0x0004
#define CAN_CMR_DATAA          0x0002
#define CAN_CMR_DATAB          0x0001

/* IFn / Mask 2 register*/
#define CAN_M2R_MXTD           0x8000
#define CAN_M2R_MDIR           0x4000

/* IFn / Arbitration 2 register*/
#define CAN_A2R_MSGVAL         0x8000
#define CAN_A2R_XTD            0x4000
#define CAN_A2R_DIR            0x2000

/* IFn / Message Control register*/
#define CAN_MCR_NEWDAT         0x8000
#define CAN_MCR_MSGLST         0x4000
#define CAN_MCR_INTPND         0x2000
#define CAN_MCR_UMASK          0x1000
#define CAN_MCR_TXIE           0x0800
#define CAN_MCR_RXIE           0x0400
#define CAN_MCR_RMTEN          0x0200
#define CAN_MCR_TXRQST         0x0100
#define CAN_MCR_EOB            0x0080


/* Wake-up modes*/
enum
{
  CAN_WAKEUP_ON_EXT,
  CAN_WAKEUP_ON_CAN
};


/* CAN message structure*/
typedef struct
{
  u32 IdType;
  u32 Id;
  u8 Dlc;
  u8 Data[8];
} canmsg;

/* Message ID types*/
enum
{
  CAN_STD_ID,
  CAN_EXT_ID
};

/* Message ID limits*/

#define CAN_LAST_STD_ID	((1<<11) - 1)
#define CAN_LAST_EXT_ID	((1L<<29) - 1)

/* Exported functions ------------------------------------------------------- */

void CAN_Init (CAN_InitTypeDef *CAN_InitStruct);
void CAN_DeInit (void);
void CAN_StructInit(CAN_InitTypeDef *CAN_InitStruct);
void CAN_SetBitrate(u32 bitrate);
void CAN_SetTiming(u32 tseg1, u32 tseg2, u32 sjw, u32 brp);
ErrorStatus CAN_SetUnusedMsgObj(u32 msgobj);
ErrorStatus CAN_SetTxMsgObj(u32 msgobj, u32 idType);
ErrorStatus CAN_SetRxMsgObj(u32 msgobj, u32 idType, u32 idLow, u32 idHigh, bool singleOrFifoLast);
void CAN_InvalidateAllMsgObj(void);
ErrorStatus CAN_ReleaseMessage(u32 msgobj);
ErrorStatus CAN_SendMessage(u32 msgobj, canmsg* pCanMsg);
ErrorStatus CAN_ReceiveMessage(u32 msgobj, bool release, canmsg* pCanMsg);
ErrorStatus CAN_WaitEndOfTx(void);
ErrorStatus CAN_BasicSendMessage(canmsg* pCanMsg);
ErrorStatus CAN_BasicReceiveMessage(canmsg* pCanMsg);
void CAN_EnterTestMode(u8 TestMask);
void CAN_EnterInitMode(u8 InitMask);
void CAN_LeaveInitMode(void);
void CAN_LeaveTestMode(void);
void CAN_ReleaseTxMessage(u32 msgobj);
void CAN_ReleaseRxMessage(u32 msgobj);
u32 CAN_IsMessageWaiting(u32 msgobj);
u32 CAN_IsTransmitRequested(u32 msgobj);
u32 CAN_IsInterruptPending(u32 msgobj);
u32 CAN_IsObjectValid(u32 msgobj);

#endif /* __75x_CAN_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
