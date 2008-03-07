/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_smi.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      SMI software library.
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
#ifndef __75x_SMI_H
#define __75x_SMI_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
typedef struct
{
  u8 SMI_ClockHold;
  u8 SMI_Prescaler;
  u8 SMI_DeselectTime;
} SMI_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* SMI mode */
#define SMI_Mode_HW    0xEFFFFFFF
#define SMI_Mode_SW    0x10000000

/* Reception Length */
#define SMI_RxLength_0Bytes    0x00000000
#define SMI_RxLength_1Byte     0x00000010
#define SMI_RxLength_2Bytes    0x00000020
#define SMI_RxLength_3Bytes    0x00000030
#define SMI_RxLength_4Bytes    0x00000040

/* Transmission Length */
#define SMI_TxLength_0Bytes    0x00000000
#define SMI_TxLength_1Byte     0x00000001
#define SMI_TxLength_2Bytes    0x00000002
#define SMI_TxLength_3Bytes    0x00000003
#define SMI_TxLength_4Bytes    0x00000004

/* SMI memory Banks */
#define SMI_Bank_0    0x00000001
#define SMI_Bank_1    0x00000002
#define SMI_Bank_2    0x00000004
#define SMI_Bank_3    0x00000008

/* SMI Interrupts */
#define SMI_IT_WC    0x00000200
#define SMI_IT_TF    0x00000100

/* Fast Read Mode */
#define SMI_FastRead_Disable    0xFFFF7FFF
#define SMI_FastRead_Enable     0x00008000

/* Write Burst Mode */
#define SMI_WriteBurst_Disable    0xDFFFFFFF
#define SMI_WriteBurst_Enable     0x20000000

/* SMI Flags */
#define SMI_FLAG_Bank3_WM    0x00008000
#define SMI_FLAG_Bank2_WM    0x00004000
#define SMI_FLAG_Bank1_WM    0x00002000
#define SMI_FLAG_Bank0_WM    0x00001000
#define SMI_FLAG_ERF2        0x00000800
#define SMI_FLAG_ERF1        0x00000400
#define SMI_FLAG_WC          0x00000200
#define SMI_FLAG_TF          0x00000100

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void SMI_DeInit(void); 
void SMI_Init(SMI_InitTypeDef* SMI_InitStruct); 
void SMI_StructInit(SMI_InitTypeDef* SMI_InitStruct);
void SMI_ModeConfig(u32 SMI_Mode);
void SMI_TxRxLengthConfig(u32 SMI_TxLength, u32 SMI_RxLength); 
void SMI_BankCmd(u32 SMI_Bank, FunctionalState NewState); 
void SMI_ITConfig(u32 SMI_IT, FunctionalState NewState); 
void SMI_SelectBank(u32 SMI_Bank); 
void SMI_SendWENCmd(void); 
void SMI_SendRSRCmd(void);
void SMI_SendCmd(u32 Command);
void SMI_FastReadConfig(u32 SMI_FastRead);
void SMI_WriteBurstConfig(u32 SMI_WriteBurst);
void SMI_WriteByte(u32 WriteAddr, u8 Data);
void SMI_WriteHalfWord(u32 WriteAddr, u16 Data);
void SMI_WriteWord(u32 WriteAddr, u32 Data);
u8 SMI_ReadByte(u32 ReadAddr);
u16 SMI_ReadHalfWord(u32 ReadAddr);
u32 SMI_ReadWord(u32 ReadAddr);
u8 SMI_ReadMemoryStatusRegister(void);
FlagStatus SMI_GetFlagStatus(u32 SMI_FLAG);
void SMI_ClearFlag(u32 SMI_FLAG);
ITStatus SMI_GetITStatus(u32 SMI_IT);
void SMI_ClearITPendingBit(u32 SMI_IT);

#endif /* __75x_SMI_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
