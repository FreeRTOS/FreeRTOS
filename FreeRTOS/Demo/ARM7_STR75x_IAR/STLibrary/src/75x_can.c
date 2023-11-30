/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_can.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the CAN software functions.
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

/* Includes ------------------------------------------------------------------*/
#include "75x_can.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/
/* Macro Name     : xxx_ID_MSK, xxx_ID_ARB                                    */
/* Description    : Form the Mask and Arbitration registers value to filter   */
/*                  a range of identifiers or a fixed identifier, for standard*/
/*                  and extended IDs                                          */
/*----------------------------------------------------------------------------*/
#define RANGE_ID_MSK(range_start, range_end)	(~((range_end) - (range_start)))
#define RANGE_ID_ARB(range_start, range_end)	((range_start) & (range_end))

#define FIXED_ID_MSK(id)	RANGE_ID_MSK((id), (id))
#define FIXED_ID_ARB(id)	RANGE_ID_ARB((id), (id))

#define STD_RANGE_ID_MSK(range_start, range_end)	((u16)((RANGE_ID_MSK((range_start), (range_end)) & 0x7FF) << 2))
#define STD_RANGE_ID_ARB(range_start, range_end)	((u16)(RANGE_ID_ARB((range_start), (range_end)) << 2))

#define STD_FIXED_ID_MSK(id)	((u16)((FIXED_ID_MSK(id) & 0x7FF) << 2))
#define STD_FIXED_ID_ARB(id)	((u16)(FIXED_ID_ARB(id) << 2))

#define EXT_RANGE_ID_MSK_L(range_start, range_end)	((u16)(RANGE_ID_MSK((range_start), (range_end)) >> 11))
#define EXT_RANGE_ID_MSK_H(range_start, range_end)	((u16)(STD_RANGE_ID_MSK((range_start), (range_end)) | ((RANGE_ID_MSK((range_start), (range_end)) >> 27) & 0x03)))
#define EXT_RANGE_ID_ARB_L(range_start, range_end)	((u16)(RANGE_ID_ARB((range_start), (range_end)) >> 11))
#define EXT_RANGE_ID_ARB_H(range_start, range_end)	((u16)(STD_RANGE_ID_ARB((range_start), (range_end)) | ((RANGE_ID_ARB((range_start), (range_end)) >> 27) & 0x03)))

#define EXT_FIXED_ID_MSK_L(id)	((u16)(FIXED_ID_MSK(id) >> 11))
#define EXT_FIXED_ID_MSK_H(id)	((u16)(STD_FIXED_ID_MSK(id) | ((FIXED_ID_MSK(id) >> 27) & 0x03)))
#define EXT_FIXED_ID_ARB_L(id)	((u16)(FIXED_ID_ARB(id) >> 11))
#define EXT_FIXED_ID_ARB_H(id)	((u16)(STD_FIXED_ID_ARB(id) | ((FIXED_ID_ARB(id) >> 27) & 0x03)))

/* macro to format the timing register value from the timing parameters*/
#define CAN_TIMING(tseg1, tseg2, sjw, brp)	((((tseg2-1) & 0x07) << 12) | (((tseg1-1) & 0x0F) << 8) | (((sjw-1) & 0x03) << 6) | ((brp-1) & 0x3F))

/* Private variables ---------------------------------------------------------*/
/* array of pre-defined timing parameters for standard bitrates*/
u16 CanTimings[] = {       /* value   bitrate     NTQ  TSEG1  TSEG2  SJW  BRP */
  CAN_TIMING(11, 4, 4, 5), /* 0x3AC4  100 kbit/s  16   11     4      4    5   */
  CAN_TIMING(11, 4, 4, 4), /* 0x3AC3  125 kbit/s  16   11     4      4    4   */
  CAN_TIMING( 4, 3, 3, 4), /* 0x2383  250 kbit/s   8    4     3      3    4   */
  CAN_TIMING(13, 2, 1, 1), /* 0x1C00  500 kbit/s  16   13     2      1    1   */
  CAN_TIMING( 4, 3, 1, 1), /* 0x2300  1 Mbit/s     8    4     3      1    1   */
};

/* Private function prototypes -----------------------------------------------*/
static u32 GetFreeIF(void);
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : CAN_DeInit                                                
* Description    : Deinitializes the CAN peripheral registers to their default     
*                  reset values.                                     
* Input          : None                                                      
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void CAN_DeInit (void)
{
  /* Reset the CAN registers values*/
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_CAN,ENABLE);
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_CAN,DISABLE);
}

/*******************************************************************************
* Function Name  : CAN_Init                                                  
* Description    : Initializes the CAN peripheral according to the specified 
*                  parameters in the CAN_InitStruct.                                            
* Input          : CAN_InitStruct: pointer to a CAN_InitTypeDef structure that
*                  contains the configuration information for the CAN peripheral. 
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void CAN_Init(CAN_InitTypeDef* CAN_InitStruct)
{
  CAN_EnterInitMode(CAN_CR_CCE | CAN_InitStruct->CAN_ConfigParameters);
  CAN_SetBitrate(CAN_InitStruct->CAN_Bitrate);
  CAN_LeaveInitMode();
  CAN_LeaveTestMode();
}

/*******************************************************************************
* Function Name  : CAN_StructInit		                        
* Description    : Fills each CAN_InitStruct member with its reset value.	      
* Input          : CAN_InitStruct : pointer to a CAN_InitTypeDef structure which       
*                  will be initialized. 
* Output         : None                  
* Return         : None.						      
*******************************************************************************/
void CAN_StructInit(CAN_InitTypeDef* CAN_InitStruct)
{
/* Reset CAN init structure parameters values */
  CAN_InitStruct->CAN_ConfigParameters = 0x0;
  CAN_InitStruct->CAN_Bitrate = 0x2301;
}

/*******************************************************************************
* Function Name  : CAN_SetBitrate                                            
* Description    : Setups a standard CAN bitrate.                              
* Input          : bitrate: specifies the bit rate.                       
* Output         : None                                                      
* Return         : None                                                                         
*******************************************************************************/
void CAN_SetBitrate(u32 bitrate)
{
  CAN->BTR = CanTimings[bitrate];  /* write the predefined timing value */
  CAN->BRPR = 0; 		     /* clear the Extended Baud Rate Prescaler */
}

/*******************************************************************************
* Function Name  : CAN_SetTiming                                             
* Description    : Setups the CAN timing with specific parameters             
* Input          : - tseg1: specifies Time Segment before the sample point.
*                    This parameter must be a number between 1 and 16.       
*                  - tseg2: Time Segment after the sample point. This parameter 
*                    must be a number between 1 and 8.        
*                  - sjw: Synchronisation Jump Width. This parameter must be                 
*                     a number between 1 and 4.
*                  - brp: Baud Rate Prescaler. This parameter must be a number
*                    between 1 and 1024.                                         
* Output         : None                                                      
* Return         : None                                                                       
*******************************************************************************/
void CAN_SetTiming(u32 tseg1, u32 tseg2, u32 sjw, u32 brp)
{
  CAN->BTR = CAN_TIMING(tseg1, tseg2, sjw, brp);
  CAN->BRPR = ((brp-1) >> 6) & 0x0F;
}

/*******************************************************************************
* Function Name  : GetFreeIF                                             
* Description    : Searchs the first free message interface, starting from 0.  
* Input          : None                                                      
* Output         : None                                                      
* Return         : A free message interface number (0 or 1) if found, else 2 
*******************************************************************************/
static u32 GetFreeIF(void)
{
  if ((CAN->sMsgObj[0].CRR & CAN_CRR_BUSY) == 0)
    return 0;
  else if ((CAN->sMsgObj[1].CRR & CAN_CRR_BUSY) == 0)
    return 1;
  else
   return 2;
}

/*******************************************************************************
* Function Name  : CAN_SetUnusedMsgObj                                       
* Description    : Configures the message object as unused                   
* Input          : msgobj: specifies the Message object number, from 0 to 31.                      
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Interface to treat the message
*                         - ERROR: No interface found to treat the message
*******************************************************************************/
ErrorStatus CAN_SetUnusedMsgObj(u32 msgobj)
{
  u32 msg_if=0;

  if ((msg_if = GetFreeIF()) == 2)
  {
    return ERROR;
  }

  CAN->sMsgObj[msg_if].CMR = CAN_CMR_WRRD
                           | CAN_CMR_MASK
                           | CAN_CMR_ARB
                           | CAN_CMR_CONTROL
                           | CAN_CMR_DATAA
                           | CAN_CMR_DATAB;

  CAN->sMsgObj[msg_if].M1R = 0;
  CAN->sMsgObj[msg_if].M2R = 0;

  CAN->sMsgObj[msg_if].A1R = 0;
  CAN->sMsgObj[msg_if].A2R = 0;

  CAN->sMsgObj[msg_if].MCR = 0;

  CAN->sMsgObj[msg_if].DA1R = 0;
  CAN->sMsgObj[msg_if].DA2R = 0;
  CAN->sMsgObj[msg_if].DB1R = 0;
  CAN->sMsgObj[msg_if].DB2R = 0;

 CAN->sMsgObj[msg_if].CRR = 1 + msgobj;
 
 return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_SetTxMsgObj                                           
* Description    : Configures the message object as TX.                        
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                      
*                  - idType: specifies the identifier type of the frames that
*                    will be transmitted using this message object.
*                    This parameter can be one of the following values:
*                          - CAN_STD_ID (standard ID, 11-bit)
*                          - CAN_EXT_ID (extended ID, 29-bit)                                
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Interface to treat the message
*                         - ERROR: No interface found to treat the message
*******************************************************************************/
ErrorStatus CAN_SetTxMsgObj(u32 msgobj, u32 idType)
{
  u32 msg_if=0;

  if ((msg_if = GetFreeIF()) == 2)
  {
    return ERROR;
  }
  
  CAN->sMsgObj[msg_if].CMR = CAN_CMR_WRRD
                           | CAN_CMR_MASK
                           | CAN_CMR_ARB
                           | CAN_CMR_CONTROL
                           | CAN_CMR_DATAA
                           | CAN_CMR_DATAB;

  CAN->sMsgObj[msg_if].M1R = 0;
  CAN->sMsgObj[msg_if].A1R = 0;

  if (idType == CAN_STD_ID)
  {
    CAN->sMsgObj[msg_if].M2R = CAN_M2R_MDIR;
    CAN->sMsgObj[msg_if].A2R = CAN_A2R_MSGVAL | CAN_A2R_DIR;
  }
  else
  {
    CAN->sMsgObj[msg_if].M2R = CAN_M2R_MDIR | CAN_M2R_MXTD;
    CAN->sMsgObj[msg_if].A2R = CAN_A2R_MSGVAL | CAN_A2R_DIR | CAN_A2R_XTD;
  }

  CAN->sMsgObj[msg_if].MCR = CAN_MCR_TXIE | CAN_MCR_EOB;

  CAN->sMsgObj[msg_if].DA1R = 0;
  CAN->sMsgObj[msg_if].DA2R = 0;
  CAN->sMsgObj[msg_if].DB1R = 0;
  CAN->sMsgObj[msg_if].DB2R = 0;

  CAN->sMsgObj[msg_if].CRR = 1 + msgobj;
  
  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_SetRxMsgObj                                           
* Description    : Configures the message object as RX.                        
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                    
*                  - idType: specifies the identifier type of the frames that
*                    will be transmitted using this message object.
*                    This parameter can be one of the following values:
*                          - CAN_STD_ID (standard ID, 11-bit)
*                          - CAN_EXT_ID (extended ID, 29-bit)                               
*                  - idLow: specifies the low part of the identifier range used      
*                    for acceptance filtering.
*                  - idHigh: specifies the high part of the identifier range    
*                    used for acceptance filtering.
*                  - singleOrFifoLast: specifies the end-of-buffer indicator.
*                    This parameter can be one of the following values:
*                          - TRUE: for a single receive object or a FIFO receive
*                            object that is the last one of the FIFO. 
*                          - FALSE: for a FIFO receive object that is not the 
*                            last one. 
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Interface to treat the message
*                         - ERROR: No interface found to treat the message
*******************************************************************************/
ErrorStatus CAN_SetRxMsgObj(u32 msgobj, u32 idType, u32 idLow, u32 idHigh, bool singleOrFifoLast)
{
  u32 msg_if=0;

  if ((msg_if = GetFreeIF()) == 2)
  {
    return ERROR;
  }
  
  CAN->sMsgObj[msg_if].CMR = CAN_CMR_WRRD
                           | CAN_CMR_MASK
                           | CAN_CMR_ARB
                           | CAN_CMR_CONTROL
                           | CAN_CMR_DATAA
                           | CAN_CMR_DATAB;

  if (idType == CAN_STD_ID)
  {
    CAN->sMsgObj[msg_if].M1R = 0;
    CAN->sMsgObj[msg_if].M2R = STD_RANGE_ID_MSK(idLow, idHigh);

    CAN->sMsgObj[msg_if].A1R = 0;
    CAN->sMsgObj[msg_if].A2R = CAN_A2R_MSGVAL | STD_RANGE_ID_ARB(idLow, idHigh);
  }
  else
  {
    CAN->sMsgObj[msg_if].M1R = EXT_RANGE_ID_MSK_L(idLow, idHigh);
    CAN->sMsgObj[msg_if].M2R = CAN_M2R_MXTD | EXT_RANGE_ID_MSK_H(idLow, idHigh);

    CAN->sMsgObj[msg_if].A1R = EXT_RANGE_ID_ARB_L(idLow, idHigh);
    CAN->sMsgObj[msg_if].A2R = CAN_A2R_MSGVAL | CAN_A2R_XTD | EXT_RANGE_ID_ARB_H(idLow, idHigh);
  }

  CAN->sMsgObj[msg_if].MCR = CAN_MCR_RXIE | CAN_MCR_UMASK | (singleOrFifoLast ? CAN_MCR_EOB : 0);

  CAN->sMsgObj[msg_if].DA1R = 0;
  CAN->sMsgObj[msg_if].DA2R = 0;
  CAN->sMsgObj[msg_if].DB1R = 0;
  CAN->sMsgObj[msg_if].DB2R = 0;

  CAN->sMsgObj[msg_if].CRR = 1 + msgobj;
  
  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_InvalidateAllMsgObj				      
* Description    : Configures all the message objects as unused.               
* Input          : None                                                      
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void CAN_InvalidateAllMsgObj(void)
{
  u32 i=0;
  for (i = 0; i < 32; i++)
    CAN_SetUnusedMsgObj(i);
}


/*******************************************************************************
* Function Name  : CAN_ReleaseMessage					      
* Description    : Releases the message object                                
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                     
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Interface to treat the message
*                         - ERROR: No interface found to treat the message
*******************************************************************************/
ErrorStatus CAN_ReleaseMessage(u32 msgobj)
{
  u32 msg_if=0;

  if ((msg_if = GetFreeIF()) == 2)
  {
    return ERROR;
  }

  CAN->sMsgObj[msg_if].CMR = CAN_CMR_CLRINTPND | CAN_CMR_TXRQSTNEWDAT;
  CAN->sMsgObj[msg_if].CRR = 1 + msgobj;
  
  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_SendMessage                                           
* Description    : Start transmission of a message                           
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                    
*                : - pCanMsg: pointer to the message structure containing data     
*                    to transmit.
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Transmission OK
*                         - ERROR: No transmission
*******************************************************************************/
ErrorStatus CAN_SendMessage(u32 msgobj, canmsg* pCanMsg)
{
  if (CAN->sMsgObj[0].CRR & CAN_CRR_BUSY)
  {
    return ERROR;                    
  }

  CAN->SR &= ~CAN_SR_TXOK;

  /* read the Arbitration and Message Control*/
  CAN->sMsgObj[0].CMR = CAN_CMR_ARB | CAN_CMR_CONTROL;

  CAN->sMsgObj[0].CRR = 1 + msgobj;

  if (CAN->sMsgObj[0].CRR & CAN_CRR_BUSY)
  {
    return ERROR;                    
  }

  /* update the contents needed for transmission*/
  CAN->sMsgObj[0].CMR = CAN_CMR_WRRD
                      | CAN_CMR_ARB
                      | CAN_CMR_CONTROL
                      | CAN_CMR_DATAA
                      | CAN_CMR_DATAB;

  if ((CAN->sMsgObj[0].A2R & CAN_A2R_XTD) == 0)
  {
    /* standard ID*/
    CAN->sMsgObj[0].A1R = 0;
    CAN->sMsgObj[0].A2R = (CAN->sMsgObj[0].A2R & 0xE000) | STD_FIXED_ID_ARB(pCanMsg->Id);
  }
  else
  {
    /* extended ID*/
    CAN->sMsgObj[0].A1R = EXT_FIXED_ID_ARB_L(pCanMsg->Id);
    CAN->sMsgObj[0].A2R = (CAN->sMsgObj[0].A2R & 0xE000) | EXT_FIXED_ID_ARB_H(pCanMsg->Id);
  }

  CAN->sMsgObj[0].MCR = (CAN->sMsgObj[0].MCR & 0xFEF0) | CAN_MCR_NEWDAT | CAN_MCR_TXRQST | pCanMsg->Dlc;

  CAN->sMsgObj[0].DA1R = ((u16)pCanMsg->Data[1]<<8) | pCanMsg->Data[0];
  CAN->sMsgObj[0].DA2R = ((u16)pCanMsg->Data[3]<<8) | pCanMsg->Data[2];
  CAN->sMsgObj[0].DB1R = ((u16)pCanMsg->Data[5]<<8) | pCanMsg->Data[4];
  CAN->sMsgObj[0].DB2R = ((u16)pCanMsg->Data[7]<<8) | pCanMsg->Data[6];

  CAN->sMsgObj[0].CRR = 1 + msgobj;

  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_ReceiveMessage                                        
* Description    : Gets the message, if received.
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                     
*                  - release: specifies the message release indicator.
*                    This parameter can be one of the following values:
*                          - TRUE: the message object is released when getting  
*                            the data.
*                          - FALSE: the message object is not released.
*                  - pCanMsg: pointer to the message structure where received   
*                    data is copied.
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Reception OK
*                         - ERROR: No message pending
*******************************************************************************/
ErrorStatus CAN_ReceiveMessage(u32 msgobj, bool release, canmsg* pCanMsg)
{
  if (!CAN_IsMessageWaiting(msgobj))
  {
    return ERROR;
  }

  CAN->SR &= ~CAN_SR_RXOK;

  /* read the message contents*/
  CAN->sMsgObj[1].CMR = CAN_CMR_MASK
                      | CAN_CMR_ARB
                      | CAN_CMR_CONTROL
                      | CAN_CMR_CLRINTPND
                      | (release ? CAN_CMR_TXRQSTNEWDAT : 0)
                      | CAN_CMR_DATAA
                      | CAN_CMR_DATAB;

  CAN->sMsgObj[1].CRR = 1 + msgobj;

  if (CAN->sMsgObj[1].CRR & CAN_CRR_BUSY)
  {
    return ERROR;                    
  }
  
  if ((CAN->sMsgObj[1].A2R & CAN_A2R_XTD) == 0)
  {
    /* standard ID*/
    pCanMsg->IdType = CAN_STD_ID;
    pCanMsg->Id = (CAN->sMsgObj[1].A2R >> 2) & 0x07FF;
  }
  else
  {
    /* extended ID*/
    pCanMsg->IdType = CAN_EXT_ID;
    pCanMsg->Id  = ((CAN->sMsgObj[1].A2R >> 2) & 0x07FF); 
    pCanMsg->Id |= ((u32)CAN->sMsgObj[1].A1R << 11);
    pCanMsg->Id |= (((u32)CAN->sMsgObj[1].A2R & 0x0003) << 27);
  }

  pCanMsg->Dlc = CAN->sMsgObj[1].MCR & 0x0F;

  pCanMsg->Data[0] = (u8) CAN->sMsgObj[1].DA1R;
  pCanMsg->Data[1] = (u8)(CAN->sMsgObj[1].DA1R >> 8);
  pCanMsg->Data[2] = (u8) CAN->sMsgObj[1].DA2R;
  pCanMsg->Data[3] = (u8)(CAN->sMsgObj[1].DA2R >> 8);
  pCanMsg->Data[4] = (u8) CAN->sMsgObj[1].DB1R;
  pCanMsg->Data[5] = (u8)(CAN->sMsgObj[1].DB1R >> 8);
  pCanMsg->Data[6] = (u8) CAN->sMsgObj[1].DB2R;
  pCanMsg->Data[7] = (u8)(CAN->sMsgObj[1].DB2R >> 8);

  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_WaitEndOfTx                                           
* Description    : Waits until current transmission is finished.               
* Input          : None                                                      
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Transmission ended
*                         - ERROR: Transmission did not occur yet
*******************************************************************************/
ErrorStatus CAN_WaitEndOfTx(void)
{
  if ((CAN->SR & CAN_SR_TXOK) == 0)
  {
    return ERROR;
  }
  CAN->SR &= ~CAN_SR_TXOK;
  
  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_BasicSendMessage                                      
* Description    : Starts transmission of a message in BASIC mode. This mode 
*                  does not use the message RAM.             
* Input          : pCanMsg: Pointer to the message structure containing data to       
*                  transmit.                                                  
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Transmission OK
*                         - ERROR: No transmission
*******************************************************************************/
ErrorStatus CAN_BasicSendMessage(canmsg* pCanMsg)
{
  /* clear NewDat bit in IF2 to detect next reception*/
  CAN->sMsgObj[1].MCR &= ~CAN_MCR_NEWDAT;

  CAN->SR &= ~CAN_SR_TXOK;
  CAN->sMsgObj[0].CMR = CAN_CMR_WRRD
                      | CAN_CMR_ARB
                      | CAN_CMR_CONTROL
                      | CAN_CMR_DATAA
                      | CAN_CMR_DATAB;

  if (pCanMsg->IdType == CAN_STD_ID)
  {
    /* standard ID*/
    CAN->sMsgObj[0].A1R = 0;
    CAN->sMsgObj[0].A2R = (CAN->sMsgObj[0].A2R & 0xE000) | STD_FIXED_ID_ARB(pCanMsg->Id);
  }
  else
  {
    /* extended ID*/
    CAN->sMsgObj[0].A1R = EXT_FIXED_ID_ARB_L(pCanMsg->Id);
    CAN->sMsgObj[0].A2R = ((CAN->sMsgObj[0].A2R) & 0xE000) | EXT_FIXED_ID_ARB_H(pCanMsg->Id);
  }

  CAN->sMsgObj[0].MCR = (CAN->sMsgObj[0].MCR & 0xFCF0) | pCanMsg->Dlc;

  CAN->sMsgObj[0].DA1R = ((u16)pCanMsg->Data[1]<<8) | pCanMsg->Data[0];
  CAN->sMsgObj[0].DA2R = ((u16)pCanMsg->Data[3]<<8) | pCanMsg->Data[2];
  CAN->sMsgObj[0].DB1R = ((u16)pCanMsg->Data[5]<<8) | pCanMsg->Data[4];
  CAN->sMsgObj[0].DB2R = ((u16)pCanMsg->Data[7]<<8) | pCanMsg->Data[6];

  /* request transmission*/
  if (CAN->sMsgObj[0].CRR == CAN_CRR_BUSY )
  {
    return ERROR;
  }

  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_BasicReceiveMessage                                   
* Description    : Gets the message in BASIC mode, if received. This mode does
*                  not use the message RAM.                
* Input          : pCanMsg: pointer to the message structure where message is copied.    
* Output         : None                                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Reception OK
*                         - ERROR: No message pending
*******************************************************************************/
ErrorStatus CAN_BasicReceiveMessage(canmsg* pCanMsg)
{
  if ((CAN->sMsgObj[1].MCR & CAN_MCR_NEWDAT) == 0)
  {
    return ERROR;
  }

  CAN->SR &= ~CAN_SR_RXOK;

  CAN->sMsgObj[1].CMR = CAN_CMR_ARB
                      | CAN_CMR_CONTROL
                      | CAN_CMR_DATAA
                      | CAN_CMR_DATAB;

  if ((CAN->sMsgObj[1].A2R & CAN_A2R_XTD) == 0)
  {
    /* standard ID*/
    pCanMsg->IdType = CAN_STD_ID;
    pCanMsg->Id = (CAN->sMsgObj[1].A2R >> 2) & 0x07FF;
  }
  else
  {
    /* extended ID*/
    pCanMsg->IdType = CAN_EXT_ID;
    pCanMsg->Id  = ((CAN->sMsgObj[1].A2R >> 2) & 0x07FF);
    pCanMsg->Id |= ((u32)CAN->sMsgObj[1].A1R << 11);
    pCanMsg->Id |= (((u32)CAN->sMsgObj[1].A2R & 0x0003) << 27);
  }

  pCanMsg->Dlc = CAN->sMsgObj[1].MCR & 0x0F;

  pCanMsg->Data[0] = (u8) CAN->sMsgObj[1].DA1R;
  pCanMsg->Data[1] = (u8)(CAN->sMsgObj[1].DA1R >> 8);
  pCanMsg->Data[2] = (u8) CAN->sMsgObj[1].DA2R;
  pCanMsg->Data[3] = (u8)(CAN->sMsgObj[1].DA2R >> 8);
  pCanMsg->Data[4] = (u8) CAN->sMsgObj[1].DB1R;
  pCanMsg->Data[5] = (u8)(CAN->sMsgObj[1].DB1R >> 8);
  pCanMsg->Data[6] = (u8) CAN->sMsgObj[1].DB2R;
  pCanMsg->Data[7] = (u8)(CAN->sMsgObj[1].DB2R >> 8);

  return SUCCESS;
}

/*******************************************************************************
* Function Name  : CAN_EnterInitMode                                         
* Description    : Switchs the CAN into initialization mode. This function must
*                  be used in conjunction with CAN_LeaveInitMode().                 
* Input          : InitMask: specifies the CAN configuration in normal mode.      
* Output         : None                                                      
* Return         : None                                                          
*******************************************************************************/
void CAN_EnterInitMode(u8 InitMask)
{
  CAN->CR = InitMask | CAN_CR_INIT;
  CAN->SR = 0;					/* reset the status*/
}

/*******************************************************************************
* Function Name  : CAN_LeaveInitMode                                         
* Description    : Leaves the initialization mode (switch into normal mode).
*                  This function must be used in conjunction with CAN_EnterInitMode().  
* Input          : None                                                      
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void CAN_LeaveInitMode(void)
{
  CAN->CR &= ~(CAN_CR_INIT | CAN_CR_CCE);
}

/*******************************************************************************
* Function Name  : CAN_EnterTestMode                                         
* Description    : Switchs the CAN into test mode. This function must be used in
*                  conjunction with CAN_LeaveTestMode().                            
* Input          : TestMask: specifies the configuration in test modes.     
* Output         : None                                                      
* Return         : None                                                            
*******************************************************************************/
void CAN_EnterTestMode(u8 TestMask)
{
  CAN->CR |= CAN_CR_TEST;
  CAN->TESTR |= TestMask;
}

/*******************************************************************************
* Function Name  : CAN_LeaveTestMode                                         
* Description    : Leaves the current test mode (switch into normal mode).
*                  This function must be used in conjunction with CAN_EnterTestMode().    
* Input          : None                                                      
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void CAN_LeaveTestMode(void)
{
  CAN->CR |= CAN_CR_TEST;
  CAN->TESTR &= ~(CAN_TESTR_LBACK | CAN_TESTR_SILENT | CAN_TESTR_BASIC);
  CAN->CR &= ~CAN_CR_TEST;
}

/*******************************************************************************
* Function Name  : CAN_ReleaseTxMessage                                      
* Description    : Releases the transmit message object.
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                     
* Output         : None                                                      
* Return         : None                                                                        
*******************************************************************************/
void CAN_ReleaseTxMessage(u32 msgobj)
{
  CAN->sMsgObj[0].CMR = CAN_CMR_CLRINTPND | CAN_CMR_TXRQSTNEWDAT;
  CAN->sMsgObj[0].CRR = 1 + msgobj;
}

/*******************************************************************************
* Function Name  : CAN_ReleaseRxMessage                                      
* Description    : Releases the receive message object.                        
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                      
* Output         : None                                                      
* Return         : None                                                                      
*******************************************************************************/
void CAN_ReleaseRxMessage(u32 msgobj)
{
  CAN->sMsgObj[1].CMR = CAN_CMR_CLRINTPND | CAN_CMR_TXRQSTNEWDAT;
  CAN->sMsgObj[1].CRR = 1 + msgobj;
}

/*******************************************************************************
* Function Name  : CAN_IsMessageWaiting                                      
* Description    : Tests the waiting status of a received message.             
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                       
* Output         : None                                                      
* Return         : A non-zero value if the corresponding message object has  
*                  received a message waiting to be copied, else 0.           
*******************************************************************************/
u32 CAN_IsMessageWaiting(u32 msgobj)
{
  return (msgobj < 16 ? CAN->ND1R & (1 << msgobj) : CAN->ND2R & (1 << (msgobj-16)));
}

/*******************************************************************************
* Function Name  : CAN_IsTransmitRequested                                   
* Description    : Tests the request status of a transmitted message.          
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                      
* Output         : None                                                      
* Return         : A non-zero value if the corresponding message is requested
*                  to transmit, else 0.                                       
*******************************************************************************/
u32 CAN_IsTransmitRequested(u32 msgobj)
{
  return (msgobj < 16 ? CAN->TXR1R & (1 << msgobj) : CAN->TXR2R & (1 << (msgobj-16)));
}

/*******************************************************************************
* Function Name  : CAN_IsInterruptPending                                    
* Description    : Tests the interrupt status of a message object.             
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                      
* Output         : None                                                      
* Return         : A non-zero value if the corresponding message has an      
*                  interrupt pending, else 0.                                 
*******************************************************************************/
u32 CAN_IsInterruptPending(u32 msgobj)
{
  return (msgobj < 16 ? CAN->IP1R & (1 << msgobj) : CAN->IP2R & (1 << (msgobj-16)));
}

/*******************************************************************************
* Function Name  : CAN_IsObjectValid                                         
* Description    : Tests the validity of a message object (ready to use).      
* Input          : - msgobj: specifies the Message object number, from 0 to 31.                      
* Output         : None                                                      
* Return         : A non-zero value if the corresponding message object is   
*                  valid, else 0.                                             
*******************************************************************************/
u32 CAN_IsObjectValid(u32 msgobj)
{
  return (msgobj < 16 ? CAN->MV1R & (1 << msgobj) : CAN->MV2R & (1 << (msgobj-16)));
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
