/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_smi.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the SMI software functions.
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
#include "75x_smi.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* SMI_CR1 mask bits */
#define SMI_HOLDPRESCTCS_RESET_Mask  0xFF00800F
#define SMI_Prescaler_MaxValue       0x7F
#define SMI_DeselectTime_MaxValue    0x0F
#define SMI_ClockHold_Mask           0x00
#define SMI_Prescaler_Mask           0x02
#define SMI_DeselectTime_Mask        0x5

/* SMI_CR2 mask bits */
#define SMI_BS_RESET_Mask              0xFFFFCFFF
#define SMI_BS_Bank1_Mask              0x00001000
#define SMI_BS_Bank2_Mask              0x00002000
#define SMI_BS_Bank3_Mask              0x00003000
#define SMI_WEN_Mask                   0x00000800
#define SMI_RSR_Mask                   0x00000400
#define SMI_SEND_Mask                  0x00000080
#define SMI_TRARECLENGTH_RESET_Mask    0xFFFFFF88

/* SMI_SR mask bits */
#define SMI_STATUSREGISTER_Mask    0xFF

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : SMI_DeInit
* Description    : Deinitializes the SMI peripheral registers to their default
*                  reset values. This function must not be used when booting
*                  from the SMI external memory.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_DeInit(void)
{
  SMI->CR1 = 0x00000250;
  SMI->CR2 = 0x00;
  SMI->SR &= 0xFFFFF0FF;
  SMI->TR = 0x00;
}

/*******************************************************************************
* Function Name  : SMI_Init
* Description    : Initializes the SMI peripheral according to the specified
*                  parameters in the SMI_InitStruct.
* Input          : - SMI_InitStruct: pointer to a SMI_InitTypeDef structure that
*                    contains the configuration information for the specified
*                    SMI peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_Init(SMI_InitTypeDef* SMI_InitStruct)
{
  u32 Temp = 0;
 
  /* Clear HOLD[7:0], PRESC[6:0] and TCS[3:0] bits */
  Temp = SMI->CR1 & SMI_HOLDPRESCTCS_RESET_Mask;

  /* Set HOLD[7:0] bits according to SMI_ClockHold value */
  Temp |= SMI_InitStruct->SMI_ClockHold << 16;

  if(SMI_InitStruct->SMI_Prescaler <= SMI_Prescaler_MaxValue)
  {
    /* Set PRESC[6:0] bits according to SMI_Prescaler value */
    Temp |= SMI_InitStruct->SMI_Prescaler << 8;
  }

  if(SMI_InitStruct->SMI_DeselectTime <= SMI_DeselectTime_MaxValue)
  {
    /* Set TCS[3:0] bits according to SMI_DeselectTime value */
    Temp |= SMI_InitStruct->SMI_DeselectTime << 4;
  }

  /* Store the new value */
  SMI->CR1 = Temp; 
}

/*******************************************************************************
* Function Name  : SMI_StructInit
* Description    : Fills each SMI_InitStruct member with its reset value.
* Input          : - SMI_InitStruct: pointer to a SMI_InitTypeDef structure which
*                    will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_StructInit(SMI_InitTypeDef* SMI_InitStruct)
{
  /* SMI_CK is sent continuously */
  SMI_InitStruct->SMI_ClockHold = SMI_ClockHold_Mask;
  
  /* SMI_CK = HCLK/2 */
  SMI_InitStruct->SMI_Prescaler = SMI_Prescaler_Mask;
  
  /* Deselect Time set to 6*SMI_CK periods */
  SMI_InitStruct->SMI_DeselectTime = SMI_DeselectTime_Mask;
}

/*******************************************************************************
* Function Name  : SMI_ModeConfig
* Description    : Selects the SMI mode: hardware or software.
* Input          : - SMI_Mode: specifies the SMI mode.
*                    This parameter can be one of the following values:
*                          - SMI_Mode_HW: SMI in hardware mode
*                          - SMI_Mode_SW: SMI in software mode
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_ModeConfig(u32 SMI_Mode)
{
  if(SMI_Mode == SMI_Mode_SW)
  {   
    SMI->CR1 |= SMI_Mode_SW;
  }
  else
  {
    SMI->CR1 &= SMI_Mode_HW;
  }
}

/*******************************************************************************
* Function Name  : SMI_TxRxLengthConfig
* Description    : Configures the number of bytes to be transmitted and received
*                  to/from external memory. This function is used in Software
*                  mode only.
* Input          : - SMI_TxLength: specifies the number of bytes to be transmitted
*                    to external memory.
*                    This parameter can be one of the following values:
*                          - SMI_TxLength_0Bytes: No bytes transmitted  
*                          - SMI_TxLength_1Byte: 1 byte transmitted
*                          - SMI_TxLength_2Bytes: 2 bytes transmitted
*                          - SMI_TxLength_3Bytes: 3 bytes transmitted
*                          - SMI_TxLength_4Bytes: 4 bytes transmitted
*                  - SMI_RxLength: specifies the number of bytes to be received
*                    from external memory.
*                    This parameter can be one of the following values:
*                          - SMI_RxLength_0Bytes: No bytes received  
*                          - SMI_RxLength_1Byte: 1 byte received
*                          - SMI_RxLength_2Bytes: 2 bytes received
*                          - SMI_RxLength_3Bytes: 3 bytes received
*                          - SMI_RxLength_4Bytes: 4 bytes received
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_TxRxLengthConfig(u32 SMI_TxLength, u32 SMI_RxLength) 
{
  u32 Temp = 0;
 
  /* Clear TRA_LENGTH[2:0] and REC_LENGTH[2:0] bits */
  Temp = SMI->CR2 & SMI_TRARECLENGTH_RESET_Mask;
 
  /* Set TRA_LENGTH[2:0] and REC_LENGTH[2:0] bits according to function parameters */
  Temp |= SMI_TxLength | SMI_RxLength;
 
  /* Store the new value */
  SMI->CR2 = Temp;
}

/*******************************************************************************
* Function Name  : SMI_BankCmd
* Description    : Enables or disables the specified memory Bank.
* Input          : - SMI_Bank: specifies the memory Bank to be enabled or disabled.
*                    This parameter can be any combination of the following values:
*                          - SMI_Bank_0
*                          - SMI_Bank_1
*                          - SMI_Bank_2
*                          - SMI_Bank_3
*                  - NewState: new state of the specified memory Bank.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_BankCmd(u32 SMI_Bank, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    SMI->CR1 |= SMI_Bank;
  }
  else
  {
    SMI->CR1 &= ~SMI_Bank;
  }
}

/*******************************************************************************
* Function Name  : SMI_ITConfig
* Description    : Enables or disables the specified SMI interrupts.
* Input          : - SMI_IT: specifies the SMI interrupts sources to be
*                    enabled or disabled. This parameter can be any combination
*                    of the following values:
*                          - SMI_IT_WC : Write Complete Interrupt
*                          - SMI_IT_TF : Transfer Finished Interrupt
*                  - NewState: new state of the specified SMI interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_ITConfig(u32 SMI_IT, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    SMI->CR2 |= SMI_IT;
  }
  else
  {
    SMI->CR2 &= ~SMI_IT;
  }
}

/*******************************************************************************
* Function Name  : SMI_SelectBank
* Description    : Selects the memory Bank to be accessed. Only one Bank can be
*                  selected at a time.
* Input          : - SMI_Bank: specifies the memory Bank to be selected.
*                    This parameter can be one of the following values:
*                          - SMI_Bank_0
*                          - SMI_Bank_1
*                          - SMI_Bank_2
*                          - SMI_Bank_3
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_SelectBank(u32 SMI_Bank)
{
  /* Clear BS[1:0] bits (Bank0 is selected)*/
  SMI->CR2 &= SMI_BS_RESET_Mask;

  switch(SMI_Bank)
  {
    case SMI_Bank_1:
      /* Select Bank1 */
      SMI->CR2 |= SMI_BS_Bank1_Mask;
      break;

    case SMI_Bank_2:
      /* Select Bank2 */
      SMI->CR2 |= SMI_BS_Bank2_Mask;
      break;

    case SMI_Bank_3:
      /* Select Bank3 */
      SMI->CR2 |= SMI_BS_Bank3_Mask;
      break;
      
    default:
      break;      
  }
}

/*******************************************************************************
* Function Name  : SMI_SendWENCmd
* Description    : Sends a Write Enable command to the selected memory Bank.
*                  This function is used in Hardware mode only.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_SendWENCmd(void)
{
  SMI->CR2 |= SMI_WEN_Mask;
}

/*******************************************************************************
* Function Name  : SMI_SendRSRCmd
* Description    : Sends a Read Status Register Command to the selected memory
*                  Bank.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_SendRSRCmd(void)
{
  SMI->CR2 |= SMI_RSR_Mask;
}

/*******************************************************************************
* Function Name  : SMI_SendCmd
* Description    : Sends command to the selected memory Bank. This function is
*                  used in Software mode only.
* Input          : - Command: specifies the command to send to the external memory.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_SendCmd(u32 Command)
{
  /* Load the command in the Transmit Register */
  SMI->TR = Command;

  /* Start transfer */    
  SMI->CR2 |= SMI_SEND_Mask;
}

/*******************************************************************************
* Function Name  : SMI_FastReadConfig
* Description    : Enables or disables the Fast Read Mode.
* Input          : - SMI_FastRead: specifies whether the Fast Read Mode is
*                    enabled or disabled.
*                    This parameter can be one of the following values:
*                          - SMI_FastRead_Disable : Fast Read Mode disabled
*                          - SMI_FastRead_Enable : Fast Read Mode enabled
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_FastReadConfig(u32 SMI_FastRead)
{
  if(SMI_FastRead == SMI_FastRead_Enable)
  {
    SMI->CR1 |= SMI_FastRead_Enable;
  }
  else
  {
    SMI->CR1 &= SMI_FastRead_Disable;
  }
}

/*******************************************************************************
* Function Name  : SMI_WriteBurstConfig
* Description    : Enables or disables the Write Burst Mode.
* Input          : - SMI_WriteBurst: specifies whether the Write Burst Mode is
*                    enabled or disabled.
*                    This parameter can be one of the following values:
*                          - SMI_WriteBurst_Disable : Write Burst Mode disabled
*                          - SMI_WriteBurst_Enable : Write Burst Mode enabled
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_WriteBurstConfig(u32 SMI_WriteBurst)
{
  if(SMI_WriteBurst == SMI_WriteBurst_Enable)
  {
    SMI->CR1 |= SMI_WriteBurst_Enable;
  }
  else
  {
    SMI->CR1 &= SMI_WriteBurst_Disable;
  }
}

/*******************************************************************************
* Function Name  : SMI_WriteByte
* Description    : Writes a Byte to the selected memory Bank. This function is
*                  used in Hardware mode only.
*                  Before calling this function, send a Write Enable command to 
*                  the selected memory Bank using SMI_SendWENCmd() function.
* Input          : - WriteAddr: external memory address from which the data will
*                    be written.
*                  - Data: data to be written to the external memory.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_WriteByte(u32 WriteAddr, u8 Data)
{
  /* Transfer data to the memory */
  *(u8 *) WriteAddr = Data;
}

/*******************************************************************************
* Function Name  : SMI_WriteHalfWord
* Description    : Writes a Half Word to the selected memory Bank. This function
*                  is used in Hardware mode only.
*                  Before calling this function, send a Write Enable command to 
*                  the selected memory Bank using SMI_SendWENCmd() function.
* Input          : - WriteAddr: external memory address from which the data will
*                    be written.
*                  - Data: data to be written to the external memory.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_WriteHalfWord(u32 WriteAddr, u16 Data)
{
  /* Transfer data to the memory */
  *(u16 *) WriteAddr = Data;
}

/*******************************************************************************
* Function Name  : SMI_WriteWord
* Description    : Writes a Word to the selected memory Bank. This function is
*                  used in Hardware mode only.
*                  Before calling this function, send a Write Enable command to 
*                  the selected memory Bank using SMI_SendWENCmd() function.
* Input          : - WriteAddr: external memory address from which the data will
*                    be written.
*                  - Data: data to be written to the external memory.
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_WriteWord(u32 WriteAddr, u32 Data)
{
  /* Transfer data to the memory */
  *(u32 *) WriteAddr = Data;
}

/*******************************************************************************
* Function Name  : SMI_ReadByte
* Description    : Reads a Byte from the selected memory Bank. This function is
*                  used in Hardware mode only.
* Input          : - ReadAddr: external memory address to read from.
* Output         : None
* Return         : Data read from the external memory.
*******************************************************************************/
u8 SMI_ReadByte(u32 ReadAddr)
{
  return(*(u8 *) ReadAddr);
}

/*******************************************************************************
* Function Name  : SMI_ReadHalfWord
* Description    : Reads a Half Word from the selected memory Bank. This function
*                  is used in Hardware mode only.
* Input          : - ReadAddr: external memory address to read from.
* Output         : None
* Return         : Data read from the external memory.
*******************************************************************************/
u16 SMI_ReadHalfWord(u32 ReadAddr)
{
  return(*(u16 *) ReadAddr);
}

/*******************************************************************************
* Function Name  : SMI_ReadWord
* Description    : Reads a Word from the selected memory Bank. This function is
*                  used in Hardware mode only.
* Input          : - ReadAddr: external memory address to read from.
* Output         : None
* Return         : Data read from the external memory.
*******************************************************************************/
u32 SMI_ReadWord(u32 ReadAddr)
{
  return(*(u32 *) ReadAddr);
}

/*******************************************************************************
* Function Name  : SMI_ReadMemoryStatusRegister
* Description    : Reads the status register of the memory connected to the
*                  selected Bank.
* Input          : None
* Output         : None
* Return         : External memory status register value.
*******************************************************************************/
u8 SMI_ReadMemoryStatusRegister(void)
{
 return((u8) (SMI->SR & SMI_STATUSREGISTER_Mask));
}

/*******************************************************************************
* Function Name  : SMI_GetFlagStatus
* Description    : Checks whether the specified SMI flag is set or not.
* Input          : - SMI_FLAG: specifies the flag to check.
*                    This parameter can be one of the following values:
*                          - SMI_FLAG_Bank3_WM : Memory Bank3 Write Mode flag
*                          - SMI_FLAG_Bank2_WM : Memory Bank2 Write Mode flag
*                          - SMI_FLAG_Bank1_WM : Memory Bank1 Write Mode flag
*                          - SMI_FLAG_Bank0_WM : Memory Bank0 Write Mode flag
*                          - SMI_FLAG_ERF2 : Error Flag 2: Forbidden Write Request
*                          - SMI_FLAG_ERF1 : Error Flag 1: Forbidden Access
*                          - SMI_FLAG_WC : Write Complete flag
*                          - SMI_FLAG_TF : Transfer Finished flag
* Output         : None
* Return         : The new state of SMI_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus SMI_GetFlagStatus(u32 SMI_FLAG)
{
  if((SMI->SR & SMI_FLAG) != RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : SMI_ClearFlag
* Description    : Clears the SMI’s pending flags.
* Input          : - SMI_FLAG: specifies the flag to clear.
*                    This parameter can be any combination of the following values:
*                          - SMI_FLAG_ERF2 : Error Flag 2: Forbidden Write Request
*                          - SMI_FLAG_ERF1 : Error Flag 1: Forbidden Access
*                          - SMI_FLAG_WC : Write Complete flag
*                          - SMI_FLAG_TF : Transfer Finished flag
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_ClearFlag(u32 SMI_FLAG)
{
  SMI->SR &= ~SMI_FLAG;
}

/*******************************************************************************
* Function Name  : SMI_GetITStatus
* Description    : Checks whether the specified SMI interrupt has occurred or not.
* Input          : - SMI_FLAG: specifies the interrupt source to check.
*                    This parameter can be one of the following values:
*                          - SMI_IT_WC : Write Complete Interrupt
*                          - SMI_IT_TF : Transfer Finished Interrupt
* Output         : None
* Return         : The new state of SMI_IT (SET or RESET).
*******************************************************************************/
ITStatus SMI_GetITStatus(u32 SMI_IT)
{
  if(((SMI->CR2 & SMI_IT) != RESET) && ((SMI->SR & SMI_IT) != RESET))
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : SMI_ClearITPendingBit
* Description    : Clears the SMI’s interrupt pending bits.
* Input          : - SMI_FLAG: specifies the interrupts sources to clear.
*                    This parameter can be any combination of the following values:
*                          - SMI_IT_WC : Write Complete Interrupt
*                          - SMI_IT_TF : Transfer Finished Interrupt
* Output         : None
* Return         : None
*******************************************************************************/
void SMI_ClearITPendingBit(u32 SMI_IT)
{
  SMI->SR &= ~SMI_IT;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
