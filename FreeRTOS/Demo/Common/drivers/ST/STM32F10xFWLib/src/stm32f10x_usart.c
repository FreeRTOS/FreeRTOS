/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_usart.c
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file provides all the USART firmware functions.
********************************************************************************
* History:
* 04/02/2007: V0.2
* 02/05/2007: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_usart.h"
#include "stm32f10x_rcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* USART RUN Mask */
#define CR1_RUN_Set               ((u16)0x2000)  /* USART Enable Mask */
#define CR1_RUN_Reset             ((u16)0xDFFF)  /* USART Disable Mask */

#define CR2_Address_Mask          ((u16)0xFFF0)  /* USART address Mask */

/* USART RWU Mask */
#define CR1_RWU_Set               ((u16)0x0002)  /* USART mute mode Enable Mask */
#define CR1_RWU_Reset             ((u16)0xFFFD)  /* USART mute mode Enable Mask */

#define USART_IT_Mask             ((u16)0x001F)  /* USART Interrupt Mask */

/* USART LIN Mask */
#define CR2_LINE_Set              ((u16)0x4000)  /* USART LIN Enable Mask */
#define CR2_LINE_Reset            ((u16)0xBFFF)  /* USART LIN Disable Mask */

#define CR1_SBK_Set               ((u16)0x0001)  /* USART Break Character send Mask */

/* USART SC Mask */
#define CR3_SCEN_Set              ((u16)0x0020)  /* USART SC Enable Mask */
#define CR3_SCEN_Reset            ((u16)0xFFDF)  /* USART SC Disable Mask */

/* USART SC NACK Mask */
#define CR3_NACK_Set              ((u16)0x0010)  /* USART SC NACK Enable Mask */
#define CR3_NACK_Reset            ((u16)0xFFEF)  /* USART SC NACK Disable Mask */

/* USART Half-Duplex Mask */
#define CR3_HDSEL_Set             ((u16)0x0008)  /* USART Half-Duplex Enable Mask */
#define CR3_HDSEL_Reset           ((u16)0xFFF7)  /* USART Half-Duplex Disable Mask */

/* USART IrDA Mask */
#define CR3_IRLP_Mask             ((u16)0xFFFB)  /* USART IrDA LowPower mode Mask */

/* USART LIN Break detection */
#define CR3_LBDL_Mask             ((u16)0xFFDF)  /* USART LIN Break detection Mask */

/* USART WakeUp Method  */
#define CR3_WAKE_Mask             ((u16)0xF7FF)  /* USART WakeUp Method Mask */

/* USART IrDA Mask */
#define CR3_IREN_Set              ((u16)0x0002)  /* USART IrDA Enable Mask */
#define CR3_IREN_Reset            ((u16)0xFFFD)  /* USART IrDA Disable Mask */

#define GTPR_LSB_Mask             ((u16)0x00FF)  /* Guard Time Register LSB Mask */
#define GTPR_MSB_Mask             ((u16)0xFF00)  /* Guard Time Register MSB Mask */

#define CR1_CLEAR_Mask            ((u16)0xE9F3)  /* USART CR1 Mask */
#define CR2_CLEAR_Mask            ((u16)0xC0FF)  /* USART CR2 Mask */
#define CR3_CLEAR_Mask            ((u16)0xFCFF)  /* USART CR3 Mask */


/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : USART_DeInit
* Description    : Deinitializes the USARTx peripheral registers to their
*                  default reset values.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_DeInit(USART_TypeDef* USARTx)
{
  switch (*(u32*)&USARTx)
  {
    case USART1_BASE:
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_USART1, ENABLE);
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_USART1, DISABLE);
      break;

    case USART2_BASE:
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_USART2, ENABLE);
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_USART2, DISABLE);
      break;

    case USART3_BASE:
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_USART3, ENABLE);
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_USART3, DISABLE);
      break;

    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : USART_Init
* Description    : Initializes the USARTx peripheral according to the specified
*                  parameters in the USART_InitStruct .
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART peripheral.
*                  - USART_InitStruct: pointer to a USART_InitTypeDef structure
*                    that contains the configuration information for the
*                    specified USART peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_Init(USART_TypeDef* USARTx, USART_InitTypeDef* USART_InitStruct)
{
  u32 tmpreg = 0x00, apbclock = 0x00;
  u32 integerdivider = 0x00;
  u32 fractionaldivider = 0x00;
  RCC_ClocksTypeDef RCC_ClocksStatus;

  /* Check the parameters */
  assert(IS_USART_WORD_LENGTH(USART_InitStruct->USART_WordLength));
  assert(IS_USART_STOPBITS(USART_InitStruct->USART_StopBits));
  assert(IS_USART_PARITY(USART_InitStruct->USART_Parity));
  assert(IS_USART_HARDWARE_FLOW_CONTROL(USART_InitStruct->USART_HardwareFlowControl));
  assert(IS_USART_MODE(USART_InitStruct->USART_Mode));
  assert(IS_USART_CLOCK(USART_InitStruct->USART_Clock));
  assert(IS_USART_CPOL(USART_InitStruct->USART_CPOL));
  assert(IS_USART_CPHA(USART_InitStruct->USART_CPHA));
  assert(IS_USART_LASTBIT(USART_InitStruct->USART_LastBit));              
  
/*---------------------------- USART CR2 Configuration -----------------------*/
  tmpreg = USARTx->CR2;
  /* Clear STOP[13:12], CLKEN, CPOL, CPHA and LBCL bits */
  tmpreg &= CR2_CLEAR_Mask;

  /* Configure the USART Stop Bits, Clock, CPOL, CPHA and LastBit ------------*/
  /* Set STOP[13:12] bits according to USART_Mode value */
  /* Set CPOL bit according to USART_CPOL value */
  /* Set CPHA bit according to USART_CPHA value */
  /* Set LBCL bit according to USART_LastBit value */
  tmpreg |= (u32)USART_InitStruct->USART_StopBits | USART_InitStruct->USART_Clock |
            USART_InitStruct->USART_CPOL | USART_InitStruct->USART_CPHA |
            USART_InitStruct->USART_LastBit;

  /* Write to USART CR2 */
  USARTx->CR2 = (u16)tmpreg;

/*---------------------------- USART CR1 Configuration -----------------------*/
  tmpreg = 0x00;
  tmpreg = USARTx->CR1;
  /* Clear M, PCE, PS, TE and RE bits */
  tmpreg &= CR1_CLEAR_Mask;

  /* Configure the USART Word Length, Parity and mode ----------------------- */
  /* Set the M bits according to USART_WordLength value */
  /* Set PCE and PS bits according to USART_Parity value */
  /* Set TE and RE bits according to USART_Mode value */
  tmpreg |= (u32)USART_InitStruct->USART_WordLength | USART_InitStruct->USART_Parity |
            USART_InitStruct->USART_Mode;

  /* Write to USART CR1 */
  USARTx->CR1 = (u16)tmpreg;

/*---------------------------- USART CR3 Configuration -----------------------*/
  tmpreg = 0x00;
  tmpreg = USARTx->CR3;
  /* Clear CTSE and RTSE bits */
  tmpreg &= CR3_CLEAR_Mask;

  /* Configure the USART HFC -------------------------------------------------*/
  /* Set CTSE and RTSE bits according to USART_HardwareFlowControl value */
  tmpreg |= USART_InitStruct->USART_HardwareFlowControl;

  /* Write to USART CR3 */
  USARTx->CR3 = (u16)tmpreg;

/*---------------------------- USART BRR Configuration -----------------------*/
  tmpreg = 0x00;

  /* Configure the USART Baud Rate -------------------------------------------*/
  RCC_GetClocksFreq(&RCC_ClocksStatus);
  if ((*(u32*)&USARTx) == USART1_BASE)
  {
    apbclock = RCC_ClocksStatus.PCLK2_Frequency;
  }
  else
  {
    apbclock = RCC_ClocksStatus.PCLK1_Frequency;
  }

  /* Determine the integer part */
  integerdivider = ((0x19 * apbclock) / (0x04 * (USART_InitStruct->USART_BaudRate)));
  tmpreg = (integerdivider / 0x64) << 0x04;

  /* Determine the fractional part */
  fractionaldivider = integerdivider - (0x64 * (tmpreg >> 0x04));
  tmpreg |= ((((fractionaldivider * 0x10) + 0x32) / 0x64)) & ((u8)0x0F);

  /* Write to USART BRR */
  USARTx->BRR = (u16)tmpreg;
}

/*******************************************************************************
* Function Name  : USART_StructInit
* Description    : Fills each USART_InitStruct member with its default value.
* Input          : - USART_InitStruct: pointer to a USART_InitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_StructInit(USART_InitTypeDef* USART_InitStruct)
{
  /* USART_InitStruct members default value */
  USART_InitStruct->USART_BaudRate = 0x2580; /* 9600 Baud */
  USART_InitStruct->USART_WordLength = USART_WordLength_8b;
  USART_InitStruct->USART_StopBits = USART_StopBits_1;
  USART_InitStruct->USART_Parity = USART_Parity_No ;
  USART_InitStruct->USART_HardwareFlowControl = USART_HardwareFlowControl_None;
  USART_InitStruct->USART_Mode = USART_Mode_Rx | USART_Mode_Tx;
  USART_InitStruct->USART_Clock = USART_Clock_Disable;
  USART_InitStruct->USART_CPOL = USART_CPOL_Low;
  USART_InitStruct->USART_CPHA = USART_CPHA_1Edge;
  USART_InitStruct->USART_LastBit = USART_LastBit_Disable;
}

/*******************************************************************************
* Function Name  : USART_Cmd
* Description    : Enables or disables the specified USART peripheral.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                : - NewState: new state of the USARTx peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_Cmd(USART_TypeDef* USARTx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the selected USART by setting the RUN bit in the CR1 register */
    USARTx->CR1 |= CR1_RUN_Set;
  }
  else
  {
    /* Disable the selected USART by clearing the RUN bit in the CR1 register */
    USARTx->CR1 &= CR1_RUN_Reset;
  }
}

/*******************************************************************************
* Function Name  : USART_ITConfig
* Description    : Enables or disables the specified USART interrupts.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_IT: specifies the USART interrupt sources to be
*                    enabled or disabled.
*                    This parameter can be one of the following values:
*                       - USART_IT_PE
*                       - USART_IT_TXE
*                       - USART_IT_TC
*                       - USART_IT_RXNE
*                       - USART_IT_IDLE
*                       - USART_IT_LBD
*                       - USART_IT_CTS
*                       - USART_IT_ERR
*                  - NewState: new state of the specified USARTx interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_ITConfig(USART_TypeDef* USARTx, u16 USART_IT, FunctionalState NewState)
{
  u32 usartreg = 0x00, itpos = 0x00, itmask = 0x00;
  u32 address = 0x00;

  /* Check the parameters */
  assert(IS_USART_CONFIG_IT(USART_IT));  
  assert(IS_FUNCTIONAL_STATE(NewState));
  
  /* Get the USART register index */
  usartreg = (((u8)USART_IT) >> 0x05);

  /* Get the interrupt position */
  itpos = USART_IT & USART_IT_Mask;

  itmask = (((u32)0x01) << itpos);
  address = *(u32*)&(USARTx);

  if (usartreg == 0x01) /* The IT  is in CR1 register */
  {
    address += 0x0C;
  }
  else if (usartreg == 0x02) /* The IT  is in CR2 register */
  {
    address += 0x10;
  }
  else /* The IT  is in CR3 register */
  {
    address += 0x14; 
  }
  if (NewState != DISABLE)
  {
    *(u32*)address  |= itmask;
  }
  else
  {
    *(u32*)address &= ~itmask;
  }
}

/*******************************************************************************
* Function Name  : USART_DMACmd
* Description    : Enables or disables the USART’s DMA interface.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_DMAReq: specifies the DMA request.
*                    This parameter can be any combination of the following values:
*                       - USART_DMAReq_Tx
*                       - USART_DMAReq_Rx
*                  - NewState: new state of the DMA Request sources.
*                   This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_DMACmd(USART_TypeDef* USARTx, u16 USART_DMAReq, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_USART_DMAREQ(USART_DMAReq));  
  assert(IS_FUNCTIONAL_STATE(NewState)); 
  
  if (NewState != DISABLE)
  {
    /* Enable the DMA transfer for selected requests by setting the DMAT and/or
    DMAR bits in the USART CR3 register */
    USARTx->CR3 |= USART_DMAReq;
  }
  else
  {
    /* Disable the DMA transfer for selected requests by clearing the DMAT and/or
    DMAR bits in the USART CR3 register */
    USARTx->CR3 &= (u16)~USART_DMAReq;
  }
}

/*******************************************************************************
* Function Name  : USART_SetAddress
* Description    : Sets the address of the USART node.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_Address: Indicates the address of the USART node.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_SetAddress(USART_TypeDef* USARTx, u8 USART_Address)
{
  /* Check the parameters */
  assert(IS_USART_ADDRESS(USART_Address)); 
    
  /* Clear the USART address */
  USARTx->CR2 &= CR2_Address_Mask;
  /* Set the USART address node */
  USARTx->CR2 |= USART_Address;
}

/*******************************************************************************
* Function Name  : USART_WakeUpConfig
* Description    : Selects the USART WakeUp method.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_WakeUp: specifies the USART wakeup method.
*                    This parameter can be one of the following values:
*                        - USART_WakeUp_IdleLine
*                        - USART_WakeUp_AddressMark
* Output         : None
* Return         : None
*******************************************************************************/
void USART_WakeUpConfig(USART_TypeDef* USARTx, u16 USART_WakeUp)
{
  /* Check the parameters */
  assert(IS_USART_WAKEUP(USART_WakeUp));
  
  USARTx->CR1 &= CR3_WAKE_Mask;
  USARTx->CR1 |= USART_WakeUp;
}

/*******************************************************************************
* Function Name  : USART_ReceiverWakeUpCmd
* Description    : Determines if the USART is in mute mode or not.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - NewState: new state of the USART mode.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_ReceiverWakeUpCmd(USART_TypeDef* USARTx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState)); 
  
  if (NewState != DISABLE)
  {
    /* Enable the mute mode USART by setting the RWU bit in the CR1 register */
    USARTx->CR1 |= CR1_RWU_Set;
  }
  else
  {
    /* Disable the mute mode USART by clearing the RWU bit in the CR1 register */
    USARTx->CR1 &= CR1_RWU_Reset;
  }
}

/*******************************************************************************
* Function Name  : USART_LINBreakDetectLengthConfig
* Description    : Sets the USART LIN Break detection length.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_LINBreakDetectLength: specifies the LIN break
*                    detection length.
*                    This parameter can be one of the following values:
*                       - USART_LINBreakDetectLength_10b
*                       - USART_LINBreakDetectLength_11b
* Output         : None
* Return         : None
*******************************************************************************/
void USART_LINBreakDetectLengthConfig(USART_TypeDef* USARTx, u16 USART_LINBreakDetectLength)
{
  /* Check the parameters */
  assert(IS_USART_LIN_BREAK_DETECT_LENGTH(USART_LINBreakDetectLength));
  
  USARTx->CR2 &= CR3_LBDL_Mask;
  USARTx->CR2 |= USART_LINBreakDetectLength;  
}

/*******************************************************************************
* Function Name  : USART_LINCmd
* Description    : Enables or disables the USART’s LIN mode.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - NewState: new state of the USART LIN mode.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_LINCmd(USART_TypeDef* USARTx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the LIN mode by setting the LINE bit in the CR2 register */
    USARTx->CR2 |= CR2_LINE_Set;
  }
  else
  {
    /* Disable the LIN mode by clearing the LINE bit in the CR2 register */
    USARTx->CR2 &= CR2_LINE_Reset;
  }
}

/*******************************************************************************
* Function Name  : USART_SendData
* Description    : Transmits signle data through the USARTx peripheral.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - Data: the data to transmit.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_SendData(USART_TypeDef* USARTx, u16 Data)
{
  /* Check the parameters */
  assert(IS_USART_DATA(Data)); 
    
  /* Transmit Data */
  USARTx->DR = (Data & (u16)0x01FF);
}

/*******************************************************************************
* Function Name  : USART_ReceiveData
* Description    : Returns the most recent received data by the USARTx peripheral.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
* Output         : None
* Return         : The received data.
*******************************************************************************/
u16 USART_ReceiveData(USART_TypeDef* USARTx)
{
  /* Receive Data */
  return (u16)(USARTx->DR & (u16)0x01FF);
}

/*******************************************************************************
* Function Name  : USART_SendBreak
* Description    : Transmits break characters.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_SendBreak(USART_TypeDef* USARTx)
{
  /* Send break characters */
  USARTx->CR1 |= CR1_SBK_Set;
}

/*******************************************************************************
* Function Name  : USART_SetGuardTime
* Description    : Sets the specified USART guard time.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_GuardTime: specifies the guard time.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_SetGuardTime(USART_TypeDef* USARTx, u8 USART_GuardTime)
{    
  /* Clear the USART Guard time */
  USARTx->GTPR &= GTPR_LSB_Mask;
  /* Set the USART guard time */
  USARTx->GTPR |= (u16)((u16)USART_GuardTime << 0x08);
}

/*******************************************************************************
* Function Name  : USART_SetPrescaler
* Description    : Sets the system clock prescaler.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_Prescaler: specifies the prescaler clock.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_SetPrescaler(USART_TypeDef* USARTx, u8 USART_Prescaler)
{ 
  /* Clear the USART prescaler */
  USARTx->GTPR &= GTPR_MSB_Mask;
  /* Set the USART prescaler */
  USARTx->GTPR |= USART_Prescaler;
}

/*******************************************************************************
* Function Name  : USART_SmartCardCmd
* Description    : Enables or disables the USART’s Smart Card mode.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - NewState: new state of the Smart Card mode.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_SmartCardCmd(USART_TypeDef* USARTx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
    
  if (NewState != DISABLE)
  {
    /* Enable the SC mode by setting the SCEN bit in the CR3 register */
    USARTx->CR3 |= CR3_SCEN_Set;
  }
  else
  {
    /* Disable the SC mode by clearing the SCEN bit in the CR3 register */
    USARTx->CR3 &= CR3_SCEN_Reset;
  }
}

/*******************************************************************************
* Function Name  : USART_SmartCardNACKCmd
* Description    : Enables or disables NACK transmission.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - NewState: new state of the NACK transmission.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_SmartCardNACKCmd(USART_TypeDef* USARTx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
   
  if (NewState != DISABLE)
  {
    /* Enable the NACK transmission by setting the NACK bit in the CR3 register */
    USARTx->CR3 |= CR3_NACK_Set;
  }
  else
  {
    /* Disable the NACK transmission by clearing the NACK bit in the CR3 register */
    USARTx->CR3 &= CR3_NACK_Reset;
  }

}

/*******************************************************************************
* Function Name  : USART_HalfDuplexCmd
* Description    : Enables or disables the USART’s Half Duplex communication.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - NewState: new state of the USART Communication.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_HalfDuplexCmd(USART_TypeDef* USARTx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the Half-Duplex mode by setting the HDSEL bit in the CR3 register */
    USARTx->CR3 |= CR3_HDSEL_Set;
  }
  else
  {
    /* Disable the Half-Duplex mode by clearing the HDSEL bit in the CR3 register */
    USARTx->CR3 &= CR3_HDSEL_Reset;
  }
}

/*******************************************************************************
* Function Name  : USART_IrDAConfig
* Description    : Configures the USART’s IrDA interface.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_IrDAMode: specifies the IrDA mode.
*                    This parameter can be one of the following values:
*                       - USART_IrDAMode_LowPower
*                       - USART_IrDAMode_Normal
* Output         : None
* Return         : None
*******************************************************************************/
void USART_IrDAConfig(USART_TypeDef* USARTx, u16 USART_IrDAMode)
{
  /* Check the parameters */
  assert(IS_USART_IRDA_MODE(USART_IrDAMode));
    
  USARTx->CR3 &= CR3_IRLP_Mask;
  USARTx->CR3 |= USART_IrDAMode;
}

/*******************************************************************************
* Function Name  : USART_IrDACmd
* Description    : Enables or disables the USART’s IrDA interface.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - NewState: new state of the IrDA mode.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void USART_IrDACmd(USART_TypeDef* USARTx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
    
  if (NewState != DISABLE)
  {
    /* Enable the IrDA mode by setting the IREN bit in the CR3 register */
    USARTx->CR3 |= CR3_IREN_Set;
  }
  else
  {
    /* Disable the IrDA mode by clearing the IREN bit in the CR3 register */
    USARTx->CR3 &= CR3_IREN_Reset;
  }
}

/*******************************************************************************
* Function Name  : USART_GetFlagStatus
* Description    : Checks whether the specified USART flag is set or not.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_FLAG: specifies the flag to check.
*                    This parameter can be one of the following values:
*                       - USART_FLAG_CTS
*                       - USART_FLAG_LBD
*                       - USART_FLAG_TXE
*                       - USART_FLAG_TC
*                       - USART_FLAG_RXNE
*                       - USART_FLAG_IDLE
*                       - USART_FLAG_ORE
*                       - USART_FLAG_NE
*                       - USART_FLAG_FE
*                       - USART_FLAG_PE
* Output         : None
* Return         : The new state of USART_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus USART_GetFlagStatus(USART_TypeDef* USARTx, u16 USART_FLAG)
{
  FlagStatus bitstatus = RESET;
  
  /* Check the parameters */
  assert(IS_USART_FLAG(USART_FLAG));
  
  if ((USARTx->SR & USART_FLAG) != (u16)RESET)
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  return bitstatus;
}

/*******************************************************************************
* Function Name  : USART_ClearFlag
* Description    : Clears the USARTx's pending flags.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_FLAG: specifies the flag to clear.
*                    This parameter can be any combination of the following values:
*                       - USART_FLAG_CTS
*                       - USART_FLAG_LBD
*                       - USART_FLAG_TXE
*                       - USART_FLAG_TC
*                       - USART_FLAG_RXNE
*                       - USART_FLAG_IDLE
*                       - USART_FLAG_ORE
*                       - USART_FLAG_NE
*                       - USART_FLAG_FE
*                       - USART_FLAG_PE
* Output         : None
* Return         : None
*******************************************************************************/
void USART_ClearFlag(USART_TypeDef* USARTx, u16 USART_FLAG)
{
  /* Check the parameters */
  assert(IS_USART_CLEAR_FLAG(USART_FLAG));
   
  USARTx->SR &= (u16)~USART_FLAG;
}

/*******************************************************************************
* Function Name  : USART_GetITStatus
* Description    : Checks whether the specified USART interrupt has occurred or not.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_IT: specifies the USART interrupt source to check.
*                    This parameter can be one of the following values:
*                       - USART_IT_PE
*                       - USART_IT_TXE
*                       - USART_IT_TC
*                       - USART_IT_RXNE
*                       - USART_IT_IDLE
*                       - USART_IT_LBD
*                       - USART_IT_CTS
*                       - USART_IT_ORE
*                       - USART_IT_NE
*                       - USART_IT_FE
* Output         : None
* Return         : The new state of USART_IT (SET or RESET).
*******************************************************************************/
ITStatus USART_GetITStatus(USART_TypeDef* USARTx, u16 USART_IT)
{
  u32 bitpos = 0x00, itmask = 0x00, usartreg = 0;
  ITStatus bitstatus = RESET;

  /* Check the parameters */
  assert(IS_USART_IT(USART_IT));
  
  /* Get the USART register index */
  usartreg = (((u8)USART_IT) >> 0x05);

  /* Get the interrupt position */
  itmask = USART_IT & USART_IT_Mask;

  itmask = (u32)0x01 << itmask;
  
  if (usartreg == 0x01) /* The IT  is in CR1 register */
  {
    itmask &= USARTx->CR1;
  }
  else if (usartreg == 0x02) /* The IT  is in CR2 register */
  {
    itmask &= USARTx->CR2;
  }
  else /* The IT  is in CR3 register */
  {
    itmask &= USARTx->CR3;
  }
  
  bitpos = USART_IT >> 0x08;

  bitpos = (u32)0x01 << bitpos;
  bitpos &= USARTx->SR;

  if ((itmask != (u16)RESET)&&(bitpos != (u16)RESET))
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  return bitstatus;
}

/*******************************************************************************
* Function Name  : USART_ClearITPendingBit
* Description    : Clears the USARTx’s interrupt pending bits.
* Input          : - USARTx: where x can be 1, 2 or 3 to select the USART
*                    peripheral.
*                  - USART_IT: specifies the interrupt pending bit to clear.
*                    This parameter can be one of the following values:
*                       - USART_IT_PE
*                       - USART_IT_TXE
*                       - USART_IT_TC
*                       - USART_IT_RXNE
*                       - USART_IT_IDLE
*                       - USART_IT_LBD
*                       - USART_IT_CTS
*                       - USART_IT_ORE
*                       - USART_IT_NE
*                       - USART_IT_FE
* Output         : None
* Return         : None
*******************************************************************************/
void USART_ClearITPendingBit(USART_TypeDef* USARTx, u16 USART_IT)
{
  u32 bitpos = 0x00, itmask = 0x00;
  
  /* Check the parameters */
  assert(IS_USART_IT(USART_IT));
  
  bitpos = USART_IT >> 0x08;

  itmask = (u32)0x01 << bitpos;
  USARTx->SR &= ~itmask;
}

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
