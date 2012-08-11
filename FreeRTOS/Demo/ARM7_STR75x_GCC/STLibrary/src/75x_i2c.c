/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_i2c.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006 
* Description        : This file provides all the I2C software functions.
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
#include "75x_i2c.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/

/* I2C IT enable */
#define  I2C_IT_Enable     0x01
#define  I2C_IT_Disable    0xFE

/* I2C Peripheral Enable/Disable */
#define  I2C_PE_Set        0x20
#define  I2C_PE_Reset      0xDF

/* I2C START Enable/Disable */
#define  I2C_Start_Enable      0x08
#define  I2C_Start_Disable     0xF7

/* I2C STOP Enable/Disable */
#define  I2C_Stop_Enable       0x02
#define  I2C_Stop_Disable      0xFD

/* Address direction bit */
#define I2C_ADD0_Set      0x01
#define I2C_ADD0_Reset    0xFE

/* I2C Masks */
#define  I2C_Frequency_Mask     0x1F
#define  I2C_AddressHigh_Mask   0xF9
#define  I2C_OwnAddress_Mask    0x0300  
#define  I2C_StandardMode_Mask  0x7f 
#define  I2C_FastMode_Mask      0x80  
#define  I2C_Event_Mask         0x3FFF

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : I2C_DeInit                                                
* Description    : Deinitializes the I2C peripheral registers to their default
*                  reset values.                 
* Input          : None               
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void I2C_DeInit(void)
{
  /* Reset the I2C registers values*/
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_I2C,ENABLE);
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_I2C,DISABLE); 
}

/*******************************************************************************
* Function Name  : I2C_Init                                                  
* Description    : Initializes the I2C peripheral according to the specified
*                  parameters in the I2C_Initstruct.
* Input          : - I2C_InitStruct: pointer to a I2C_InitTypeDef structure that
*                  contains the configuration information for the specified I2C
*                  peripheral.               
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void I2C_Init(I2C_InitTypeDef* I2C_InitStruct)
{
  u8 ITEState = 0;
  u16 Result = 0x0F;
  u32 APBClock = 8000000;
  MRCC_ClocksTypeDef  MRCC_ClocksStatus;

  /* Get APBClock frequency value */
  MRCC_GetClocksStatus(&MRCC_ClocksStatus);
  APBClock = MRCC_ClocksStatus.PCLK_Frequency;
  /* Save ITE bit state */
  ITEState = I2C->CR & 0xFE;
  /* Disable I2C peripheral to set FR[2:0] bits */
  I2C_Cmd(DISABLE);
  /* Clear frequency FR[2:0] bits */
  I2C->OAR2 &= I2C_Frequency_Mask;
  
  /* Set frequency bits depending on APBClock value */
  if (APBClock < 10000000)
    I2C->OAR2 &= 0x1F;
  else if (APBClock < 16670000)
    I2C->OAR2 |= 0x20;
  else if (APBClock < 26670000)
    I2C->OAR2 |= 0x40;
  else if (APBClock < 40000000)
    I2C->OAR2 |= 0x60;
  else if (APBClock < 53330000)
    I2C->OAR2 |= 0x80;
  else if (APBClock < 66000000)
    I2C->OAR2 |= 0xA0;
  else if (APBClock < 80000000)
    I2C->OAR2 |= 0xC0;
  else if (APBClock < 100000000)
    I2C->OAR2 |= 0xE0;
  I2C_Cmd(ENABLE);
  
  /* Restore the ITE bit state */
  I2C->CR |= ITEState;

  /* Configure general call */
  if (I2C_InitStruct->I2C_GeneralCall == I2C_GeneralCall_Enable)
  {
    /* Enable general call */
    I2C->CR |= I2C_GeneralCall_Enable;
  }
  else
  {
    /* Disable general call */
    I2C->CR &= I2C_GeneralCall_Disable;
  }
  
  /* Configure acknowledgement */
  if (I2C_InitStruct->I2C_Ack == I2C_Ack_Enable)
  {
    /* Enable acknowledgement */
    I2C->CR |= I2C_Ack_Enable;
  }
  else
  {
    /* Disable acknowledgement */
    I2C->CR &= I2C_Ack_Disable;
  }
  
  /* Configure LSB own address */
  I2C->OAR1 = I2C_InitStruct->I2C_OwnAddress;
  /* Clear MSB own address ADD[9:8] bits */
  I2C->OAR2 &= I2C_AddressHigh_Mask;
  /* Set MSB own address value */
  I2C->OAR2 |= (I2C_InitStruct->I2C_OwnAddress & I2C_OwnAddress_Mask)>>7;

  /* Configure speed in standard mode */
  if (I2C_InitStruct->I2C_CLKSpeed <= 100000)
  {
    /* Standard mode speed calculate */
    Result = ((APBClock/I2C_InitStruct->I2C_CLKSpeed)-7)/2;
    /* Set speed value and clear FM/SM bit for standard mode in LSB clock divider */
    I2C->CCR = Result & I2C_StandardMode_Mask;
  }
  /* Configure speed in fast mode */
  else if (I2C_InitStruct->I2C_CLKSpeed <= 400000)
  {
    /* Fast mode speed calculate */
    Result = ((APBClock/I2C_InitStruct->I2C_CLKSpeed)-9)/3;
    /* Set speed value and set FM/SM bit for fast mode in LSB clock divider */
    I2C->CCR = Result | I2C_FastMode_Mask;
  }
  /* Set speed in MSB clock divider */
  I2C->ECCR = Result >>7;
}

/*******************************************************************************
* Function Name  : I2C_StructInit                   
* Description    : Fills each I2C_InitStruct member with its default value.
* Input          : - I2C_InitStruct: pointer to an I2C_InitTypeDef structure
                     which will be initialized.  
* Output         : None              
* Return         : None.                            
*******************************************************************************/
void I2C_StructInit(I2C_InitTypeDef* I2C_InitStruct)
{
  /* Initialize the I2C_CLKSpeed member */
  I2C_InitStruct->I2C_CLKSpeed = 5000;
  
  /* Initialize the I2C_OwnAddress member */
  I2C_InitStruct->I2C_OwnAddress = 0x0;
  
  /* Initialize the I2C_GeneralCall member */
  I2C_InitStruct->I2C_GeneralCall = I2C_GeneralCall_Disable;
  
  /* Initialize the I2C_Ack member */
  I2C_InitStruct->I2C_Ack = I2C_Ack_Disable;
}

/*******************************************************************************
* Function Name  : I2C_Cmd                                                    
* Description    : Enables or disables the I2C peripheral.      
* Input          : - NewState: new state of the I2C peripheral. This parameter
*                    can be: ENABLE or DISABLE.
* Output         : None                      
* Return         : None.                                                      
*******************************************************************************/
void I2C_Cmd(FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable the I2C peripheral by setting twice the PE bit on the CR register */
    I2C->CR |= I2C_PE_Set;
    I2C->CR |= I2C_PE_Set;
  }
  else
  {
    /* Disable the I2C peripheral */
    I2C->CR &= I2C_PE_Reset;
  }
}

/*******************************************************************************
* Function Name  : I2C_GenerateSTART                                          
* Description    : Generates I2C communication START condition.               
* Input          : - NewState: new state of the I2C START condition generation.
*                    This parameter can be: ENABLE or DISABLE.         
* Output         : None
* Return         : None.                                                      
*******************************************************************************/
void I2C_GenerateSTART(FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Generate a START condition */
    I2C->CR |= I2C_Start_Enable;
  }
  else
  {
    /* Disable the START condition generation */
    I2C->CR &= I2C_Start_Disable;
  }
}

/*******************************************************************************
* Function Name  : I2C_GenerateSTOP                                           
* Description    : Generates I2C communication STOP condition.                
* Input          : - NewState: new state of the I2C STOP condition generation.
*                    This parameter can be: ENABLE or DISABLE.       
* Output         : None                
* Return         : None.                                                      
*******************************************************************************/
void I2C_GenerateSTOP(FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Generate a SIOP condition */
    I2C->CR |= I2C_Stop_Enable;
  }
  else
  {
    /* Disable the STOP condition generation */
    I2C->CR &= I2C_Stop_Disable;
  }
}

/*******************************************************************************
* Function Name  : I2C_AcknowledgeConfig                                      
* Description    : Enables or disables I2C acknowledge feature.               
* Input          : - NewState: new state of the I2C Acknowledgement. 
*                    This parameter can be: ENABLE or DISABLE. 
* Output         : None                     
* Return         : None.                                                      
*******************************************************************************/
void I2C_AcknowledgeConfig(FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable the acknowledgement */
    I2C->CR |= I2C_Ack_Enable;
  }
  else
  {
    /* Disable the acknowledgement */
    I2C->CR &= I2C_Ack_Disable;
  }
}

/*******************************************************************************
* Function Name  : I2C_ITConfig                                               
* Description    : Enables or disables the I2C interrupt.                 
* Input          : - NewState: new state of the I2C interrupt.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None                      
* Return         : None.                                                      
*******************************************************************************/
void I2C_ITConfig(FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable the I2C interrupt */
    I2C->CR |= I2C_IT_Enable;
  }
  else
  {
    /* Disable the I2C interrupt */
    I2C->CR &= I2C_IT_Disable;
  }
}

/*******************************************************************************
* Function Name  : I2C_GetLastEvent                                  
* Description    : Gets the last I2C event that has occurred.                  
* Input          : None  
* Output         : None                          
* Return         : The Last happened Event.                           
*******************************************************************************/
u16 I2C_GetLastEvent(void)
{
  u16 Flag1 = 0, Flag2 = 0, LastEvent = 0;

  Flag1 = I2C->SR1;
  Flag2 = I2C->SR2;
  Flag2 = Flag2<<8;
  /* Get the last event value from I2C status register */
  LastEvent = (((Flag1 | (Flag2)) & I2C_Event_Mask));
  /* Return the last event */
  return LastEvent;
}

/*******************************************************************************
* Function Name  : I2C_CheckEvent                                         
* Description    : Checks whether the Last I2C Event is equal to the one passed 
*                  as parameter.                                              
* Input          : - I2C_EVENT: specifies the event to be checked. This parameter
*                    can be one of the following values:
*                         - I2C_EVENT_SLAVE_ADDRESS_MATCHED
*                         - I2C_EVENT_SLAVE_BYTE_RECEIVED
*                         - I2C_EVENT_SLAVE_BYTE_TRANSMITTED
*                         - I2C_EVENT_SLAVE_ACK_FAILURE 
*                         - I2C_EVENT_MASTER_MODE_SELECT
*                         - I2C_EVENT_MASTER_MODE_SELECTED
*                         - I2C_EVENT_MASTER_BYTE_RECEIVED
*                         - I2C_EVENT_MASTER_BYTE_TRANSMITTED
*                         - I2C_EVENT_MASTER_MODE_ADDRESS10
*                         - I2C_EVENT_SLAVE_STOP_DETECTED
* Output         : None                                      
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Last event is equal to the I2C_Event
*                         - ERROR: Last event is different from the I2C_Event        
*******************************************************************************/
ErrorStatus I2C_CheckEvent(u16 I2C_EVENT)
{
  u16  LastEvent = I2C_GetLastEvent();

  /* Check whether the last event is equal to I2C_EVENT */
  if (LastEvent == I2C_EVENT)
  {
    /* Return SUCCESS when last event is equal to I2C_EVENT */
    return SUCCESS;
  }
  else
  {
    /* Return ERROR when last event is different from I2C_EVENT */
    return ERROR;
  }
}

/*******************************************************************************
* Function Name  : I2C_SendData                                                
* Description    : Sends a data byte.                                 
* Input          : - Data: indicates the byte to be transmitted.
* Output         : None            
* Return         : None.                                                       
*******************************************************************************/
void I2C_SendData(u8 Data)
{
  /* Write in the DR register the byte to be sent */
  I2C->DR = Data;
}

/*******************************************************************************
* Function Name  : I2C_ReceiveData                                             
* Description    : Reads the received byte. 
* Input          : None 
* Output         : None                                        
* Return         : The received byte                                      
*******************************************************************************/
u8 I2C_ReceiveData(void)
{
  /* Return from the DR register the received byte */
  return I2C->DR;
}

/*******************************************************************************
* Function Name  : I2C_Send7bitAddress                                             
* Description    : Transmits the address byte to select the slave device.      
* Input          : - Address: specifies the slave address which will be transmitted    
*                  - Direction: specifies whether the I2C device will be a 
*                    Transmitter or a Receiver. This parameter can be one of the 
*                    following values
*                         - I2C_MODE_TRANSMITTER: Transmitter mode
*                         - I2C_MODE_RECEIVER: Receiver mode  
* Output         : None	
* Return         : None.                                                       
*******************************************************************************/
void I2C_Send7bitAddress(u8 Address, u8 Direction)
{
  /* Test on the direction to define the read/write bit */
  if (Direction == I2C_MODE_RECEIVER)
  {
    /* Set the address bit0 for read */
    Address |= I2C_ADD0_Set;
  }
  else
  {
    /* Reset the address bit0 for write */
    Address &= I2C_ADD0_Reset;
  }
  /* Send the address */
  I2C->DR = Address;
}

/*******************************************************************************
* Function Name  : I2C_ReadRegister                                            
* Description    : Reads the specified I2C register and returns its value.    
* Input1         : - I2C_Register: specifies the register to read.
*                    This parameter can be one of the following values:        
*                         - I2C_CR:   CR register. 
*                         - I2C_SR1:  SR1 register.
*                         - I2C_SR2:  SR2 register.
*                         - I2C_CCR:  CCR register.
*                         - I2C_OAR1: OAR1 register.
*                         - I2C_OAR2: OAR2 register.
*                         - I2C_DR:   DR register.
*                         - I2C_ECCR: ECCR register.
* Output         : None
* Return         : The value of the read register.              
*******************************************************************************/
u8 I2C_ReadRegister(u8 I2C_Register)
{
  /* Return the selected register value */
  return (*(u8 *)(I2C_BASE + I2C_Register));
}

/*******************************************************************************
* Function Name  : I2C_GetFlagStatus  
* Description    : Checks whether the specified I2C flag is set or not.
* Input          : - I2C_FLAG: specifies the flag to check. 
*                    This parameter can be one of the following values:
*                         - I2C_FLAG_SB: Start bit flag (Master mode)    
*                         - I2C_FLAG_M_SL: Master/Slave flag   
*                         - I2C_FLAG_ADSL: Address matched flag (Slave mode)    
*                         - I2C_FLAG_BTF: Byte transfer finished flag    
*                         - I2C_FLAG_BUSY: Bus busy flag    
*                         - I2C_FLAG_TRA: Transmitter/Receiver flag    
*                         - I2C_FLAG_ADD10: 10-bit addressing in Master mode flag   
*                         - I2C_FLAG_EVF: Event flag     
*                         - I2C_FLAG_GCAL: General call flag (slave mode)   
*                         - I2C_FLAG_BERR: Bus error flag    
*                         - I2C_FLAG_ARLO: Arbitration lost flag    
*                         - I2C_FLAG_STOPF: Stop detection flag (slave mode)   
*                         - I2C_FLAG_AF: Acknowledge failure flag      
*                         - I2C_FLAG_ENDAD: End of address transmission flag   
*                         - I2C_FLAG_ACK: Acknowledge enable flag     
* Output         : None                                                   
* Return         : The NewState of the I2C_FLAG (SET or RESET).              
*******************************************************************************/
FlagStatus I2C_GetFlagStatus(u16 I2C_FLAG)
{ 
    u16 Flag1 = 0, Flag2 = 0, Flag3 = 0, Tmp = 0;

  Flag1 = I2C->SR1;
  Flag2 = I2C->SR2;
  Flag2 = Flag2<<8;
  Flag3 = I2C->CR & 0x04;
  
  /* Get all the I2C flags in a unique register*/
  Tmp = (((Flag1 | (Flag2)) & I2C_Event_Mask) | (Flag3<<12)); 
  
  /* Check the status of the specified I2C flag */
  if((Tmp & I2C_FLAG) != RESET)
  {
    /* Return SET if I2C_FLAG is set */
    return SET;
  }
  else
  {
    /* Return RESET if I2C_FLAG is reset */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : I2C_ClearFlag                                 
* Description    : Clears the I2C’s pending flags                            
* Input          : - I2C_FLAG: specifies the flag to clear. 
*                    This parameter can be one of the following values:
*                         - I2C_FLAG_SB: Start bit flag    
*                         - I2C_FLAG_M_SL: Master/Slave flag   
*                         - I2C_FLAG_ADSL: Adress matched flag    
*                         - I2C_FLAG_BTF: Byte transfer finished flag    
*                         - I2C_FLAG_BUSY: Bus busy flag    
*                         - I2C_FLAG_TRA: Transmitter/Receiver flag    
*                         - I2C_FLAG_ADD10: 10-bit addressing in Master mode flag   
*                         - I2C_FLAG_EVF: Event flag     
*                         - I2C_FLAG_GCAL: General call flag    
*                         - I2C_FLAG_BERR: Bus error flag    
*                         - I2C_FLAG_ARLO: Arbitration lost flag    
*                         - I2C_FLAG_STOPF: Stop detection flag   
*                         - I2C_FLAG_AF: Acknowledge failure flag      
*                         - I2C_FLAG_ENDAD: End of address transmission flag   
*                         - I2C_FLAG_ACK: Acknowledge enable flag             
*                  - parameter needed in the case that the flag to be cleared
*                    need a write in one register  
* Output         : None	                                             
* Return         : None                                                      
*******************************************************************************/
void I2C_ClearFlag(u16 I2C_FLAG, ...)
{
  u8 Tmp = (u8)*((u32 *) & I2C_FLAG + sizeof(I2C_FLAG));

  /* flags that need a read of the SR2 register to be cleared */
  if ((I2C_FLAG == I2C_FLAG_ADD10) || (I2C_FLAG == I2C_FLAG_EVF) ||
      (I2C_FLAG == I2C_FLAG_STOPF) || (I2C_FLAG == I2C_FLAG_AF)  || 
      (I2C_FLAG == I2C_FLAG_BERR) ||  (I2C_FLAG == I2C_FLAG_ARLO) ||
      (I2C_FLAG == I2C_FLAG_ENDAD))
  {
    /* Read the SR2 register */
    (void)I2C->SR2;

    /* Two flags need a second step to be cleared */
    switch (I2C_FLAG)
    {
       case  I2C_FLAG_ADD10:
         /* Send the MSB 10bit address passed as second parameter */
         I2C->DR = Tmp; 
         break;
       case  I2C_FLAG_ENDAD: 
         /* Write to the I2C_CR register by setting PE bit */
         I2C->CR |= I2C_PE_Set;
         break;
    }
  }
  /* flags that need a read of the SR1 register to be cleared */
  else if (I2C_FLAG==I2C_FLAG_SB || I2C_FLAG==I2C_FLAG_ADSL || I2C_FLAG==I2C_FLAG_BTF || I2C_FLAG==I2C_FLAG_TRA)
  {
    /* Read the SR1 register */
    (void)I2C->SR1;

    /* three flags need a second step to be cleared */
    if (I2C_FLAG == I2C_FLAG_SB)
    {
      /* Send the address byte passed as second parameter */
      I2C->DR=Tmp;
    }
    else if (I2C_FLAG==I2C_FLAG_BTF || I2C_FLAG==I2C_FLAG_TRA)
    {
      /* return the received byte in the variable passed as second parameter  */
      Tmp=I2C->DR;
    }
  }
  /* flags that need to disable the I2C interface */
  else if ( I2C_FLAG==I2C_FLAG_M_SL || I2C_FLAG==I2C_FLAG_GCAL)
  {
    I2C_Cmd(DISABLE);
    I2C_Cmd(ENABLE);
  }
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
