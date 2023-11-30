/**
  ******************************************************************************
  * @file    stm32f7xx_hal_uart.c
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   UART HAL module driver.
  *
  *          This file provides firmware functions to manage the following 
  *          functionalities of the Universal Asynchronous Receiver Transmitter (UART) peripheral:
  *           + Initialization and de-initialization functions
  *           + IO operation functions
  *           + Peripheral Control functions  
  *           + Peripheral State and Errors functions  
  *           
  @verbatim       
  ==============================================================================
                        ##### How to use this driver #####
  ==============================================================================
  [..]
    The UART HAL driver can be used as follows:
    
    (#) Declare a UART_HandleTypeDef handle structure.
  
    (#) Initialize the UART low level resources by implementing the HAL_UART_MspInit() API:
        (##) Enable the USARTx interface clock.
        (##) UART pins configuration:
            (+++) Enable the clock for the UART GPIOs.
            (+++) Configure these UART pins as alternate function pull-up.
        (##) NVIC configuration if you need to use interrupt process (HAL_UART_Transmit_IT()
             and HAL_UART_Receive_IT() APIs):
            (+++) Configure the USARTx interrupt priority.
            (+++) Enable the NVIC USART IRQ handle.
        (##) DMA Configuration if you need to use DMA process (HAL_UART_Transmit_DMA()
             and HAL_UART_Receive_DMA() APIs):
            (+++) Declare a DMA handle structure for the Tx/Rx stream.
            (+++) Enable the DMAx interface clock.
            (+++) Configure the declared DMA handle structure with the required 
                  Tx/Rx parameters.                
            (+++) Configure the DMA Tx/Rx Stream.
            (+++) Associate the initialized DMA handle to the UART DMA Tx/Rx handle.
            (+++) Configure the priority and enable the NVIC for the transfer complete 
                  interrupt on the DMA Tx/Rx Stream.

    (#) Program the Baud Rate, Word Length, Stop Bit, Parity, Hardware 
        flow control and Mode(Receiver/Transmitter) in the Init structure.

    (#) For the UART asynchronous mode, initialize the UART registers by calling
        the HAL_UART_Init() API.
    
    (#) For the UART Half duplex mode, initialize the UART registers by calling 
        the HAL_HalfDuplex_Init() API.
    
    (#) For the LIN mode, initialize the UART registers by calling the HAL_LIN_Init() API.
    
    (#) For the Multi-Processor mode, initialize the UART registers by calling 
        the HAL_MultiProcessor_Init() API.
        
     [..] 
       (@) The specific UART interrupts (Transmission complete interrupt, 
            RXNE interrupt and Error Interrupts) will be managed using the macros
            __HAL_UART_ENABLE_IT() and __HAL_UART_DISABLE_IT() inside the transmit 
            and receive process.
          
     [..] 
       (@) These APIs (HAL_UART_Init() and HAL_HalfDuplex_Init()) configure also the 
            low level Hardware GPIO, CLOCK, CORTEX...etc) by calling the customized 
            HAL_UART_MspInit() API.
          
     [..] 
        Three operation modes are available within this driver :     
  
     *** Polling mode IO operation ***
     =================================
     [..]    
       (+) Send an amount of data in blocking mode using HAL_UART_Transmit() 
       (+) Receive an amount of data in blocking mode using HAL_UART_Receive()
       
     *** Interrupt mode IO operation ***    
     ===================================
     [..]    
       (+) Send an amount of data in non blocking mode using HAL_UART_Transmit_IT() 
       (+) At transmission end of transfer HAL_UART_TxCpltCallback is executed and user can 
            add his own code by customization of function pointer HAL_UART_TxCpltCallback
       (+) Receive an amount of data in non blocking mode using HAL_UART_Receive_IT() 
       (+) At reception end of transfer HAL_UART_RxCpltCallback is executed and user can 
            add his own code by customization of function pointer HAL_UART_RxCpltCallback
       (+) In case of transfer Error, HAL_UART_ErrorCallback() function is executed and user can 
            add his own code by customization of function pointer HAL_UART_ErrorCallback

     *** DMA mode IO operation ***    
     ==============================
     [..] 
       (+) Send an amount of data in non blocking mode (DMA) using HAL_UART_Transmit_DMA() 
       (+) At transmission end of half transfer HAL_UART_TxHalfCpltCallback is executed and user can 
            add his own code by customization of function pointer HAL_UART_TxHalfCpltCallback 
       (+) At transmission end of transfer HAL_UART_TxCpltCallback is executed and user can 
            add his own code by customization of function pointer HAL_UART_TxCpltCallback
       (+) Receive an amount of data in non blocking mode (DMA) using HAL_UART_Receive_DMA() 
       (+) At reception end of half transfer HAL_UART_RxHalfCpltCallback is executed and user can 
            add his own code by customization of function pointer HAL_UART_RxHalfCpltCallback 
       (+) At reception end of transfer HAL_UART_RxCpltCallback is executed and user can 
            add his own code by customization of function pointer HAL_UART_RxCpltCallback
       (+) In case of transfer Error, HAL_UART_ErrorCallback() function is executed and user can 
            add his own code by customization of function pointer HAL_UART_ErrorCallback
       (+) Pause the DMA Transfer using HAL_UART_DMAPause()      
       (+) Resume the DMA Transfer using HAL_UART_DMAResume()  
       (+) Stop the DMA Transfer using HAL_UART_DMAStop()      
    
     *** UART HAL driver macros list ***
     ============================================= 
     [..]
       Below the list of most used macros in UART HAL driver.
       
      (+) __HAL_UART_ENABLE: Enable the UART peripheral 
      (+) __HAL_UART_DISABLE: Disable the UART peripheral     
      (+) __HAL_UART_GET_FLAG : Check whether the specified UART flag is set or not
      (+) __HAL_UART_CLEAR_IT : Clears the specified UART ISR flag
      (+) __HAL_UART_ENABLE_IT: Enable the specified UART interrupt
      (+) __HAL_UART_DISABLE_IT: Disable the specified UART interrupt
      (+) __HAL_UART_GET_IT_SOURCE: Check whether the specified UART interrupt has occurred or not
      
     [..] 
       (@) You can refer to the UART HAL driver header file for more useful macros 
      
  @endverbatim
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2015 STMicroelectronics</center></h2>
  *
  * Redistribution and use in source and binary forms, with or without modification,
  * are permitted provided that the following conditions are met:
  *   1. Redistributions of source code must retain the above copyright notice,
  *      this list of conditions and the following disclaimer.
  *   2. Redistributions in binary form must reproduce the above copyright notice,
  *      this list of conditions and the following disclaimer in the documentation
  *      and/or other materials provided with the distribution.
  *   3. Neither the name of STMicroelectronics nor the names of its contributors
  *      may be used to endorse or promote products derived from this software
  *      without specific prior written permission.
  *
  * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  *
  ******************************************************************************
  */ 

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal.h"

/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */

/** @defgroup UART UART
  * @brief HAL UART module driver
  * @{
  */
#ifdef HAL_UART_MODULE_ENABLED
    
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define HAL_UART_TXDMA_TIMEOUTVALUE                      22000
#define UART_CR1_FIELDS  ((uint32_t)(USART_CR1_M | USART_CR1_PCE | USART_CR1_PS | \
                                     USART_CR1_TE | USART_CR1_RE | USART_CR1_OVER8))
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
static void UART_DMATransmitCplt(DMA_HandleTypeDef *hdma);
static void UART_DMAReceiveCplt(DMA_HandleTypeDef *hdma);
static void UART_DMARxHalfCplt(DMA_HandleTypeDef *hdma);
static void UART_DMATxHalfCplt(DMA_HandleTypeDef *hdma);
static void UART_DMAError(DMA_HandleTypeDef *hdma); 
static HAL_StatusTypeDef UART_Transmit_IT(UART_HandleTypeDef *huart);
static HAL_StatusTypeDef UART_EndTransmit_IT(UART_HandleTypeDef *huart);
static HAL_StatusTypeDef UART_Receive_IT(UART_HandleTypeDef *huart);
/* Private functions ---------------------------------------------------------*/

/** @defgroup UART_Exported_Functions UART Exported Functions
  * @{
  */

/** @defgroup UART_Exported_Functions_Group1 Initialization and de-initialization functions 
  *  @brief    Initialization and Configuration functions 
  *
@verbatim    
===============================================================================
            ##### Initialization and Configuration functions #####
 ===============================================================================
    [..]
    This subsection provides a set of functions allowing to initialize the USARTx or the UARTy 
    in asynchronous mode.
      (+) For the asynchronous mode only these parameters can be configured: 
        (++) Baud Rate
        (++) Word Length 
        (++) Stop Bit
        (++) Parity: If the parity is enabled, then the MSB bit of the data written
             in the data register is transmitted but is changed by the parity bit.
             Depending on the frame length defined by the M bit (8-bits or 9-bits),
             please refer to Reference manual for possible UART frame formats.           
        (++) Hardware flow control
        (++) Receiver/transmitter modes
        (++) Over Sampling Method
    [..]
    The HAL_UART_Init(), HAL_HalfDuplex_Init(), HAL_LIN_Init() and HAL_MultiProcessor_Init() APIs 
    follow respectively the UART asynchronous, UART Half duplex, LIN and Multi-Processor
    configuration procedures (details for the procedures are available in reference manual (RM0329)).

@endverbatim
  * @{
  */

/**
  * @brief Initializes the UART mode according to the specified
  *         parameters in the UART_InitTypeDef and creates the associated handle .
  * @param huart: uart handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_Init(UART_HandleTypeDef *huart)
{
  /* Check the UART handle allocation */
  if(huart == NULL)
  {
    return HAL_ERROR;
  }
  
  if(huart->Init.HwFlowCtl != UART_HWCONTROL_NONE)
  {
    /* Check the parameters */
    assert_param(IS_UART_HWFLOW_INSTANCE(huart->Instance));
  }
  else
  {
    /* Check the parameters */
    assert_param(IS_UART_INSTANCE(huart->Instance));
  }
  
  if(huart->State == HAL_UART_STATE_RESET)
  {
    /* Allocate lock resource and initialize it */
    huart->Lock = HAL_UNLOCKED;

    /* Init the low level hardware : GPIO, CLOCK */
    HAL_UART_MspInit(huart);
  }

  huart->State = HAL_UART_STATE_BUSY;

  /* Disable the Peripheral */
  __HAL_UART_DISABLE(huart);
  
  /* Set the UART Communication parameters */
  if (UART_SetConfig(huart) == HAL_ERROR)
  {
    return HAL_ERROR;
  }

  if (huart->AdvancedInit.AdvFeatureInit != UART_ADVFEATURE_NO_INIT)
  {
    UART_AdvFeatureConfig(huart);
  }

  /* In asynchronous mode, the following bits must be kept cleared:
  - LINEN and CLKEN bits in the USART_CR2 register,
  - SCEN, HDSEL and IREN  bits in the USART_CR3 register.*/
  huart->Instance->CR2 &= ~(USART_CR2_LINEN | USART_CR2_CLKEN);
  huart->Instance->CR3 &= ~(USART_CR3_SCEN | USART_CR3_HDSEL | USART_CR3_IREN);

  /* Enable the Peripheral */
  __HAL_UART_ENABLE(huart);

  /* TEACK and/or REACK to check before moving huart->State to Ready */
  return (UART_CheckIdleState(huart));
}

/**
  * @brief Initializes the half-duplex mode according to the specified
  *         parameters in the UART_InitTypeDef and creates the associated handle .
  * @param huart: UART handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_HalfDuplex_Init(UART_HandleTypeDef *huart)
{
  /* Check the UART handle allocation */
  if(huart == NULL)
  {
    return HAL_ERROR;
  }
  
  if(huart->State == HAL_UART_STATE_RESET)
  {
    /* Allocate lock resource and initialize it */
    huart->Lock = HAL_UNLOCKED;
    /* Init the low level hardware : GPIO, CLOCK */
    HAL_UART_MspInit(huart);
  }

  huart->State = HAL_UART_STATE_BUSY;

  /* Disable the Peripheral */
  __HAL_UART_DISABLE(huart);

  /* Set the UART Communication parameters */
  if (UART_SetConfig(huart) == HAL_ERROR)
  {
    return HAL_ERROR;
  }

  if (huart->AdvancedInit.AdvFeatureInit != UART_ADVFEATURE_NO_INIT)
  {
    UART_AdvFeatureConfig(huart);
  }

  /* In half-duplex mode, the following bits must be kept cleared:
  - LINEN and CLKEN bits in the USART_CR2 register,
  - SCEN and IREN bits in the USART_CR3 register.*/
  huart->Instance->CR2 &= ~(USART_CR2_LINEN | USART_CR2_CLKEN);
  huart->Instance->CR3 &= ~(USART_CR3_IREN | USART_CR3_SCEN);

  /* Enable the Half-Duplex mode by setting the HDSEL bit in the CR3 register */
  huart->Instance->CR3 |= USART_CR3_HDSEL;

  /* Enable the Peripheral */
  __HAL_UART_ENABLE(huart);

  /* TEACK and/or REACK to check before moving huart->State to Ready */
  return (UART_CheckIdleState(huart));
}


/**
  * @brief Initializes the LIN mode according to the specified
  *         parameters in the UART_InitTypeDef and creates the associated handle .
  * @param huart: uart handle
  * @param BreakDetectLength: specifies the LIN break detection length.
  *        This parameter can be one of the following values:
  *          @arg UART_LINBREAKDETECTLENGTH_10B: 10-bit break detection
  *          @arg UART_LINBREAKDETECTLENGTH_11B: 11-bit break detection
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_LIN_Init(UART_HandleTypeDef *huart, uint32_t BreakDetectLength)
{
  /* Check the UART handle allocation */
  if(huart == NULL)
  {
    return HAL_ERROR;
  }

  /* Check the parameters */
  assert_param(IS_UART_INSTANCE(huart->Instance));
  assert_param(IS_UART_LIN_BREAK_DETECT_LENGTH(BreakDetectLength));
  assert_param(IS_LIN_WORD_LENGTH(huart->Init.WordLength));
  	
  if(huart->State == HAL_UART_STATE_RESET)
  {  
    /* Allocate lock resource and initialize it */
    huart->Lock = HAL_UNLOCKED; 
    /* Init the low level hardware : GPIO, CLOCK */
    HAL_UART_MspInit(huart);
  }
  
  huart->State = HAL_UART_STATE_BUSY;
  
  /* Disable the Peripheral */
  __HAL_UART_DISABLE(huart);
  
  /* Set the UART Communication parameters */
  if (UART_SetConfig(huart) == HAL_ERROR)
  {
    return HAL_ERROR;
  } 
  
  if (huart->AdvancedInit.AdvFeatureInit != UART_ADVFEATURE_NO_INIT)
  {
    UART_AdvFeatureConfig(huart);
  }
  
  /* In LIN mode, the following bits must be kept cleared: 
  - LINEN and CLKEN bits in the USART_CR2 register,
  - SCEN and IREN bits in the USART_CR3 register.*/
  huart->Instance->CR2 &= ~(USART_CR2_CLKEN);
  huart->Instance->CR3 &= ~(USART_CR3_HDSEL | USART_CR3_IREN | USART_CR3_SCEN);
  
  /* Enable the LIN mode by setting the LINEN bit in the CR2 register */
  huart->Instance->CR2 |= USART_CR2_LINEN;
  
  /* Set the USART LIN Break detection length. */
  MODIFY_REG(huart->Instance->CR2, USART_CR2_LBDL, BreakDetectLength);
  
    /* Enable the Peripheral */
  __HAL_UART_ENABLE(huart);
  
  /* TEACK and/or REACK to check before moving huart->State to Ready */
  return (UART_CheckIdleState(huart));
}



/**
  * @brief Initializes the multiprocessor mode according to the specified
  *         parameters in the UART_InitTypeDef and creates the associated handle.
  * @param huart: UART handle   
  * @param Address: UART node address (4-, 6-, 7- or 8-bit long)
  * @param WakeUpMethod: specifies the UART wakeup method.
  *        This parameter can be one of the following values:
  *          @arg UART_WAKEUPMETHOD_IDLELINE: WakeUp by an idle line detection
  *          @arg UART_WAKEUPMETHOD_ADDRESSMARK: WakeUp by an address mark
  * @note  If the user resorts to idle line detection wake up, the Address parameter
  *        is useless and ignored by the initialization function.               
  * @note  If the user resorts to address mark wake up, the address length detection 
  *        is configured by default to 4 bits only. For the UART to be able to 
  *        manage 6-, 7- or 8-bit long addresses detection                    
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_MultiProcessor_Init(UART_HandleTypeDef *huart, uint8_t Address, uint32_t WakeUpMethod)
{
  /* Check the UART handle allocation */
  if(huart == NULL)
  {
    return HAL_ERROR;
  }

  /* Check the wake up method parameter */
  assert_param(IS_UART_WAKEUPMETHOD(WakeUpMethod));
  
  if(huart->State == HAL_UART_STATE_RESET)
  { 
    /* Allocate lock resource and initialize it */
    huart->Lock = HAL_UNLOCKED;  
    /* Init the low level hardware : GPIO, CLOCK */
    HAL_UART_MspInit(huart);
  }
  
  huart->State = HAL_UART_STATE_BUSY;
  
  /* Disable the Peripheral */
  __HAL_UART_DISABLE(huart);
  
  /* Set the UART Communication parameters */
  if (UART_SetConfig(huart) == HAL_ERROR)
  {
    return HAL_ERROR;
  } 
  
  if (huart->AdvancedInit.AdvFeatureInit != UART_ADVFEATURE_NO_INIT)
  {
    UART_AdvFeatureConfig(huart);
  }
  
  /* In multiprocessor mode, the following bits must be kept cleared: 
  - LINEN and CLKEN bits in the USART_CR2 register,
  - SCEN, HDSEL and IREN  bits in the USART_CR3 register. */
  huart->Instance->CR2 &= ~(USART_CR2_LINEN | USART_CR2_CLKEN);
  huart->Instance->CR3 &= ~(USART_CR3_SCEN | USART_CR3_HDSEL | USART_CR3_IREN);
  
  if (WakeUpMethod == UART_WAKEUPMETHOD_ADDRESSMARK)
  {
    /* If address mark wake up method is chosen, set the USART address node */
    MODIFY_REG(huart->Instance->CR2, USART_CR2_ADD, ((uint32_t)Address << UART_CR2_ADDRESS_LSB_POS));
  }
  
  /* Set the wake up method by setting the WAKE bit in the CR1 register */
  MODIFY_REG(huart->Instance->CR1, USART_CR1_WAKE, WakeUpMethod);
  
  /* Enable the Peripheral */
  __HAL_UART_ENABLE(huart); 
  
  /* TEACK and/or REACK to check before moving huart->State to Ready */
  return (UART_CheckIdleState(huart));
}




/**
  * @brief DeInitializes the UART peripheral 
  * @param huart: uart handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_DeInit(UART_HandleTypeDef *huart)
{
  /* Check the UART handle allocation */
  if(huart == NULL)
  {
    return HAL_ERROR;
  }
  
  /* Check the parameters */
  assert_param(IS_UART_INSTANCE(huart->Instance));

  huart->State = HAL_UART_STATE_BUSY;
  
  /* Disable the Peripheral */
  __HAL_UART_DISABLE(huart);
  
  huart->Instance->CR1 = 0x0;
  huart->Instance->CR2 = 0x0;
  huart->Instance->CR3 = 0x0;
  
  /* DeInit the low level hardware */
  HAL_UART_MspDeInit(huart);

  huart->ErrorCode = HAL_UART_ERROR_NONE;
  huart->State = HAL_UART_STATE_RESET;
  
  /* Process Unlock */
  __HAL_UNLOCK(huart);
  
  return HAL_OK;
}

/**
  * @brief UART MSP Init
  * @param huart: uart handle
  * @retval None
  */
 __weak void HAL_UART_MspInit(UART_HandleTypeDef *huart)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_UART_MspInit can be implemented in the user file
   */ 
}

/**
  * @brief UART MSP DeInit
  * @param huart: uart handle
  * @retval None
  */
 __weak void HAL_UART_MspDeInit(UART_HandleTypeDef *huart)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_UART_MspDeInit can be implemented in the user file
   */ 
}

/**
  * @}
  */

/** @defgroup UART_Exported_Functions_Group2 IO operation functions 
  *  @brief UART Transmit/Receive functions 
  *
@verbatim   
 ===============================================================================
                      ##### I/O operation functions #####
 ===============================================================================
    This subsection provides a set of functions allowing to manage the UART asynchronous
    and Half duplex data transfers.

    (#) There are two mode of transfer:
       (+) Blocking mode: The communication is performed in polling mode. 
            The HAL status of all data processing is returned by the same function 
            after finishing transfer.  
       (+) No-Blocking mode: The communication is performed using Interrupts 
           or DMA, These API's return the HAL status.
           The end of the data processing will be indicated through the 
           dedicated UART IRQ when using Interrupt mode or the DMA IRQ when 
           using DMA mode.
           The HAL_UART_TxCpltCallback(), HAL_UART_RxCpltCallback() user callbacks 
           will be executed respectively at the end of the transmit or Receive process
           The HAL_UART_ErrorCallback()user callback will be executed when a communication error is detected

    (#) Blocking mode API's are :
        (+) HAL_UART_Transmit()
        (+) HAL_UART_Receive() 
        
    (#) Non-Blocking mode API's with Interrupt are :
        (+) HAL_UART_Transmit_IT()
        (+) HAL_UART_Receive_IT()
        (+) HAL_UART_IRQHandler()
        (+) UART_Transmit_IT()
        (+) UART_Receive_IT()

    (#) No-Blocking mode API's with DMA are :
        (+) HAL_UART_Transmit_DMA()
        (+) HAL_UART_Receive_DMA()
        (+) HAL_UART_DMAPause()
        (+) HAL_UART_DMAResume()
        (+) HAL_UART_DMAStop()

    (#) A set of Transfer Complete Callbacks are provided in No_Blocking mode:
        (+) HAL_UART_TxHalfCpltCallback()
        (+) HAL_UART_TxCpltCallback()
        (+) HAL_UART_RxHalfCpltCallback()
        (+) HAL_UART_RxCpltCallback()
        (+) HAL_UART_ErrorCallback()


    -@- In the Half duplex communication, it is forbidden to run the transmit 
        and receive process in parallel, the UART state HAL_UART_STATE_BUSY_TX_RX can't be useful.

@endverbatim
  * @{
  */

/**
  * @brief Send an amount of data in blocking mode 
  * @param huart: uart handle
  * @param pData: pointer to data buffer
  * @param Size: amount of data to be sent
  * @param Timeout : Timeout duration
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_Transmit(UART_HandleTypeDef *huart, uint8_t *pData, uint16_t Size, uint32_t Timeout)
{
   uint16_t* tmp;

  if((huart->State == HAL_UART_STATE_READY) || (huart->State == HAL_UART_STATE_BUSY_RX))
  {
    if((pData == NULL ) || (Size == 0))
    {
      return  HAL_ERROR;
    }

    /* Process Locked */
    __HAL_LOCK(huart);

    huart->ErrorCode = HAL_UART_ERROR_NONE;
    /* Check if a non-blocking receive process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_RX) 
    {
      huart->State = HAL_UART_STATE_BUSY_TX_RX;
    }
    else
    {
      huart->State = HAL_UART_STATE_BUSY_TX;
    }

    huart->TxXferSize = Size;
    huart->TxXferCount = Size;
    while(huart->TxXferCount > 0)
    {
      huart->TxXferCount--;
        if(UART_WaitOnFlagUntilTimeout(huart, UART_FLAG_TXE, RESET, Timeout) != HAL_OK)  
        { 
          return HAL_TIMEOUT;
        }
      if ((huart->Init.WordLength == UART_WORDLENGTH_9B) && (huart->Init.Parity == UART_PARITY_NONE))
      {
        tmp = (uint16_t*) pData;
        huart->Instance->TDR = (*tmp & (uint16_t)0x01FF);
        pData += 2;
      }
      else
      {
        huart->Instance->TDR = (*pData++ & (uint8_t)0xFF);
      }
    }
    if(UART_WaitOnFlagUntilTimeout(huart, UART_FLAG_TC, RESET, Timeout) != HAL_OK)  
    { 
      return HAL_TIMEOUT;
    }
    /* Check if a non-blocking receive Process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_TX_RX) 
    {
      huart->State = HAL_UART_STATE_BUSY_RX;
    }
    else
    {
      huart->State = HAL_UART_STATE_READY;
    }

    /* Process Unlocked */
    __HAL_UNLOCK(huart);

    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;
  }
}

/**
  * @brief Receive an amount of data in blocking mode 
  * @param huart: uart handle
  * @param pData: pointer to data buffer
  * @param Size: amount of data to be received
  * @param Timeout : Timeout duration
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_Receive(UART_HandleTypeDef *huart, uint8_t *pData, uint16_t Size, uint32_t Timeout)
{
  uint16_t* tmp;
  uint16_t uhMask;

  if((huart->State == HAL_UART_STATE_READY) || (huart->State == HAL_UART_STATE_BUSY_TX))
  {
    if((pData == NULL ) || (Size == 0))
    {
      return  HAL_ERROR;
    }

    /* Process Locked */
    __HAL_LOCK(huart);

    huart->ErrorCode = HAL_UART_ERROR_NONE;
    /* Check if a non-blocking transmit process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_TX)
    {
      huart->State = HAL_UART_STATE_BUSY_TX_RX;
    }
    else
    {
      huart->State = HAL_UART_STATE_BUSY_RX;
    }

    huart->RxXferSize = Size; 
    huart->RxXferCount = Size;

    /* Computation of UART mask to apply to RDR register */
    UART_MASK_COMPUTATION(huart);
    uhMask = huart->Mask;

    /* as long as data have to be received */
    while(huart->RxXferCount > 0)
    {
      huart->RxXferCount--;
        if(UART_WaitOnFlagUntilTimeout(huart, UART_FLAG_RXNE, RESET, Timeout) != HAL_OK)  
        {
          return HAL_TIMEOUT;
        }
      if ((huart->Init.WordLength == UART_WORDLENGTH_9B) && (huart->Init.Parity == UART_PARITY_NONE))
      {
        tmp = (uint16_t*) pData ;
        *tmp = (uint16_t)(huart->Instance->RDR & uhMask);
        pData +=2; 
      }
      else
      {
        *pData++ = (uint8_t)(huart->Instance->RDR & (uint8_t)uhMask); 
      }
    }

    /* Check if a non-blocking transmit Process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_TX_RX) 
    {
      huart->State = HAL_UART_STATE_BUSY_TX;
    }
    else
    {
      huart->State = HAL_UART_STATE_READY;
    }
    /* Process Unlocked */
    __HAL_UNLOCK(huart);

    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;
  }
}

/**
  * @brief Send an amount of data in interrupt mode 
  * @param huart: uart handle
  * @param pData: pointer to data buffer
  * @param Size: amount of data to be sent
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_Transmit_IT(UART_HandleTypeDef *huart, uint8_t *pData, uint16_t Size)
{  
  if((huart->State == HAL_UART_STATE_READY) || (huart->State == HAL_UART_STATE_BUSY_RX))
  {
    if((pData == NULL ) || (Size == 0)) 
    {
      return HAL_ERROR;
    }
    
    /* Process Locked */
    __HAL_LOCK(huart);
    
    huart->pTxBuffPtr = pData;
    huart->TxXferSize = Size;
    huart->TxXferCount = Size;
    
    huart->ErrorCode = HAL_UART_ERROR_NONE;
    /* Check if a receive process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_RX) 
    {
      huart->State = HAL_UART_STATE_BUSY_TX_RX;
    }
    else
    {
      huart->State = HAL_UART_STATE_BUSY_TX;
    }
    
    /* Enable the UART Error Interrupt: (Frame error, noise error, overrun error) */
    __HAL_UART_ENABLE_IT(huart, UART_IT_ERR);
    
    /* Process Unlocked */
    __HAL_UNLOCK(huart);    
    
    /* Enable the UART Transmit Data Register Empty Interrupt */
    __HAL_UART_ENABLE_IT(huart, UART_IT_TXE);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;   
  }
}

/**
  * @brief Receive an amount of data in interrupt mode 
  * @param huart: uart handle
  * @param pData: pointer to data buffer
  * @param Size: amount of data to be received
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_Receive_IT(UART_HandleTypeDef *huart, uint8_t *pData, uint16_t Size)
{
  if((huart->State == HAL_UART_STATE_READY) || (huart->State == HAL_UART_STATE_BUSY_TX))
  {
    if((pData == NULL ) || (Size == 0)) 
    {
      return HAL_ERROR;
    }

    /* Process Locked */
    __HAL_LOCK(huart);

    huart->pRxBuffPtr = pData;
    huart->RxXferSize = Size;
    huart->RxXferCount = Size;

    /* Computation of UART mask to apply to RDR register */
    UART_MASK_COMPUTATION(huart);

    huart->ErrorCode = HAL_UART_ERROR_NONE;
    /* Check if a transmit process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_TX) 
    {
      huart->State = HAL_UART_STATE_BUSY_TX_RX;
    }
    else
    {
      huart->State = HAL_UART_STATE_BUSY_RX;
    }

    /* Enable the UART Parity Error Interrupt */
    __HAL_UART_ENABLE_IT(huart, UART_IT_PE);

    /* Enable the UART Error Interrupt: (Frame error, noise error, overrun error) */
    __HAL_UART_ENABLE_IT(huart, UART_IT_ERR);

    /* Process Unlocked */
    __HAL_UNLOCK(huart);

    /* Enable the UART Data Register not empty Interrupt */
    __HAL_UART_ENABLE_IT(huart, UART_IT_RXNE);

    return HAL_OK;
  }
  else
  {
    return HAL_BUSY; 
  }
}

/**
  * @brief Send an amount of data in DMA mode 
  * @param huart: uart handle
  * @param pData: pointer to data buffer
  * @param Size: amount of data to be sent
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_Transmit_DMA(UART_HandleTypeDef *huart, uint8_t *pData, uint16_t Size)
{
  uint32_t *tmp;
  
  if((huart->State == HAL_UART_STATE_READY) || (huart->State == HAL_UART_STATE_BUSY_RX))
  {
    if((pData == NULL ) || (Size == 0)) 
    {
      return HAL_ERROR;
    }
    
    /* Process Locked */
    __HAL_LOCK(huart);
    
    huart->pTxBuffPtr = pData;
    huart->TxXferSize = Size;
    huart->TxXferCount = Size; 
    
    huart->ErrorCode = HAL_UART_ERROR_NONE;
    /* Check if a receive process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_RX) 
    {
      huart->State = HAL_UART_STATE_BUSY_TX_RX;
    }
    else
    {
      huart->State = HAL_UART_STATE_BUSY_TX;
    }
    
    /* Set the UART DMA transfer complete callback */
    huart->hdmatx->XferCpltCallback = UART_DMATransmitCplt;
    
    /* Set the UART DMA Half transfer complete callback */
    huart->hdmatx->XferHalfCpltCallback = UART_DMATxHalfCplt;
    
    /* Set the DMA error callback */
    huart->hdmatx->XferErrorCallback = UART_DMAError;

    /* Enable the UART transmit DMA channel */
    tmp = (uint32_t*)&pData;
    HAL_DMA_Start_IT(huart->hdmatx, *(uint32_t*)tmp, (uint32_t)&huart->Instance->TDR, Size);

    /* Clear the TC flag in the SR register by writing 0 to it */
    __HAL_UART_CLEAR_IT(huart, UART_FLAG_TC);

    
    /* Enable the DMA transfer for transmit request by setting the DMAT bit
       in the UART CR3 register */
    huart->Instance->CR3 |= USART_CR3_DMAT;
    
    /* Process Unlocked */
    __HAL_UNLOCK(huart);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;   
  }
}

/**
  * @brief Receive an amount of data in DMA mode 
  * @param huart: uart handle
  * @param pData: pointer to data buffer
  * @param Size: amount of data to be received
  * @note   When the UART parity is enabled (PCE = 1), the received data contain 
  *         the parity bit (MSB position)     
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_UART_Receive_DMA(UART_HandleTypeDef *huart, uint8_t *pData, uint16_t Size)
{
  uint32_t *tmp;
  
  if((huart->State == HAL_UART_STATE_READY) || (huart->State == HAL_UART_STATE_BUSY_TX))
  {
    if((pData == NULL ) || (Size == 0)) 
    {
      return HAL_ERROR;
    }
    
    /* Process Locked */
    __HAL_LOCK(huart);
    
    huart->pRxBuffPtr = pData;
    huart->RxXferSize = Size;
    
    huart->ErrorCode = HAL_UART_ERROR_NONE;
    /* Check if a transmit process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_TX) 
    {
      huart->State = HAL_UART_STATE_BUSY_TX_RX;
    }
    else
    {
      huart->State = HAL_UART_STATE_BUSY_RX;
    }
    
    /* Set the UART DMA transfer complete callback */
    huart->hdmarx->XferCpltCallback = UART_DMAReceiveCplt;
    
    /* Set the UART DMA Half transfer complete callback */
    huart->hdmarx->XferHalfCpltCallback = UART_DMARxHalfCplt;
    
    /* Set the DMA error callback */
    huart->hdmarx->XferErrorCallback = UART_DMAError;

    /* Enable the DMA channel */
    tmp = (uint32_t*)&pData;
    HAL_DMA_Start_IT(huart->hdmarx, (uint32_t)&huart->Instance->RDR, *(uint32_t*)tmp, Size);

    /* Enable the DMA transfer for the receiver request by setting the DMAR bit 
       in the UART CR3 register */
     huart->Instance->CR3 |= USART_CR3_DMAR;
    
     /* Process Unlocked */
     __HAL_UNLOCK(huart);
     
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY; 
  }
}

/**
  * @brief Pauses the DMA Transfer.
  * @param huart: UART handle
  * @retval None
  */
HAL_StatusTypeDef HAL_UART_DMAPause(UART_HandleTypeDef *huart)
{
  /* Process Locked */
  __HAL_LOCK(huart);
  
  if(huart->State == HAL_UART_STATE_BUSY_TX)
  {
    /* Disable the UART DMA Tx request */
    huart->Instance->CR3 &= (uint32_t)(~USART_CR3_DMAT);
  }
  else if(huart->State == HAL_UART_STATE_BUSY_RX)
  {
    /* Disable the UART DMA Rx request */
    huart->Instance->CR3 &= (uint32_t)(~USART_CR3_DMAR);
  }
  else if(huart->State == HAL_UART_STATE_BUSY_TX_RX)
  {
    /* Disable the UART DMA Tx request */
    huart->Instance->CR3 &= (uint32_t)(~USART_CR3_DMAT);
    /* Disable the UART DMA Rx request */
    huart->Instance->CR3 &= (uint32_t)(~USART_CR3_DMAR);
  }
  
  /* Process Unlocked */
  __HAL_UNLOCK(huart);

  return HAL_OK; 
}

/**
  * @brief Resumes the DMA Transfer.
  * @param huart: UART handle
  * @retval None
  */
HAL_StatusTypeDef HAL_UART_DMAResume(UART_HandleTypeDef *huart)
{
  /* Process Locked */
  __HAL_LOCK(huart);

  if(huart->State == HAL_UART_STATE_BUSY_TX)
  {
    /* Enable the UART DMA Tx request */
    huart->Instance->CR3 |= USART_CR3_DMAT;
  }
  else if(huart->State == HAL_UART_STATE_BUSY_RX)
  {
    /* Enable the UART DMA Rx request */
    huart->Instance->CR3 |= USART_CR3_DMAR;
  }
  else if(huart->State == HAL_UART_STATE_BUSY_TX_RX)
  {
    /* Enable the UART DMA Rx request  before the DMA Tx request */
    huart->Instance->CR3 |= USART_CR3_DMAR;
    /* Enable the UART DMA Tx request */
    huart->Instance->CR3 |= USART_CR3_DMAT;
  }

  /* If the UART peripheral is still not enabled, enable it */
  if ((huart->Instance->CR1 & USART_CR1_UE) == 0)
  {
    /* Enable UART peripheral */
    __HAL_UART_ENABLE(huart);
  }

  /* TEACK and/or REACK to check before moving huart->State to Ready */
  return (UART_CheckIdleState(huart));
}

/**
  * @brief Stops the DMA Transfer.
  * @param huart: UART handle
  * @retval None
  */
HAL_StatusTypeDef HAL_UART_DMAStop(UART_HandleTypeDef *huart)
{
  /* Process Locked */
  __HAL_LOCK(huart);
  
  /* Disable the UART Tx/Rx DMA requests */
  huart->Instance->CR3 &= ~USART_CR3_DMAT;
  huart->Instance->CR3 &= ~USART_CR3_DMAR;
  
  /* Abort the UART DMA tx channel */
  if(huart->hdmatx != NULL)
  {
    HAL_DMA_Abort(huart->hdmatx);
  }
  /* Abort the UART DMA rx channel */
  if(huart->hdmarx != NULL)
  {
    HAL_DMA_Abort(huart->hdmarx);
  }
  
  /* Disable UART peripheral */
  __HAL_UART_DISABLE(huart);
  
  huart->State = HAL_UART_STATE_READY;
  
  /* Process Unlocked */
  __HAL_UNLOCK(huart);
  
  return HAL_OK;
}

/**
  * @brief This function handles UART interrupt request.
  * @param huart: uart handle
  * @retval None
  */
void HAL_UART_IRQHandler(UART_HandleTypeDef *huart)
{
  /* UART parity error interrupt occurred -------------------------------------*/
  if((__HAL_UART_GET_IT(huart, UART_IT_PE) != RESET) && (__HAL_UART_GET_IT_SOURCE(huart, UART_IT_PE) != RESET))
  { 
		__HAL_UART_CLEAR_PEFLAG(huart);

    huart->ErrorCode |= HAL_UART_ERROR_PE;
    /* Set the UART state ready to be able to start again the process */
    huart->State = HAL_UART_STATE_READY;
  }
  
  /* UART frame error interrupt occurred --------------------------------------*/
  if((__HAL_UART_GET_IT(huart, UART_IT_FE) != RESET) && (__HAL_UART_GET_IT_SOURCE(huart, UART_IT_ERR) != RESET))
  { 
    __HAL_UART_CLEAR_FEFLAG(huart);

    huart->ErrorCode |= HAL_UART_ERROR_FE;
    /* Set the UART state ready to be able to start again the process */
    huart->State = HAL_UART_STATE_READY;
  }
  
  /* UART noise error interrupt occurred --------------------------------------*/
  if((__HAL_UART_GET_IT(huart, UART_IT_NE) != RESET) && (__HAL_UART_GET_IT_SOURCE(huart, UART_IT_ERR) != RESET))
  { 
    __HAL_UART_CLEAR_NEFLAG(huart);

    huart->ErrorCode |= HAL_UART_ERROR_NE;
    /* Set the UART state ready to be able to start again the process */
    huart->State = HAL_UART_STATE_READY;
  }
  
  /* UART Over-Run interrupt occurred -----------------------------------------*/
  if((__HAL_UART_GET_IT(huart, UART_IT_ORE) != RESET) && (__HAL_UART_GET_IT_SOURCE(huart, UART_IT_ERR) != RESET))
  { 
    __HAL_UART_CLEAR_OREFLAG(huart);

    huart->ErrorCode |= HAL_UART_ERROR_ORE;
    /* Set the UART state ready to be able to start again the process */
    huart->State = HAL_UART_STATE_READY;
  }

   /* Call UART Error Call back function if need be --------------------------*/
  if(huart->ErrorCode != HAL_UART_ERROR_NONE)
  {
    HAL_UART_ErrorCallback(huart);
  }

  /* UART in mode Receiver ---------------------------------------------------*/
  if((__HAL_UART_GET_IT(huart, UART_IT_RXNE) != RESET) && (__HAL_UART_GET_IT_SOURCE(huart, UART_IT_RXNE) != RESET))
  { 
    UART_Receive_IT(huart);
    /* Clear RXNE interrupt flag */
    __HAL_UART_SEND_REQ(huart, UART_RXDATA_FLUSH_REQUEST);
  }
  

  /* UART in mode Transmitter ------------------------------------------------*/
 if((__HAL_UART_GET_IT(huart, UART_IT_TXE) != RESET) &&(__HAL_UART_GET_IT_SOURCE(huart, UART_IT_TXE) != RESET))
  {
    UART_Transmit_IT(huart);
  }

  /* UART in mode Transmitter (transmission end) -----------------------------*/
 if((__HAL_UART_GET_IT(huart, UART_IT_TC) != RESET) &&(__HAL_UART_GET_IT_SOURCE(huart, UART_IT_TC) != RESET))
  {
    UART_EndTransmit_IT(huart);
  }
  
}


/**
  * @brief  This function handles UART Communication Timeout.
  * @param  huart: UART handle
  * @param  Flag: specifies the UART flag to check.
  * @param  Status: The new Flag status (SET or RESET).
  * @param  Timeout: Timeout duration
  * @retval HAL status
  */
HAL_StatusTypeDef UART_WaitOnFlagUntilTimeout(UART_HandleTypeDef *huart, uint32_t Flag, FlagStatus Status, uint32_t Timeout)
{
  uint32_t tickstart = HAL_GetTick();
  
  /* Wait until flag is set */
  if(Status == RESET)
  {    
    while(__HAL_UART_GET_FLAG(huart, Flag) == RESET)
    {
      /* Check for the Timeout */
      if(Timeout != HAL_MAX_DELAY)
      {
        if((Timeout == 0)||((HAL_GetTick()-tickstart) >=  Timeout))
        {
          /* Disable TXE, RXNE, PE and ERR (Frame error, noise error, overrun error) interrupts for the interrupt process */
          __HAL_UART_DISABLE_IT(huart, UART_IT_TXE);
          __HAL_UART_DISABLE_IT(huart, UART_IT_RXNE);
          __HAL_UART_DISABLE_IT(huart, UART_IT_PE);
          __HAL_UART_DISABLE_IT(huart, UART_IT_ERR);
          
          huart->State= HAL_UART_STATE_READY;
          
          /* Process Unlocked */
          __HAL_UNLOCK(huart);
          
          return HAL_TIMEOUT;
        }
      }
    }
  }
  else
  {
    while(__HAL_UART_GET_FLAG(huart, Flag) != RESET)
    {
      /* Check for the Timeout */
      if(Timeout != HAL_MAX_DELAY)
      {
        if((Timeout == 0)||((HAL_GetTick()-tickstart) >=  Timeout))
        {
          /* Disable TXE, RXNE, PE and ERR (Frame error, noise error, overrun error) interrupts for the interrupt process */
          __HAL_UART_DISABLE_IT(huart, UART_IT_TXE);
          __HAL_UART_DISABLE_IT(huart, UART_IT_RXNE);
          __HAL_UART_DISABLE_IT(huart, UART_IT_PE);
          __HAL_UART_DISABLE_IT(huart, UART_IT_ERR);
          
          huart->State= HAL_UART_STATE_READY;
          
          /* Process Unlocked */
          __HAL_UNLOCK(huart);
          
          return HAL_TIMEOUT;
        }
      }
    }
  }
  return HAL_OK;      
}



/**
  * @brief DMA UART transmit process complete callback 
  * @param hdma: DMA handle
  * @retval None
  */
static void UART_DMATransmitCplt(DMA_HandleTypeDef *hdma)     
{
  UART_HandleTypeDef* huart = ( UART_HandleTypeDef* )((DMA_HandleTypeDef* )hdma)->Parent;
  
  /* DMA Normal mode*/
  if((hdma->Instance->CR & DMA_SxCR_CIRC) == 0)
  {
    huart->TxXferCount = 0;

    /* Disable the DMA transfer for transmit request by setting the DMAT bit
       in the UART CR3 register */
    huart->Instance->CR3 &= (uint32_t)~((uint32_t)USART_CR3_DMAT);

    /* Enable the UART Transmit Complete Interrupt */
    __HAL_UART_ENABLE_IT(huart, UART_IT_TC);
  }
  /* DMA Circular mode */
  else
  {
    HAL_UART_TxCpltCallback(huart);
  }
}

/**
  * @brief DMA UART transmit process half complete callback 
  * @param hdma : DMA handle
  * @retval None
  */
static void UART_DMATxHalfCplt(DMA_HandleTypeDef *hdma)
{
  UART_HandleTypeDef* huart = (UART_HandleTypeDef*)((DMA_HandleTypeDef*)hdma)->Parent;

  HAL_UART_TxHalfCpltCallback(huart);
}

/**
  * @brief DMA UART receive process complete callback 
  * @param hdma: DMA handle
  * @retval None
  */
static void UART_DMAReceiveCplt(DMA_HandleTypeDef *hdma)  
{
  UART_HandleTypeDef* huart = ( UART_HandleTypeDef* )((DMA_HandleTypeDef* )hdma)->Parent;
  
  /* DMA Normal mode */
  if((hdma->Instance->CR & DMA_SxCR_CIRC) == 0)
  { 
    huart->RxXferCount = 0;
    
    /* Disable the DMA transfer for the receiver request by setting the DMAR bit 
    in the UART CR3 register */
    huart->Instance->CR3 &= (uint32_t)~((uint32_t)USART_CR3_DMAR);
    
    /* Check if a transmit Process is ongoing or not */
    if(huart->State == HAL_UART_STATE_BUSY_TX_RX) 
    {
      huart->State = HAL_UART_STATE_BUSY_TX;
    }
    else
    {
      huart->State = HAL_UART_STATE_READY;
    }
  }
  HAL_UART_RxCpltCallback(huart);
}

/**
  * @brief DMA UART receive process half complete callback 
  * @param hdma : DMA handle
  * @retval None
  */
static void UART_DMARxHalfCplt(DMA_HandleTypeDef *hdma)
{
  UART_HandleTypeDef* huart = (UART_HandleTypeDef*)((DMA_HandleTypeDef*)hdma)->Parent;

  HAL_UART_RxHalfCpltCallback(huart); 
}

/**
  * @brief DMA UART communication error callback 
  * @param hdma: DMA handle
  * @retval None
  */
static void UART_DMAError(DMA_HandleTypeDef *hdma)   
{
  UART_HandleTypeDef* huart = ( UART_HandleTypeDef* )((DMA_HandleTypeDef* )hdma)->Parent;
  huart->RxXferCount = 0;
  huart->TxXferCount = 0;
  huart->State= HAL_UART_STATE_READY;
  huart->ErrorCode |= HAL_UART_ERROR_DMA;
  HAL_UART_ErrorCallback(huart);
}

/**
  * @brief Tx Transfer completed callbacks
  * @param huart: uart handle
  * @retval None
  */
 __weak void HAL_UART_TxCpltCallback(UART_HandleTypeDef *huart)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_UART_TxCpltCallback can be implemented in the user file
   */ 
}

/**
  * @brief  Tx Half Transfer completed callbacks.
  * @param  huart: UART handle
  * @retval None
  */
 __weak void HAL_UART_TxHalfCpltCallback(UART_HandleTypeDef *huart)
{
  /* NOTE: This function should not be modified, when the callback is needed,
           the HAL_UART_TxHalfCpltCallback can be implemented in the user file
   */ 
}

/**
  * @brief Rx Transfer completed callbacks
  * @param huart: uart handle
  * @retval None
  */
__weak void HAL_UART_RxCpltCallback(UART_HandleTypeDef *huart)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_UART_RxCpltCallback can be implemented in the user file
   */
}

/**
  * @brief  Rx Half Transfer completed callbacks.
  * @param  huart: UART handle
  * @retval None
  */
__weak void HAL_UART_RxHalfCpltCallback(UART_HandleTypeDef *huart)
{
  /* NOTE: This function should not be modified, when the callback is needed,
           the HAL_UART_RxHalfCpltCallback can be implemented in the user file
   */
}

/**
  * @brief UART error callbacks
  * @param huart: uart handle
  * @retval None
  */
 __weak void HAL_UART_ErrorCallback(UART_HandleTypeDef *huart)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_UART_ErrorCallback can be implemented in the user file
   */ 
}

/**
  * @brief Send an amount of data in interrupt mode 
  *         Function called under interruption only, once
  *         interruptions have been enabled by HAL_UART_Transmit_IT()
  * @param  huart: UART handle
  * @retval HAL status
  */
static HAL_StatusTypeDef UART_Transmit_IT(UART_HandleTypeDef *huart)
{
  uint16_t* tmp;

  if ((huart->State == HAL_UART_STATE_BUSY_TX) || (huart->State == HAL_UART_STATE_BUSY_TX_RX))
  {

    if(huart->TxXferCount == 0)
    {
      /* Disable the UART Transmit Data Register Empty Interrupt */
      __HAL_UART_DISABLE_IT(huart, UART_IT_TXE);

      /* Check if a receive Process is ongoing or not */
      if(huart->State == HAL_UART_STATE_BUSY_TX_RX) 
      {
        huart->State = HAL_UART_STATE_BUSY_RX;
      }
      else
      {
        /* Disable the UART Error Interrupt: (Frame error, noise error, overrun error) */
        __HAL_UART_DISABLE_IT(huart, UART_IT_ERR);
        
        huart->State = HAL_UART_STATE_READY;
      }
      
      /* Wait on TC flag to be able to start a second transfer */
      if(UART_WaitOnFlagUntilTimeout(huart, UART_FLAG_TC, RESET, HAL_UART_TIMEOUT_VALUE) != HAL_OK)
      { 
        return HAL_TIMEOUT;
      }

      HAL_UART_TxCpltCallback(huart);

      return HAL_OK;
    }
    else
    {
      if ((huart->Init.WordLength == UART_WORDLENGTH_9B) && (huart->Init.Parity == UART_PARITY_NONE))
      {
        tmp = (uint16_t*) huart->pTxBuffPtr;
        huart->Instance->TDR = (*tmp & (uint16_t)0x01FF);
        huart->pTxBuffPtr += 2;
      } 
      else
      {
        huart->Instance->TDR = (uint8_t)(*huart->pTxBuffPtr++ & (uint8_t)0xFF);
      }

      huart->TxXferCount--;
      
      return HAL_OK;
    }
  }
  else
  {
    return HAL_BUSY;   
  }
}

/**
  * @brief  Wrap up transmission in non-blocking mode.
  * @param  huart: pointer to a UART_HandleTypeDef structure that contains
  *                the configuration information for the specified UART module.
  * @retval HAL status
  */
static HAL_StatusTypeDef UART_EndTransmit_IT(UART_HandleTypeDef *huart)
{
  /* Disable the UART Transmit Complete Interrupt */
  __HAL_UART_DISABLE_IT(huart, UART_IT_TC);

  /* Check if a receive process is ongoing or not */
  if(huart->State == HAL_UART_STATE_BUSY_TX_RX)
  {
    huart->State = HAL_UART_STATE_BUSY_RX;
  }
  else
  {
    /* Disable the UART Error Interrupt: (Frame error, noise error, overrun error) */
    __HAL_UART_DISABLE_IT(huart, UART_IT_ERR);

    huart->State = HAL_UART_STATE_READY;
  }

  HAL_UART_TxCpltCallback(huart);

  return HAL_OK;
}

/**
  * @brief Receive an amount of data in interrupt mode 
  *         Function called under interruption only, once
  *         interruptions have been enabled by HAL_UART_Receive_IT()
  * @param  huart: UART handle
  * @retval HAL status
  */
static HAL_StatusTypeDef UART_Receive_IT(UART_HandleTypeDef *huart)
{
  uint16_t* tmp;
  uint16_t uhMask = huart->Mask;

  if((huart->State == HAL_UART_STATE_BUSY_RX) || (huart->State == HAL_UART_STATE_BUSY_TX_RX))
  {
    
    if ((huart->Init.WordLength == UART_WORDLENGTH_9B) && (huart->Init.Parity == UART_PARITY_NONE))
    {
      tmp = (uint16_t*) huart->pRxBuffPtr ;
      *tmp = (uint16_t)(huart->Instance->RDR & uhMask);
      huart->pRxBuffPtr +=2;
    }
    else
    {
      *huart->pRxBuffPtr++ = (uint8_t)(huart->Instance->RDR & (uint8_t)uhMask); 
    }

    if(--huart->RxXferCount == 0)
    {
      __HAL_UART_DISABLE_IT(huart, UART_IT_RXNE);

      /* Check if a transmit Process is ongoing or not */
      if(huart->State == HAL_UART_STATE_BUSY_TX_RX) 
      {
        huart->State = HAL_UART_STATE_BUSY_TX;
      }
      else
      {
        /* Disable the UART Parity Error Interrupt */
        __HAL_UART_DISABLE_IT(huart, UART_IT_PE);

        /* Disable the UART Error Interrupt: (Frame error, noise error, overrun error) */
        __HAL_UART_DISABLE_IT(huart, UART_IT_ERR);

        huart->State = HAL_UART_STATE_READY;
      }
      
      HAL_UART_RxCpltCallback(huart);
      
      return HAL_OK;
    }
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY; 
  }
}

/**
  * @}
  */

/** @defgroup UART_Exported_Functions_Group3 Peripheral Control functions 
  *  @brief   UART control functions 
  *
@verbatim   
 ===============================================================================
                      ##### Peripheral Control functions #####
 ===============================================================================  
    [..]
    This subsection provides a set of functions allowing to control the UART.
     (+) HAL_UART_GetState() API is helpful to check in run-time the state of the UART peripheral. 
     (+) HAL_MultiProcessor_EnableMuteMode() API enables mute mode
     (+) HAL_MultiProcessor_DisableMuteMode() API disables mute mode
     (+) HAL_MultiProcessor_EnterMuteMode() API enters mute mode
     (+) HAL_MultiProcessor_EnableMuteMode() API enables mute mode
     (+) UART_SetConfig() API configures the UART peripheral
     (+) UART_AdvFeatureConfig() API optionally configures the UART advanced features        
     (+) UART_CheckIdleState() API ensures that TEACK and/or REACK are set after initialization 
     (+) HAL_HalfDuplex_EnableTransmitter() API disables receiver and enables transmitter  
     (+) HAL_HalfDuplex_EnableReceiver() API disables transmitter and enables receiver  
     (+) HAL_LIN_SendBreak() API transmits the break characters           
@endverbatim
  * @{
  */

/**
  * @brief Enable UART in mute mode (doesn't mean UART enters mute mode;
  * to enter mute mode, HAL_MultiProcessor_EnterMuteMode() API must be called)
  * @param huart: UART handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_MultiProcessor_EnableMuteMode(UART_HandleTypeDef *huart)
{  
  /* Process Locked */
  __HAL_LOCK(huart);
  
  huart->State = HAL_UART_STATE_BUSY;
  
  /* Enable USART mute mode by setting the MME bit in the CR1 register */
  huart->Instance->CR1 |= USART_CR1_MME;
  
  huart->State = HAL_UART_STATE_READY;
  
  return (UART_CheckIdleState(huart));
}

/**
  * @brief Disable UART mute mode (doesn't mean it actually wakes up the software,
  * as it may not have been in mute mode at this very moment).
  * @param huart: uart handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_MultiProcessor_DisableMuteMode(UART_HandleTypeDef *huart)
{ 
  /* Process Locked */
  __HAL_LOCK(huart);
  
  huart->State = HAL_UART_STATE_BUSY;
  
   /* Disable USART mute mode by clearing the MME bit in the CR1 register */
  huart->Instance->CR1 &= ~(USART_CR1_MME);
  
  huart->State = HAL_UART_STATE_READY;
  
  return (UART_CheckIdleState(huart));
}

/**
  * @brief Enter UART mute mode (means UART actually enters mute mode).
  * To exit from mute mode, HAL_MultiProcessor_DisableMuteMode() API must be called. 
  * @param huart: uart handle
  * @retval HAL status
  */
void HAL_MultiProcessor_EnterMuteMode(UART_HandleTypeDef *huart)
{    
  __HAL_UART_SEND_REQ(huart, UART_MUTE_MODE_REQUEST);
}



/**
  * @brief return the UART state
  * @param huart: uart handle
  * @retval HAL state
  */
HAL_UART_StateTypeDef HAL_UART_GetState(UART_HandleTypeDef *huart)
{
  return huart->State;
}

/**
* @brief  Return the UART error code
* @param  huart : pointer to a UART_HandleTypeDef structure that contains
  *              the configuration information for the specified UART.
* @retval UART Error Code
*/
uint32_t HAL_UART_GetError(UART_HandleTypeDef *huart)
{
  return huart->ErrorCode;
}

/**
  * @brief Configure the UART peripheral 
  * @param huart: uart handle
  * @retval None
  */
HAL_StatusTypeDef UART_SetConfig(UART_HandleTypeDef *huart)
{
  uint32_t tmpreg                     = 0x00000000;
  UART_ClockSourceTypeDef clocksource = UART_CLOCKSOURCE_UNDEFINED;
  uint16_t brrtemp                    = 0x0000;
  uint16_t usartdiv                   = 0x0000;
  HAL_StatusTypeDef ret               = HAL_OK;  
  
  /* Check the parameters */ 
  assert_param(IS_UART_BAUDRATE(huart->Init.BaudRate));  
  assert_param(IS_UART_WORD_LENGTH(huart->Init.WordLength));
  assert_param(IS_UART_STOPBITS(huart->Init.StopBits));
  assert_param(IS_UART_PARITY(huart->Init.Parity));
  assert_param(IS_UART_MODE(huart->Init.Mode));
  assert_param(IS_UART_HARDWARE_FLOW_CONTROL(huart->Init.HwFlowCtl));
  assert_param(IS_UART_ONE_BIT_SAMPLE(huart->Init.OneBitSampling)); 


  /*-------------------------- USART CR1 Configuration -----------------------*/
  /* Clear M, PCE, PS, TE, RE and OVER8 bits and configure       
   *  the UART Word Length, Parity, Mode and oversampling: 
   *  set the M bits according to huart->Init.WordLength value 
   *  set PCE and PS bits according to huart->Init.Parity value
   *  set TE and RE bits according to huart->Init.Mode value
   *  set OVER8 bit according to huart->Init.OverSampling value */
  tmpreg = (uint32_t)huart->Init.WordLength | huart->Init.Parity | huart->Init.Mode | huart->Init.OverSampling ;
  MODIFY_REG(huart->Instance->CR1, UART_CR1_FIELDS, tmpreg);

  /*-------------------------- USART CR2 Configuration -----------------------*/
  /* Configure the UART Stop Bits: Set STOP[13:12] bits according 
   * to huart->Init.StopBits value */
  MODIFY_REG(huart->Instance->CR2, USART_CR2_STOP, huart->Init.StopBits);
  
  /*-------------------------- USART CR3 Configuration -----------------------*/
  /* Configure 
   * - UART HardWare Flow Control: set CTSE and RTSE bits according 
   *   to huart->Init.HwFlowCtl value 
   * - one-bit sampling method versus three samples' majority rule according
   *   to huart->Init.OneBitSampling */
  tmpreg = (uint32_t)huart->Init.HwFlowCtl | huart->Init.OneBitSampling ;
  MODIFY_REG(huart->Instance->CR3, (USART_CR3_RTSE | USART_CR3_CTSE | USART_CR3_ONEBIT), tmpreg);
  
  /*-------------------------- USART BRR Configuration -----------------------*/
  UART_GETCLOCKSOURCE(huart, clocksource);

  /* Check UART Over Sampling to set Baud Rate Register */
  if (huart->Init.OverSampling == UART_OVERSAMPLING_8)
  { 
    switch (clocksource)
    {
    case UART_CLOCKSOURCE_PCLK1:
        usartdiv = (uint16_t)(UART_DIV_SAMPLING8(HAL_RCC_GetPCLK1Freq(), huart->Init.BaudRate));
      break;
    case UART_CLOCKSOURCE_PCLK2:
        usartdiv = (uint16_t)(UART_DIV_SAMPLING8(HAL_RCC_GetPCLK2Freq(), huart->Init.BaudRate));
      break;
    case UART_CLOCKSOURCE_HSI:
        usartdiv = (uint16_t)(UART_DIV_SAMPLING8(HSI_VALUE, huart->Init.BaudRate)); 
      break;
    case UART_CLOCKSOURCE_SYSCLK:
        usartdiv = (uint16_t)(UART_DIV_SAMPLING8(HAL_RCC_GetSysClockFreq(), huart->Init.BaudRate));
      break;
    case UART_CLOCKSOURCE_LSE:
        usartdiv = (uint16_t)(UART_DIV_SAMPLING8(LSE_VALUE, huart->Init.BaudRate)); 
      break;
      case UART_CLOCKSOURCE_UNDEFINED:                
    default:
        ret = HAL_ERROR; 
      break;
    }
    
    brrtemp = usartdiv & 0xFFF0;
    brrtemp |= (uint16_t)((usartdiv & (uint16_t)0x000F) >> 1U);
    huart->Instance->BRR = brrtemp;
  }
  else
  {
    switch (clocksource)
    {
    case UART_CLOCKSOURCE_PCLK1: 
        huart->Instance->BRR = (uint16_t)(UART_DIV_SAMPLING16(HAL_RCC_GetPCLK1Freq(), huart->Init.BaudRate));
      break;
    case UART_CLOCKSOURCE_PCLK2: 
        huart->Instance->BRR = (uint16_t)(UART_DIV_SAMPLING16(HAL_RCC_GetPCLK2Freq(), huart->Init.BaudRate));
      break;
    case UART_CLOCKSOURCE_HSI: 
        huart->Instance->BRR = (uint16_t)(UART_DIV_SAMPLING16(HSI_VALUE, huart->Init.BaudRate)); 
      break; 
    case UART_CLOCKSOURCE_SYSCLK:  
        huart->Instance->BRR = (uint16_t)(UART_DIV_SAMPLING16(HAL_RCC_GetSysClockFreq(), huart->Init.BaudRate));
      break;  
    case UART_CLOCKSOURCE_LSE:
        huart->Instance->BRR = (uint16_t)(UART_DIV_SAMPLING16(LSE_VALUE, huart->Init.BaudRate)); 
      break;
      case UART_CLOCKSOURCE_UNDEFINED:                
    default:
        ret = HAL_ERROR; 
      break;
    }
  }

  return ret;   

}


/**
  * @brief Configure the UART peripheral advanced features 
  * @param huart: uart handle  
  * @retval None
  */
void UART_AdvFeatureConfig(UART_HandleTypeDef *huart)
{
  /* Check whether the set of advanced features to configure is properly set */ 
  assert_param(IS_UART_ADVFEATURE_INIT(huart->AdvancedInit.AdvFeatureInit));
  
  /* if required, configure TX pin active level inversion */
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_TXINVERT_INIT))
  {
    assert_param(IS_UART_ADVFEATURE_TXINV(huart->AdvancedInit.TxPinLevelInvert));
    MODIFY_REG(huart->Instance->CR2, USART_CR2_TXINV, huart->AdvancedInit.TxPinLevelInvert);
  }
  
  /* if required, configure RX pin active level inversion */
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_RXINVERT_INIT))
  {
    assert_param(IS_UART_ADVFEATURE_RXINV(huart->AdvancedInit.RxPinLevelInvert));
    MODIFY_REG(huart->Instance->CR2, USART_CR2_RXINV, huart->AdvancedInit.RxPinLevelInvert);
  }
  
  /* if required, configure data inversion */
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_DATAINVERT_INIT))
  {
    assert_param(IS_UART_ADVFEATURE_DATAINV(huart->AdvancedInit.DataInvert));
    MODIFY_REG(huart->Instance->CR2, USART_CR2_DATAINV, huart->AdvancedInit.DataInvert);
  }
  
  /* if required, configure RX/TX pins swap */
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_SWAP_INIT))
  {
    assert_param(IS_UART_ADVFEATURE_SWAP(huart->AdvancedInit.Swap));
    MODIFY_REG(huart->Instance->CR2, USART_CR2_SWAP, huart->AdvancedInit.Swap);
  }
  
  /* if required, configure RX overrun detection disabling */
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_RXOVERRUNDISABLE_INIT))
  {
    assert_param(IS_UART_OVERRUN(huart->AdvancedInit.OverrunDisable));  
    MODIFY_REG(huart->Instance->CR3, USART_CR3_OVRDIS, huart->AdvancedInit.OverrunDisable);
  }
  
  /* if required, configure DMA disabling on reception error */
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_DMADISABLEONERROR_INIT))
  {
    assert_param(IS_UART_ADVFEATURE_DMAONRXERROR(huart->AdvancedInit.DMADisableonRxError));   
    MODIFY_REG(huart->Instance->CR3, USART_CR3_DDRE, huart->AdvancedInit.DMADisableonRxError);
  }
  
  /* if required, configure auto Baud rate detection scheme */              
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_AUTOBAUDRATE_INIT))
  {
    assert_param(IS_UART_ADVFEATURE_AUTOBAUDRATE(huart->AdvancedInit.AutoBaudRateEnable));
    MODIFY_REG(huart->Instance->CR2, USART_CR2_ABREN, huart->AdvancedInit.AutoBaudRateEnable);
    /* set auto Baudrate detection parameters if detection is enabled */
    if(huart->AdvancedInit.AutoBaudRateEnable == UART_ADVFEATURE_AUTOBAUDRATE_ENABLE)
    {
      assert_param(IS_UART_ADVFEATURE_AUTOBAUDRATEMODE(huart->AdvancedInit.AutoBaudRateMode));
      MODIFY_REG(huart->Instance->CR2, USART_CR2_ABRMODE, huart->AdvancedInit.AutoBaudRateMode);
    }
  }
  
  /* if required, configure MSB first on communication line */  
  if(HAL_IS_BIT_SET(huart->AdvancedInit.AdvFeatureInit, UART_ADVFEATURE_MSBFIRST_INIT))
  {
    assert_param(IS_UART_ADVFEATURE_MSBFIRST(huart->AdvancedInit.MSBFirst));   
    MODIFY_REG(huart->Instance->CR2, USART_CR2_MSBFIRST, huart->AdvancedInit.MSBFirst);
  }
}



/**
  * @brief Check the UART Idle State
  * @param huart: uart handle
  * @retval HAL status
  */
HAL_StatusTypeDef UART_CheckIdleState(UART_HandleTypeDef *huart)
{
  /* Initialize the UART ErrorCode */
  huart->ErrorCode = HAL_UART_ERROR_NONE;
  
  /* Check if the Transmitter is enabled */
  if((huart->Instance->CR1 & USART_CR1_TE) == USART_CR1_TE)
  {
    /* Wait until TEACK flag is set */
    if(UART_WaitOnFlagUntilTimeout(huart, USART_ISR_TEACK, RESET, HAL_UART_TIMEOUT_VALUE) != HAL_OK)  
    {
      /* Timeout Occurred */
      return HAL_TIMEOUT;
    }
  }
  /* Check if the Receiver is enabled */
  if((huart->Instance->CR1 & USART_CR1_RE) == USART_CR1_RE)
  {
    /* Wait until REACK flag is set */
    if(UART_WaitOnFlagUntilTimeout(huart, USART_ISR_REACK, RESET,  HAL_UART_TIMEOUT_VALUE) != HAL_OK)  
    { 
      /* Timeout Occurred */
      return HAL_TIMEOUT;
    }
  }
  
  /* Initialize the UART State */
  huart->State= HAL_UART_STATE_READY;
    
  /* Process Unlocked */
  __HAL_UNLOCK(huart);
  
  return HAL_OK;
}

/**
  * @brief  Enables the UART transmitter and disables the UART receiver.
  * @param  huart: UART handle
  * @retval HAL status
  * @retval None
  */
HAL_StatusTypeDef HAL_HalfDuplex_EnableTransmitter(UART_HandleTypeDef *huart)
{
  /* Process Locked */
  __HAL_LOCK(huart);
  huart->State = HAL_UART_STATE_BUSY;
  
  /* Clear TE and RE bits */
  CLEAR_BIT(huart->Instance->CR1, (USART_CR1_TE | USART_CR1_RE));
  /* Enable the USART's transmit interface by setting the TE bit in the USART CR1 register */
  SET_BIT(huart->Instance->CR1, USART_CR1_TE);
 
  huart->State= HAL_UART_STATE_READY;
  /* Process Unlocked */
  __HAL_UNLOCK(huart);
  
  return HAL_OK;
}

/**
  * @brief  Enables the UART receiver and disables the UART transmitter.
  * @param  huart: UART handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_HalfDuplex_EnableReceiver(UART_HandleTypeDef *huart)
{
  /* Process Locked */
  __HAL_LOCK(huart);
  huart->State = HAL_UART_STATE_BUSY;

  /* Clear TE and RE bits */
  CLEAR_BIT(huart->Instance->CR1, (USART_CR1_TE | USART_CR1_RE));
  /* Enable the USART's receive interface by setting the RE bit in the USART CR1 register */
  SET_BIT(huart->Instance->CR1, USART_CR1_RE);

  huart->State = HAL_UART_STATE_READY;
  /* Process Unlocked */
  __HAL_UNLOCK(huart);

  return HAL_OK;
}


/**
  * @brief  Transmits break characters.
  * @param  huart: UART handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_LIN_SendBreak(UART_HandleTypeDef *huart)
{
  /* Check the parameters */
  assert_param(IS_UART_INSTANCE(huart->Instance));
  
  /* Process Locked */
  __HAL_LOCK(huart);
  
  huart->State = HAL_UART_STATE_BUSY;
  
  /* Send break characters */
  huart->Instance->RQR |= UART_SENDBREAK_REQUEST;  
 
  huart->State = HAL_UART_STATE_READY;
  
  /* Process Unlocked */
  __HAL_UNLOCK(huart);
  
  return HAL_OK; 
}


/**
  * @}
  */

/**
  * @}
  */

#endif /* HAL_UART_MODULE_ENABLED */
/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
