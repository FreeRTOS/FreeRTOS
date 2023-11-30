/**
  ******************************************************************************
  * @file    stm32f7xx_hal_sai.c
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   SAI HAL module driver.
  *          This file provides firmware functions to manage the following 
  *          functionalities of the Serial Audio Interface (SAI) peripheral:
  *           + Initialization/de-initialization functions
  *           + I/O operation functions
  *           + Peripheral Control functions 
  *           + Peripheral State functions
  *         
  @verbatim
 ==============================================================================
                  ##### How to use this driver #####
  ==============================================================================
           
  [..]
    The SAI HAL driver can be used as follows:
    
    (#) Declare a SAI_HandleTypeDef handle structure.
    (#) Initialize the SAI low level resources by implementing the HAL_SAI_MspInit() API:
        (##) Enable the SAI interface clock.                      
        (##) SAI pins configuration:
            (+++) Enable the clock for the SAI GPIOs.
            (+++) Configure these SAI pins as alternate function pull-up.
        (##) NVIC configuration if you need to use interrupt process (HAL_SAI_Transmit_IT()
             and HAL_SAI_Receive_IT() APIs):
            (+++) Configure the SAI interrupt priority.
            (+++) Enable the NVIC SAI IRQ handle.

        (##) DMA Configuration if you need to use DMA process (HAL_SAI_Transmit_DMA()
             and HAL_SAI_Receive_DMA() APIs):
            (+++) Declare a DMA handle structure for the Tx/Rx stream.
            (+++) Enable the DMAx interface clock.
            (+++) Configure the declared DMA handle structure with the required Tx/Rx parameters.                
            (+++) Configure the DMA Tx/Rx Stream.
            (+++) Associate the initialized DMA handle to the SAI DMA Tx/Rx handle.
            (+++) Configure the priority and enable the NVIC for the transfer complete interrupt on the 
                DMA Tx/Rx Stream.
  
   (#) Program the SAI Mode, Standard, Data Format, MCLK Output, Audio frequency and Polarity
       using HAL_SAI_Init() function.
   
   -@- The specific SAI interrupts (FIFO request and Overrun underrun interrupt)
       will be managed using the macros __SAI_ENABLE_IT() and __SAI_DISABLE_IT()
       inside the transmit and receive process.   

  [..]           
   (@) SAI Clock Source, the configuration is managed through RCCEx_PeriphCLKConfig()
            function in the HAL RCC drivers        
  [..]           
   (@) Make sure that either:
       (+@) I2S PLL is configured or 
       (+@) SAI PLL is configured or 
       (+@) External clock source is configured after setting correctly 
            the define constant EXTERNAL_CLOCK_VALUE in the stm32f7xx_hal_conf.h file. 
                        
  [..]           
    (@) In master Tx mode: enabling the audio block immediately generates the bit clock 
        for the external slaves even if there is no data in the FIFO, However FS signal 
        generation is conditioned by the presence of data in the FIFO.
                 
  [..]           
    (@) In master Rx mode: enabling the audio block immediately generates the bit clock 
        and FS signal for the external slaves. 
                
  [..]           
    (@) It is mandatory to respect the following conditions in order to avoid bad SAI behavior: 
        (+@)  First bit Offset <= (SLOT size - Data size)
        (+@)  Data size <= SLOT size
        (+@)  Number of SLOT x SLOT size = Frame length
        (+@)  The number of slots should be even when SAI_FS_CHANNEL_IDENTIFICATION is selected.  

  [..]         
     Three operation modes are available within this driver :     
  
   *** Polling mode IO operation ***
   =================================
   [..]    
     (+) Send an amount of data in blocking mode using HAL_SAI_Transmit() 
     (+) Receive an amount of data in blocking mode using HAL_SAI_Receive()
   
   *** Interrupt mode IO operation ***    
   ===================================
   [..]    
     (+) Send an amount of data in non blocking mode using HAL_SAI_Transmit_IT() 
     (+) At transmission end of transfer HAL_SAI_TxCpltCallback is executed and user can 
         add his own code by customization of function pointer HAL_SAI_TxCpltCallback
     (+) Receive an amount of data in non blocking mode using HAL_SAI_Receive_IT() 
     (+) At reception end of transfer HAL_SAI_RxCpltCallback is executed and user can 
         add his own code by customization of function pointer HAL_SAI_RxCpltCallback                                      
     (+) In case of transfer Error, HAL_SAI_ErrorCallback() function is executed and user can 
         add his own code by customization of function pointer HAL_SAI_ErrorCallback

   *** DMA mode IO operation ***    
   ==============================
   [..] 
     (+) Send an amount of data in non blocking mode (DMA) using HAL_SAI_Transmit_DMA() 
     (+) At transmission end of transfer HAL_SAI_TxCpltCallback is executed and user can 
         add his own code by customization of function pointer HAL_SAI_TxCpltCallback
     (+) Receive an amount of data in non blocking mode (DMA) using HAL_SAI_Receive_DMA() 
     (+) At reception end of transfer HAL_SAI_RxCpltCallback is executed and user can 
         add his own code by customization of function pointer HAL_SAI_RxCpltCallback                                  
     (+) In case of transfer Error, HAL_SAI_ErrorCallback() function is executed and user can 
         add his own code by customization of function pointer HAL_SAI_ErrorCallback
     (+) Pause the DMA Transfer using HAL_SAI_DMAPause()      
     (+) Resume the DMA Transfer using HAL_SAI_DMAResume()  
     (+) Stop the DMA Transfer using HAL_SAI_DMAStop()      
   
   *** SAI HAL driver macros list ***
   ============================================= 
   [..]
     Below the list of most used macros in USART HAL driver :
       
      (+) __HAL_SAI_ENABLE: Enable the SAI peripheral
      (+) __HAL_SAI_DISABLE: Disable the SAI peripheral
      (+) __HAL_SAI_ENABLE_IT : Enable the specified SAI interrupts
      (+) __HAL_SAI_DISABLE_IT : Disable the specified SAI interrupts
      (+) __HAL_SAI_GET_IT_SOURCE: Check if the specified SAI interrupt source is 
          enabled or disabled
      (+) __HAL_SAI_GET_FLAG: Check whether the specified SAI flag is set or not
  
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

/** @defgroup SAI SAI
  * @brief SAI HAL module driver
  * @{
  */

#ifdef HAL_SAI_MODULE_ENABLED

/* Private typedef -----------------------------------------------------------*/
/** @defgroup SAI_Private_Typedefs  SAI Private Typedefs
  * @{
  */
typedef enum {
  SAI_MODE_DMA,
  SAI_MODE_IT
}SAI_ModeTypedef;
/**
  * @}
  */
/* Private define ------------------------------------------------------------*/
/** @defgroup SAI_Private_Constants  SAI Private Constants
  * @{
  */
#define SAI_FIFO_SIZE       8
#define SAI_DEFAULT_TIMEOUT 4
/**
  * @}
  */

/* SAI registers Masks */
#define CR1_CLEAR_MASK            ((uint32_t)0xFF04C010)
#define FRCR_CLEAR_MASK           ((uint32_t)0xFFF88000)
#define SLOTR_CLEAR_MASK          ((uint32_t)0x0000F020)

#define SAI_TIMEOUT_VALUE         10
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
static void SAI_FillFifo(SAI_HandleTypeDef *hsai);
static uint32_t SAI_InterruptFlag(SAI_HandleTypeDef *hsai, uint32_t mode);
static HAL_StatusTypeDef SAI_InitI2S(SAI_HandleTypeDef *hsai, uint32_t protocol, uint32_t datasize, uint32_t nbslot);
static HAL_StatusTypeDef SAI_InitPCM(SAI_HandleTypeDef *hsai, uint32_t protocol, uint32_t datasize, uint32_t nbslot);

static HAL_StatusTypeDef SAI_Disable(SAI_HandleTypeDef *hsai);
static void SAI_Transmit_IT8Bit(SAI_HandleTypeDef *hsai);
static void SAI_Transmit_IT16Bit(SAI_HandleTypeDef *hsai);
static void SAI_Transmit_IT32Bit(SAI_HandleTypeDef *hsai);
static void SAI_Receive_IT8Bit(SAI_HandleTypeDef *hsai);
static void SAI_Receive_IT16Bit(SAI_HandleTypeDef *hsai);
static void SAI_Receive_IT32Bit(SAI_HandleTypeDef *hsai);

static void SAI_DMATxCplt(DMA_HandleTypeDef *hdma);
static void SAI_DMATxHalfCplt(DMA_HandleTypeDef *hdma);
static void SAI_DMARxCplt(DMA_HandleTypeDef *hdma);
static void SAI_DMARxHalfCplt(DMA_HandleTypeDef *hdma);
static void SAI_DMAError(DMA_HandleTypeDef *hdma);

/* Exported functions ---------------------------------------------------------*/

/** @defgroup SAI_Exported_Functions  SAI Exported Functions
  * @{
  */

/** @defgroup SAI_Exported_Functions_Group1 Initialization and de-initialization functions 
 *  @brief    Initialization and Configuration functions 
 *
@verbatim    
 ===============================================================================
              ##### Initialization and de-initialization functions #####
 ===============================================================================
    [..]  This subsection provides a set of functions allowing to initialize and 
          de-initialize the SAIx peripheral:

      (+) User must implement HAL_SAI_MspInit() function in which he configures 
          all related peripherals resources (CLOCK, GPIO, DMA, IT and NVIC ).

      (+) Call the function HAL_SAI_Init() to configure the selected device with 
          the selected configuration:
        (++) Mode (Master/slave TX/RX)
        (++) Protocol 
        (++) Data Size
        (++) MCLK Output
        (++) Audio frequency
        (++) FIFO Threshold
        (++) Frame Config
        (++) Slot Config

      (+) Call the function HAL_SAI_DeInit() to restore the default configuration 
          of the selected SAI peripheral.     

@endverbatim
  * @{
  */

/**
  * @brief  Initializes the structure FrameInit, SlotInit and the low part of 
  *         Init according to the specified parameters and call the function
  *         HAL_SAI_Init to initialize the SAI block.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains 
  *               the configuration information for SAI module.
  * @param  protocol : one of the supported protocol @ref SAI_Protocol
  * @param  datasize : one of the supported datasize @ref SAI_Protocol_DataSize
  *                the configuration information for SAI module.
  * @param  nbslot   : Number of slot.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_InitProtocol(SAI_HandleTypeDef *hsai, uint32_t protocol, uint32_t datasize, uint32_t nbslot)
{
  HAL_StatusTypeDef status = HAL_OK;
  
  /* Check the parameters */
  assert_param(IS_SAI_SUPPORTED_PROTOCOL(protocol));
  assert_param(IS_SAI_PROTOCOL_DATASIZE(datasize));
  
  switch(protocol)
  {
  case SAI_I2S_STANDARD :
  case SAI_I2S_MSBJUSTIFIED :
  case SAI_I2S_LSBJUSTIFIED :
    status = SAI_InitI2S(hsai, protocol, datasize, nbslot);
    break;  
  case SAI_PCM_LONG :
  case SAI_PCM_SHORT :
    status = SAI_InitPCM(hsai, protocol, datasize, nbslot);
    break;
  default :
    status = HAL_ERROR;
    break;
  }
  
  if(status == HAL_OK)
  {
    status = HAL_SAI_Init(hsai);
  }

  return status;
}

/**
  * @brief  Initializes the SAI according to the specified parameters 
  *         in the SAI_InitTypeDef and create the associated handle.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Init(SAI_HandleTypeDef *hsai)
{ 
  uint32_t tmpclock = 0;

  /* This variable used to store the SAI_CK_x (value in Hz) */
  uint32_t freq = 0;
  
  /* Check the SAI handle allocation */
  if(hsai == NULL)
  {
    return HAL_ERROR;
  }
  
  /* Check the SAI Block parameters */
  assert_param(IS_SAI_AUDIO_FREQUENCY(hsai->Init.AudioFrequency));  
  assert_param(IS_SAI_BLOCK_PROTOCOL(hsai->Init.Protocol));
  assert_param(IS_SAI_BLOCK_MODE(hsai->Init.AudioMode));
  assert_param(IS_SAI_BLOCK_SYNCEXT(hsai->Init.SynchroExt));
  assert_param(IS_SAI_BLOCK_DATASIZE(hsai->Init.DataSize));
  assert_param(IS_SAI_BLOCK_FIRST_BIT(hsai->Init.FirstBit));
  assert_param(IS_SAI_BLOCK_CLOCK_STROBING(hsai->Init.ClockStrobing));
  assert_param(IS_SAI_BLOCK_SYNCHRO(hsai->Init.Synchro));
  assert_param(IS_SAI_BLOCK_OUTPUT_DRIVE(hsai->Init.OutputDrive));
  assert_param(IS_SAI_BLOCK_NODIVIDER(hsai->Init.NoDivider));
  assert_param(IS_SAI_BLOCK_FIFO_THRESHOLD(hsai->Init.FIFOThreshold));
  assert_param(IS_SAI_MONO_STEREO_MODE(hsai->Init.MonoStereoMode));
  assert_param(IS_SAI_BLOCK_COMPANDING_MODE(hsai->Init.CompandingMode));
  assert_param(IS_SAI_BLOCK_TRISTATE_MANAGEMENT(hsai->Init.TriState));
  
  /* Check the SAI Block Frame parameters */
  assert_param(IS_SAI_BLOCK_FRAME_LENGTH(hsai->FrameInit.FrameLength));
  assert_param(IS_SAI_BLOCK_ACTIVE_FRAME(hsai->FrameInit.ActiveFrameLength));
  assert_param(IS_SAI_BLOCK_FS_DEFINITION(hsai->FrameInit.FSDefinition));
  assert_param(IS_SAI_BLOCK_FS_POLARITY(hsai->FrameInit.FSPolarity));
  assert_param(IS_SAI_BLOCK_FS_OFFSET(hsai->FrameInit.FSOffset));
  
  /* Check the SAI Block Slot parameters */
  assert_param(IS_SAI_BLOCK_FIRSTBIT_OFFSET(hsai->SlotInit.FirstBitOffset));
  assert_param(IS_SAI_BLOCK_SLOT_SIZE(hsai->SlotInit.SlotSize));
  assert_param(IS_SAI_BLOCK_SLOT_NUMBER(hsai->SlotInit.SlotNumber));
  assert_param(IS_SAI_SLOT_ACTIVE(hsai->SlotInit.SlotActive));
  
  if(hsai->State == HAL_SAI_STATE_RESET)
  {
    /* Allocate lock resource and initialize it */
    hsai->Lock = HAL_UNLOCKED;
    
    /* Init the low level hardware : GPIO, CLOCK, NVIC and DMA */
    HAL_SAI_MspInit(hsai);
  }
  
  hsai->State = HAL_SAI_STATE_BUSY;
  
  /* Disable the selected SAI peripheral */
  SAI_Disable(hsai);
  
  /* SAI Block Synchro Configuration -----------------------------------------*/
  SAI_BlockSynchroConfig(hsai);
    
  /* Configure Master Clock using the following formula :
     MCLK_x = SAI_CK_x / (MCKDIV[3:0] * 2) with MCLK_x = 256 * FS
     FS = SAI_CK_x / (MCKDIV[3:0] * 2) * 256
     MCKDIV[3:0] = SAI_CK_x / FS * 512 */
  if(hsai->Init.AudioFrequency != SAI_AUDIO_FREQUENCY_MCKDIV)
  { 
  /* Get SAI clock source based on Source clock selection from RCC */
  freq = SAI_GetInputClock(hsai);
  
    /* (saiclocksource x 10) to keep Significant digits */
    tmpclock = (((freq * 10) / ((hsai->Init.AudioFrequency) * 512)));
    
    hsai->Init.Mckdiv = tmpclock / 10;
    
        /* Round result to the nearest integer */
    if((tmpclock % 10) > 8) 
    {
      hsai->Init.Mckdiv+= 1;
    }
  }

  /* SAI Block Configuration ------------------------------------------------------------*/
  /* SAI CR1 Configuration */
  hsai->Instance->CR1&=~(SAI_xCR1_MODE | SAI_xCR1_PRTCFG |  SAI_xCR1_DS |      \
                         SAI_xCR1_LSBFIRST | SAI_xCR1_CKSTR | SAI_xCR1_SYNCEN |\
                         SAI_xCR1_MONO | SAI_xCR1_OUTDRIV  | SAI_xCR1_DMAEN |  \
                         SAI_xCR1_NODIV | SAI_xCR1_MCKDIV);
  
  hsai->Instance->CR1|= (hsai->Init.AudioMode | hsai->Init.Protocol |           \
                        hsai->Init.DataSize | hsai->Init.FirstBit  |           \
                        hsai->Init.ClockStrobing | hsai->Init.Synchro |        \
                        hsai->Init.MonoStereoMode | hsai->Init.OutputDrive |   \
                        hsai->Init.NoDivider | (hsai->Init.Mckdiv << 20) | hsai->Init.CompandingMode);  
  
  /* SAI CR2 Configuration */
  hsai->Instance->CR2&= ~(SAI_xCR2_FTH | SAI_xCR2_FFLUSH | SAI_xCR2_COMP);
  hsai->Instance->CR2|=  (hsai->Init.FIFOThreshold | hsai->Init.CompandingMode | hsai->Init.TriState);


  /* SAI Frame Configuration -----------------------------------------*/
  hsai->Instance->FRCR&=(~(SAI_xFRCR_FRL | SAI_xFRCR_FSALL | SAI_xFRCR_FSDEF | \
                           SAI_xFRCR_FSPO | SAI_xFRCR_FSOFF));
  hsai->Instance->FRCR|=((hsai->FrameInit.FrameLength - 1)  | 
                            hsai->FrameInit.FSOffset | 
                            hsai->FrameInit.FSDefinition | 
                            hsai->FrameInit.FSPolarity   | 
                            ((hsai->FrameInit.ActiveFrameLength - 1) << 8));  
  
  /* SAI Block_x SLOT Configuration ------------------------------------------*/
  /* This register has no meaning in AC�97 and SPDIF audio protocol */
  hsai->Instance->SLOTR&= (~(SAI_xSLOTR_FBOFF | SAI_xSLOTR_SLOTSZ |            \
                             SAI_xSLOTR_NBSLOT | SAI_xSLOTR_SLOTEN ));
  
  hsai->Instance->SLOTR|=  hsai->SlotInit.FirstBitOffset |  hsai->SlotInit.SlotSize
                          | hsai->SlotInit.SlotActive | ((hsai->SlotInit.SlotNumber - 1) <<  8);           
  
  /* Initialise the error code */
  hsai->ErrorCode = HAL_SAI_ERROR_NONE;
  
  /* Initialize the SAI state */
  hsai->State= HAL_SAI_STATE_READY;
  
  /* Release Lock */
  __HAL_UNLOCK(hsai);
  
  return HAL_OK;
}

/**
  * @brief  DeInitializes the SAI peripheral. 
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_DeInit(SAI_HandleTypeDef *hsai)
{
  /* Check the SAI handle allocation */
  if(hsai == NULL)
  {
    return HAL_ERROR;
  }

  hsai->State = HAL_SAI_STATE_BUSY;

  /* Disabled All interrupt and clear all the flag */
  hsai->Instance->IMR = 0;
  hsai->Instance->CLRFR = 0xFFFFFFFF;
  
  /* Disable the SAI */
  SAI_Disable(hsai);

  /* Flush the fifo */
  SET_BIT(hsai->Instance->CR2, SAI_xCR2_FFLUSH);
  
  /* DeInit the low level hardware: GPIO, CLOCK, NVIC and DMA */
  HAL_SAI_MspDeInit(hsai);

  /* Initialize the error code */
  hsai->ErrorCode = HAL_SAI_ERROR_NONE;
  
  /* Initialize the SAI state */
  hsai->State = HAL_SAI_STATE_RESET;

  /* Release Lock */
  __HAL_UNLOCK(hsai);

  return HAL_OK;
}

/**
  * @brief SAI MSP Init.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None
  */
__weak void HAL_SAI_MspInit(SAI_HandleTypeDef *hsai)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_SAI_MspInit could be implemented in the user file
   */ 
}

/**
  * @brief SAI MSP DeInit.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None
  */
__weak void HAL_SAI_MspDeInit(SAI_HandleTypeDef *hsai)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_SAI_MspDeInit could be implemented in the user file
   */ 
}

/**
  * @}
  */

/** @defgroup SAI_Exported_Functions_Group2 IO operation functions 
 *  @brief   Data transfers functions 
 *
@verbatim   
  ===============================================================================
                      ##### IO operation functions #####
 ===============================================================================  
    [..]
    This subsection provides a set of functions allowing to manage the SAI data 
    transfers.

    (+) There are two modes of transfer:
       (++) Blocking mode : The communication is performed in the polling mode. 
            The status of all data processing is returned by the same function 
            after finishing transfer.  
       (++) No-Blocking mode : The communication is performed using Interrupts 
            or DMA. These functions return the status of the transfer startup.
            The end of the data processing will be indicated through the 
            dedicated SAI IRQ when using Interrupt mode or the DMA IRQ when 
            using DMA mode.

    (+) Blocking mode functions are :
        (++) HAL_SAI_Transmit()
        (++) HAL_SAI_Receive()
        (++) HAL_SAI_TransmitReceive()
        
    (+) Non Blocking mode functions with Interrupt are :
        (++) HAL_SAI_Transmit_IT()
        (++) HAL_SAI_Receive_IT()
        (++) HAL_SAI_TransmitReceive_IT()

    (+) Non Blocking mode functions with DMA are :
        (++) HAL_SAI_Transmit_DMA()
        (++) HAL_SAI_Receive_DMA()
        (++) HAL_SAI_TransmitReceive_DMA()

    (+) A set of Transfer Complete Callbacks are provided in non Blocking mode:
        (++) HAL_SAI_TxCpltCallback()
        (++) HAL_SAI_RxCpltCallback()
        (++) HAL_SAI_ErrorCallback()

@endverbatim
  * @{
  */

/**
  * @brief  Transmits an amount of data in blocking mode.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  pData: Pointer to data buffer
  * @param  Size: Amount of data to be sent
  * @param  Timeout: Timeout duration
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Transmit(SAI_HandleTypeDef *hsai, uint8_t* pData, uint16_t Size, uint32_t Timeout)
{
  uint32_t tickstart = 0;
  
  if((pData == NULL ) || (Size == 0)) 
  {
    return  HAL_ERROR;
  }
  
  if(hsai->State == HAL_SAI_STATE_READY)
  {  
    /* Process Locked */
    __HAL_LOCK(hsai);
    
    hsai->State = HAL_SAI_STATE_BUSY_TX;
    hsai->ErrorCode = HAL_SAI_ERROR_NONE;
    hsai->XferSize = Size;
    hsai->XferCount = Size;
    hsai->pBuffPtr = pData;
    
    /* Check if the SAI is already enabled */ 
    if((hsai->Instance->CR1 & SAI_xCR1_SAIEN) != SAI_xCR1_SAIEN)
    {
      /* fill the fifo with data before to enabled the SAI */
      SAI_FillFifo(hsai);      
      /* Enable SAI peripheral */    
      __HAL_SAI_ENABLE(hsai);
    }
    
    while(hsai->XferCount > 0)
    { 
      /* Write data if the FIFO is not full */
      if((hsai->Instance->SR & SAI_xSR_FLVL) != SAI_FIFOSTATUS_FULL)
      {
        if((hsai->Init.DataSize == SAI_DATASIZE_8) && (hsai->Init.CompandingMode == SAI_NOCOMPANDING))
        {      
          hsai->Instance->DR = (*hsai->pBuffPtr++);
        }
        else if(hsai->Init.DataSize <= SAI_DATASIZE_16)
        {
          hsai->Instance->DR = *((uint16_t *)hsai->pBuffPtr);
          hsai->pBuffPtr+= 2;        
        }
        else
        {
          hsai->Instance->DR = *((uint32_t *)hsai->pBuffPtr);
          hsai->pBuffPtr+= 4;
        }       
        hsai->XferCount--; 
      }
      else
      {
        /* Get tick */
        tickstart = HAL_GetTick();      
        /* Check for the Timeout */
        if(Timeout != HAL_MAX_DELAY)
        {
          if((Timeout == 0)||((HAL_GetTick() - tickstart ) > Timeout))
          {
            /* Update error code */
            hsai->ErrorCode |= HAL_SAI_ERROR_TIMEOUT;
            
            /* Process Unlocked */
            __HAL_UNLOCK(hsai);
            
            /* Change the SAI state */
            hsai->State = HAL_SAI_STATE_TIMEOUT;
            
            return HAL_TIMEOUT;
          }
        } 
      }
    }      
    
    hsai->State = HAL_SAI_STATE_READY; 
    
    /* Process Unlocked */
    __HAL_UNLOCK(hsai);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;
  }
}

/**
  * @brief  Receives an amount of data in blocking mode. 
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  pData: Pointer to data buffer
  * @param  Size: Amount of data to be received
  * @param  Timeout: Timeout duration
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Receive(SAI_HandleTypeDef *hsai, uint8_t *pData, uint16_t Size, uint32_t Timeout)
{
  uint32_t tickstart = 0;
  
  if((pData == NULL ) || (Size == 0)) 
  {
    return  HAL_ERROR;
  }
  
  if(hsai->State == HAL_SAI_STATE_READY)
  { 
    /* Process Locked */
    __HAL_LOCK(hsai);
    
    hsai->State = HAL_SAI_STATE_BUSY_RX;
    hsai->ErrorCode = HAL_SAI_ERROR_NONE;
    hsai->pBuffPtr = pData;
    hsai->XferSize = Size;
    hsai->XferCount = Size;
    
    /* Check if the SAI is already enabled */ 
    if((hsai->Instance->CR1 & SAI_xCR1_SAIEN) != SAI_xCR1_SAIEN)
    {
      /* Enable SAI peripheral */    
      __HAL_SAI_ENABLE(hsai);
    }
    
    /* Receive data */
    while(hsai->XferCount > 0)
    {
      
      if((hsai->Instance->SR & SAI_xSR_FLVL) != SAI_FIFOSTATUS_EMPTY)
      {
        if((hsai->Init.DataSize == SAI_DATASIZE_8) && (hsai->Init.CompandingMode == SAI_NOCOMPANDING))
        {
          (*hsai->pBuffPtr++) = hsai->Instance->DR;
        }
        else if(hsai->Init.DataSize <= SAI_DATASIZE_16)
        {
          *((uint16_t*)hsai->pBuffPtr) = hsai->Instance->DR;
          hsai->pBuffPtr+= 2;
        }
        else
        {
          *((uint32_t*)hsai->pBuffPtr) = hsai->Instance->DR;
          hsai->pBuffPtr+= 4;
        }  
        hsai->XferCount--; 
      }
      else
      {
        /* Get tick */
        tickstart = HAL_GetTick();
        /* Check for the Timeout */
        if(Timeout != HAL_MAX_DELAY)
        {
          if((Timeout == 0)||((HAL_GetTick() - tickstart ) > Timeout))
          {
            /* Update error code */
            hsai->ErrorCode |= HAL_SAI_ERROR_TIMEOUT;
            
            /* Process Unlocked */
            __HAL_UNLOCK(hsai);
            
            /* Change the SAI state */
            hsai->State = HAL_SAI_STATE_TIMEOUT;
            
            return HAL_TIMEOUT;
          }
        }
      }
    }      
    
    hsai->State = HAL_SAI_STATE_READY; 
    
    /* Process Unlocked */
    __HAL_UNLOCK(hsai);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;
  }
}

/**
  * @brief  Transmits an amount of data in no-blocking mode with Interrupt.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  pData: Pointer to data buffer
  * @param  Size: Amount of data to be sent
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Transmit_IT(SAI_HandleTypeDef *hsai, uint8_t *pData, uint16_t Size)
{  
  if(hsai->State == HAL_SAI_STATE_READY)
  {
    if((pData == NULL) || (Size == 0)) 
    {
      return  HAL_ERROR;
    }
    
    hsai->pBuffPtr = pData;
    hsai->XferSize = Size;
    hsai->XferCount = Size;
    
    /* Process Locked */
    __HAL_LOCK(hsai);
    
    hsai->State = HAL_SAI_STATE_BUSY_TX;
    
    if((hsai->Init.DataSize == SAI_DATASIZE_8) && (hsai->Init.CompandingMode == SAI_NOCOMPANDING))
    {
      hsai->InterruptServiceRoutine = SAI_Transmit_IT8Bit;
    }
    else if(hsai->Init.DataSize <= SAI_DATASIZE_16)
    {
      hsai->InterruptServiceRoutine = SAI_Transmit_IT16Bit;
    }
    else
    {
      hsai->InterruptServiceRoutine = SAI_Transmit_IT32Bit;
    }
    
    /* Enable FRQ and OVRUDR interrupts */
    __HAL_SAI_ENABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT));
    
    /* Check if the SAI is already enabled */ 
    if((hsai->Instance->CR1 & SAI_xCR1_SAIEN) != SAI_xCR1_SAIEN)
    {
      /* Fill the fifo before starting the communication */
      SAI_FillFifo(hsai);
      
      /* Enable SAI peripheral */    
      __HAL_SAI_ENABLE(hsai);
    }
    /* Process Unlocked */
    __HAL_UNLOCK(hsai);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;
  }
}

/**
  * @brief  Receives an amount of data in no-blocking mode with Interrupt.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  pData: Pointer to data buffer
  * @param  Size: Amount of data to be received
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Receive_IT(SAI_HandleTypeDef *hsai, uint8_t *pData, uint16_t Size)
{
  
  if(hsai->State == HAL_SAI_STATE_READY)
  {
    if((pData == NULL) || (Size == 0)) 
    {
      return  HAL_ERROR;
    }
    
    hsai->pBuffPtr = pData;
    hsai->XferSize = Size;
    hsai->XferCount = Size;
    
    /* Process Locked */
    __HAL_LOCK(hsai);
    
    hsai->State = HAL_SAI_STATE_BUSY_RX;
    
    if((hsai->Init.DataSize == SAI_DATASIZE_8) && (hsai->Init.CompandingMode == SAI_NOCOMPANDING))
    {
      hsai->InterruptServiceRoutine = SAI_Receive_IT8Bit;
    }
    else if(hsai->Init.DataSize <= SAI_DATASIZE_16)
    {
      hsai->InterruptServiceRoutine = SAI_Receive_IT16Bit;
    }
    else
    {
      hsai->InterruptServiceRoutine = SAI_Receive_IT32Bit;
    }    
    /* Enable TXE and OVRUDR interrupts */
    __HAL_SAI_ENABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT));
    
    /* Check if the SAI is already enabled */ 
    if((hsai->Instance->CR1 & SAI_xCR1_SAIEN) != SAI_xCR1_SAIEN)
    {
      /* Enable SAI peripheral */    
      __HAL_SAI_ENABLE(hsai);
    }
    
    /* Process Unlocked */
    __HAL_UNLOCK(hsai);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY; 
  } 
}

/**
  * @brief Pauses the audio stream playing from the Media.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_DMAPause(SAI_HandleTypeDef *hsai)
{
  /* Process Locked */
  __HAL_LOCK(hsai);
  
  /* Pause the audio file playing by disabling the SAI DMA requests */
  hsai->Instance->CR1 &= ~SAI_xCR1_DMAEN;
  
  /* Process Unlocked */
  __HAL_UNLOCK(hsai);
  
  return HAL_OK; 
}

/**
  * @brief Resumes the audio stream playing from the Media.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_DMAResume(SAI_HandleTypeDef *hsai)
{
  /* Process Locked */
  __HAL_LOCK(hsai);
  
  /* Enable the SAI DMA requests */
  hsai->Instance->CR1 |= SAI_xCR1_DMAEN;
  
  /* If the SAI peripheral is still not enabled, enable it */
  if ((hsai->Instance->CR1 & SAI_xCR1_SAIEN) == RESET)
  {
    /* Enable SAI peripheral */    
    __HAL_SAI_ENABLE(hsai);
  }
  
  /* Process Unlocked */
  __HAL_UNLOCK(hsai);
  
  return HAL_OK;
}

/**
  * @brief Stops the audio stream playing from the Media.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_DMAStop(SAI_HandleTypeDef *hsai)
{
  /* Process Locked */
  __HAL_LOCK(hsai);
  
  /* Disable the SAI DMA request */
  hsai->Instance->CR1 &= ~SAI_xCR1_DMAEN;
  
  /* Abort the SAI DMA Tx Stream */
  if(hsai->hdmatx != NULL)
  {
    HAL_DMA_Abort(hsai->hdmatx);
  }
  /* Abort the SAI DMA Rx Stream */
  if(hsai->hdmarx != NULL)
  {  
    HAL_DMA_Abort(hsai->hdmarx);
  }

  /* Disable SAI peripheral */
  SAI_Disable(hsai);
  
  hsai->State = HAL_SAI_STATE_READY;
  
  /* Process Unlocked */
  __HAL_UNLOCK(hsai);
  
  return HAL_OK;
}

/**
  * @brief Abort the current transfer and disbaled the SAI.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Abort(SAI_HandleTypeDef *hsai)
{
  /* Disable the SAI DMA request */
  hsai->Instance->CR1 &= ~SAI_xCR1_DMAEN;
  
  /* Abort the SAI DMA Tx Stream */
  if(hsai->hdmatx != NULL)
  {
    HAL_DMA_Abort(hsai->hdmatx);
  }
  /* Abort the SAI DMA Rx Stream */
  if(hsai->hdmarx != NULL)
  {  
    HAL_DMA_Abort(hsai->hdmarx);
  }

  /* Disabled All interrupt and clear all the flag */
  hsai->Instance->IMR = 0;
  hsai->Instance->CLRFR = 0xFFFFFFFF;
  
  /* Disable SAI peripheral */
  SAI_Disable(hsai);
  
  /* Flush the fifo */
  SET_BIT(hsai->Instance->CR2, SAI_xCR2_FFLUSH);
  
  hsai->State = HAL_SAI_STATE_READY;
  
  /* Process Unlocked */
  __HAL_UNLOCK(hsai);
  
  return HAL_OK;
}

/**
  * @brief  Transmits an amount of data in no-blocking mode with DMA.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  pData: Pointer to data buffer
  * @param  Size: Amount of data to be sent
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Transmit_DMA(SAI_HandleTypeDef *hsai, uint8_t *pData, uint16_t Size)
{
  uint32_t *tmp;
  
  if((pData == NULL) || (Size == 0)) 
  {
    return  HAL_ERROR;
  }
  
  if(hsai->State == HAL_SAI_STATE_READY)
  {  
    hsai->pBuffPtr = pData;
    hsai->XferSize = Size;
    hsai->XferCount = Size;
    
    /* Process Locked */
    __HAL_LOCK(hsai);
    
    hsai->State = HAL_SAI_STATE_BUSY_TX;
    
    /* Set the SAI Tx DMA Half transfer complete callback */
    hsai->hdmatx->XferHalfCpltCallback = SAI_DMATxHalfCplt;
    
    /* Set the SAI TxDMA transfer complete callback */
    hsai->hdmatx->XferCpltCallback = SAI_DMATxCplt;
    
    /* Set the DMA error callback */
    hsai->hdmatx->XferErrorCallback = SAI_DMAError;
    
    /* Enable the Tx DMA Stream */
    tmp = (uint32_t*)&pData;
    HAL_DMA_Start_IT(hsai->hdmatx, *(uint32_t*)tmp, (uint32_t)&hsai->Instance->DR, hsai->XferSize);
    
    /* Check if the SAI is already enabled */ 
    if((hsai->Instance->CR1 & SAI_xCR1_SAIEN) != SAI_xCR1_SAIEN)
    {
      /* Enable SAI peripheral */
      __HAL_SAI_ENABLE(hsai);
    }
    
    /* Enable the interrupts for error handling */
    __HAL_SAI_ENABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_DMA));
    
    /* Enable SAI Tx DMA Request */  
    hsai->Instance->CR1 |= SAI_xCR1_DMAEN;
    
    /* Process Unlocked */
    __HAL_UNLOCK(hsai);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;
  }
}

/**
  * @brief  Receives an amount of data in no-blocking mode with DMA. 
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  pData: Pointer to data buffer
  * @param  Size: Amount of data to be received
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_Receive_DMA(SAI_HandleTypeDef *hsai, uint8_t *pData, uint16_t Size)
{
  uint32_t *tmp;
  
  if((pData == NULL) || (Size == 0))
  {
    return  HAL_ERROR;
  } 
  
  if(hsai->State == HAL_SAI_STATE_READY)
  {    
    hsai->pBuffPtr = pData;
    hsai->XferSize = Size;
    hsai->XferCount = Size;
    
    /* Process Locked */
    __HAL_LOCK(hsai);
    
    hsai->State = HAL_SAI_STATE_BUSY_RX;
    
    /* Set the SAI Rx DMA Half transfer complete callback */
    hsai->hdmarx->XferHalfCpltCallback = SAI_DMARxHalfCplt;
    
    /* Set the SAI Rx DMA transfer complete callback */
    hsai->hdmarx->XferCpltCallback = SAI_DMARxCplt;
    
    /* Set the DMA error callback */
    hsai->hdmarx->XferErrorCallback = SAI_DMAError;
    
    /* Enable the Rx DMA Stream */
    tmp = (uint32_t*)&pData;
    HAL_DMA_Start_IT(hsai->hdmarx, (uint32_t)&hsai->Instance->DR, *(uint32_t*)tmp, hsai->XferSize);
    
    /* Check if the SAI is already enabled */
    if((hsai->Instance->CR1 & SAI_xCR1_SAIEN) != SAI_xCR1_SAIEN)
    {
      /* Enable SAI peripheral */
      __HAL_SAI_ENABLE(hsai);
    }
    
    /* Enable the interrupts for error handling */
    __HAL_SAI_ENABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_DMA));
    
    /* Enable SAI Rx DMA Request */
    hsai->Instance->CR1 |= SAI_xCR1_DMAEN;
    
    /* Process Unlocked */
    __HAL_UNLOCK(hsai);
    
    return HAL_OK;
  }
  else
  {
    return HAL_BUSY;
  }
}

/**
  * @brief  Enable the tx mute mode.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  val :  value sent during the mute @ref SAI_Block_Mute_Value
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_EnableTxMuteMode(SAI_HandleTypeDef *hsai, uint16_t val)
{
  assert_param(IS_SAI_BLOCK_MUTE_VALUE(val));
  
  if(hsai->State != HAL_SAI_STATE_RESET)
  {
    CLEAR_BIT(hsai->Instance->CR2, SAI_xCR2_MUTEVAL | SAI_xCR2_MUTE);
    SET_BIT(hsai->Instance->CR2, SAI_xCR2_MUTE | val);
    return HAL_OK;
  }
  return HAL_ERROR;
}

/**
  * @brief  Disable the tx mute mode.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_DisableTxMuteMode(SAI_HandleTypeDef *hsai)
{
  if(hsai->State != HAL_SAI_STATE_RESET)
  {
    CLEAR_BIT(hsai->Instance->CR2, SAI_xCR2_MUTEVAL | SAI_xCR2_MUTE);
    return HAL_OK;
  }
  return HAL_ERROR;
}

/**
  * @brief  Enable the rx mute detection.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  callback : function called when the mute is detected
  * @param  counter : number a data before mute detection max 63.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_EnableRxMuteMode(SAI_HandleTypeDef *hsai, SAIcallback callback, uint16_t counter)
{
  assert_param(IS_SAI_BLOCK_MUTE_COUNTER(counter));
  
  if(hsai->State != HAL_SAI_STATE_RESET)
  {
    /* set the mute counter */
    CLEAR_BIT(hsai->Instance->CR2, SAI_xCR2_MUTECNT);
    SET_BIT(hsai->Instance->CR2, (uint32_t)((uint32_t)counter << 6));
    hsai->mutecallback = callback;
    /* enable the IT interrupt */
    __HAL_SAI_ENABLE_IT(hsai, SAI_IT_MUTEDET);
    return HAL_OK;
  }
  return HAL_ERROR;
}

/**
  * @brief  Disable the rx mute detection.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_SAI_DisableRxMuteMode(SAI_HandleTypeDef *hsai)
{
  if(hsai->State != HAL_SAI_STATE_RESET)
  {
    /* set the mutecallback to NULL */
    hsai->mutecallback = (SAIcallback)NULL;
    /* enable the IT interrupt */
    __HAL_SAI_DISABLE_IT(hsai, SAI_IT_MUTEDET);
    return HAL_OK;
  }
  return HAL_ERROR;
}

/**
  * @brief  This function handles SAI interrupt request.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL status
  */
void HAL_SAI_IRQHandler(SAI_HandleTypeDef *hsai)
{ 
  if(hsai->State != HAL_SAI_STATE_RESET)
  {
    uint32_t tmpFlag = hsai->Instance->SR;
    uint32_t tmpItSource = hsai->Instance->IMR; 
    
    if(((tmpFlag & SAI_xSR_FREQ) == SAI_xSR_FREQ) && ((tmpItSource & SAI_IT_FREQ) == SAI_IT_FREQ))
    {
      hsai->InterruptServiceRoutine(hsai);
    }
    
    /* check the flag only if one of them is set */
    if(tmpFlag != 0x00000000)
    {
      /* SAI Overrun error interrupt occurred ----------------------------------*/
      if(((tmpFlag & SAI_FLAG_OVRUDR) == SAI_FLAG_OVRUDR) && ((tmpItSource & SAI_IT_OVRUDR) == SAI_IT_OVRUDR))
      {
        /* Clear the SAI Overrun flag */
        __HAL_SAI_CLEAR_FLAG(hsai, SAI_FLAG_OVRUDR);
        /* Change the SAI error code */
        hsai->ErrorCode = ((hsai->State == HAL_SAI_STATE_BUSY_RX) ? HAL_SAI_ERROR_OVR : HAL_SAI_ERROR_UDR);
        /* the transfer is not stopped, we will forward the information to the user and we let the user decide what needs to be done */
        HAL_SAI_ErrorCallback(hsai);
      }
      
      /* SAI mutedet interrupt occurred ----------------------------------*/
      if(((tmpFlag & SAI_FLAG_MUTEDET) == SAI_FLAG_MUTEDET) && ((tmpItSource & SAI_IT_MUTEDET) == SAI_IT_MUTEDET))
      {
        /* Clear the SAI mutedet flag */
        __HAL_SAI_CLEAR_FLAG(hsai, SAI_FLAG_MUTEDET);
        /* call the call back function */
        if(hsai->mutecallback != (SAIcallback)NULL)
        {
          /* inform the user that an RX mute event has been detected */
          hsai->mutecallback();
        }
      }
      
      /* SAI AFSDET interrupt occurred ----------------------------------*/
      if(((tmpFlag & SAI_FLAG_AFSDET) == SAI_FLAG_AFSDET) && ((tmpItSource & SAI_IT_AFSDET) == SAI_IT_AFSDET))
      {
        /* Change the SAI error code */
        hsai->ErrorCode = HAL_SAI_ERROR_AFSDET;
        HAL_SAI_Abort(hsai);
        HAL_SAI_ErrorCallback(hsai);
      }
      
      /* SAI LFSDET interrupt occurred ----------------------------------*/
      if(((tmpFlag & SAI_FLAG_LFSDET) == SAI_FLAG_LFSDET) && ((tmpItSource & SAI_IT_LFSDET) == SAI_IT_LFSDET))
      {
        /* Change the SAI error code */
        hsai->ErrorCode = HAL_SAI_ERROR_LFSDET;
        HAL_SAI_Abort(hsai);
        HAL_SAI_ErrorCallback(hsai);
      }

      /* SAI WCKCFG interrupt occurred ----------------------------------*/
      if(((tmpFlag & SAI_FLAG_WCKCFG) == SAI_FLAG_WCKCFG) && ((tmpItSource & SAI_IT_WCKCFG) == SAI_IT_WCKCFG))
      {
        /* Change the SAI error code */
        hsai->ErrorCode = HAL_SAI_ERROR_WCKCFG;
        HAL_SAI_Abort(hsai);
        HAL_SAI_ErrorCallback(hsai);
      }
    }
  }
}

/**
  * @brief Tx Transfer completed callbacks.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None
  */
 __weak void HAL_SAI_TxCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_SAI_TxCpltCallback could be implemented in the user file
   */ 
}

/**
  * @brief Tx Transfer Half completed callbacks
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None
  */
 __weak void HAL_SAI_TxHalfCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_SAI_TxHalfCpltCallback could be implemented in the user file
   */ 
}

/**
  * @brief Rx Transfer completed callbacks.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None
  */
__weak void HAL_SAI_RxCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_SAI_RxCpltCallback could be implemented in the user file
   */
}

/**
  * @brief Rx Transfer half completed callbacks
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None
  */
__weak void HAL_SAI_RxHalfCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_SAI_RxCpltCallback could be implemented in the user file
   */
}

/**
  * @brief SAI error callbacks.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None
  */
__weak void HAL_SAI_ErrorCallback(SAI_HandleTypeDef *hsai)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_SAI_ErrorCallback could be implemented in the user file
   */ 
}

/**
  * @}
  */


/** @defgroup SAI_Exported_Functions_Group3 Peripheral State functions 
 *  @brief   Peripheral State functions 
 *
@verbatim   
 ===============================================================================
                ##### Peripheral State and Errors functions #####
 ===============================================================================  
    [..]
    This subsection permits to get in run-time the status of the peripheral 
    and the data flow.

@endverbatim
  * @{
  */

/**
  * @brief  Returns the SAI state.
  * @param  hsai: pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval HAL state
  */
HAL_SAI_StateTypeDef HAL_SAI_GetState(SAI_HandleTypeDef *hsai)
{
  return hsai->State;
}

/**
* @brief  Return the SAI error code
* @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *              the configuration information for the specified SAI Block.
* @retval SAI Error Code
*/
uint32_t HAL_SAI_GetError(SAI_HandleTypeDef *hsai)
{
  return hsai->ErrorCode;
}
/**
  * @}
  */

/**
  * @brief  Initializes the SAI I2S protocol according to the specified parameters 
  *         in the SAI_InitTypeDef and create the associated handle.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  protocol : one of the supported protocol
  * @param  datasize : one of the supported datasize @ref SAI_Protocol_DataSize
  *                the configuration information for SAI module.
  * @param  nbslot : number of slot minimum value is 2 and max is 16. 
  *                    the value must be a multiple of 2.
  * @retval HAL status
  */
static HAL_StatusTypeDef SAI_InitI2S(SAI_HandleTypeDef *hsai, uint32_t protocol, uint32_t datasize, uint32_t nbslot)
{
  /* Check the parameters */
  assert_param(IS_SAI_SUPPORTED_PROTOCOL(protocol));
  assert_param(IS_SAI_PROTOCOL_DATASIZE(datasize));
  
  hsai->Init.Protocol            = SAI_FREE_PROTOCOL;
  hsai->Init.FirstBit            = SAI_FIRSTBIT_MSB;
  hsai->Init.ClockStrobing       = SAI_CLOCKSTROBING_FALLINGEDGE;
  hsai->FrameInit.FSDefinition   = SAI_FS_CHANNEL_IDENTIFICATION;
  hsai->SlotInit.SlotActive      = SAI_SLOTACTIVE_ALL;
  hsai->SlotInit.FirstBitOffset  = 0;
  hsai->SlotInit.SlotNumber      = nbslot;
  
  /* in IS2 the number of slot must be even */
  if((nbslot & 0x1) != 0 )
  {
    return HAL_ERROR;
  }
    
  switch(protocol)
  {
  case SAI_I2S_STANDARD :
    hsai->FrameInit.FSPolarity = SAI_FS_ACTIVE_LOW;
    hsai->FrameInit.FSOffset   = SAI_FS_BEFOREFIRSTBIT;
    break;
  case SAI_I2S_MSBJUSTIFIED :
  case SAI_I2S_LSBJUSTIFIED :
    hsai->FrameInit.FSPolarity = SAI_FS_ACTIVE_HIGH;
    hsai->FrameInit.FSOffset   = SAI_FS_FIRSTBIT;
    break;
  default :
    return HAL_ERROR;
  }
   
  /* Frame definition */
  hsai->Init.DataSize = 0xFFFFFFFF;
  switch(datasize)
  {
  case SAI_PROTOCOL_DATASIZE_16BIT:
    hsai->Init.DataSize = SAI_DATASIZE_16;
    hsai->FrameInit.FrameLength = 32*(nbslot/2);
    hsai->FrameInit.ActiveFrameLength = 16*(nbslot/2);
    hsai->SlotInit.SlotSize = SAI_SLOTSIZE_16B;
    break; 
  case SAI_PROTOCOL_DATASIZE_16BITEXTENDED :
    if(hsai->Init.DataSize == 0xFFFFFFFF)
    {
      hsai->Init.DataSize = SAI_DATASIZE_16;
    }
    break; 
  case SAI_PROTOCOL_DATASIZE_24BIT:
    if(hsai->Init.DataSize == 0xFFFFFFFF)
    {
      hsai->Init.DataSize = SAI_DATASIZE_24;
    }
    break;
  case SAI_PROTOCOL_DATASIZE_32BIT: 
    if(hsai->Init.DataSize == 0xFFFFFFFF)
    {
      hsai->Init.DataSize = SAI_DATASIZE_32;
    }
    hsai->FrameInit.FrameLength = 64*(nbslot/2);
    hsai->FrameInit.ActiveFrameLength = 32*(nbslot/2);
    hsai->SlotInit.SlotSize = SAI_SLOTSIZE_32B;
    if(protocol == SAI_I2S_LSBJUSTIFIED)
    {
      if (datasize == SAI_PROTOCOL_DATASIZE_16BITEXTENDED)
      {
        hsai->SlotInit.FirstBitOffset = 16;
      }
      if (datasize == SAI_PROTOCOL_DATASIZE_24BIT)
      {
        hsai->SlotInit.FirstBitOffset = 8;
      }
    }
    break;
  default :
    return HAL_ERROR;
  }
 
  return HAL_OK;
}

/**
  * @brief  Initializes the SAI PCM protocol according to the specified parameters 
  *         in the SAI_InitTypeDef and create the associated handle.
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  protocol : one of the supported protocol
  * @param  datasize : one of the supported datasize @ref SAI_Protocol_DataSize
  * @param  nbslot : number of slot minimum value is 1 and the max is 16.
  * @retval HAL status
  */
static HAL_StatusTypeDef SAI_InitPCM(SAI_HandleTypeDef *hsai, uint32_t protocol, uint32_t datasize, uint32_t nbslot)
{
  /* Check the parameters */
  assert_param(IS_SAI_SUPPORTED_PROTOCOL(protocol));
  assert_param(IS_SAI_PROTOCOL_DATASIZE(datasize));

  hsai->Init.Protocol            = SAI_FREE_PROTOCOL;
  hsai->Init.FirstBit            = SAI_FIRSTBIT_MSB;
  hsai->Init.ClockStrobing       = SAI_CLOCKSTROBING_FALLINGEDGE;
  hsai->FrameInit.FSDefinition   = SAI_FS_STARTFRAME;
  hsai->FrameInit.FSPolarity     = SAI_FS_ACTIVE_HIGH;
  hsai->FrameInit.FSOffset       = SAI_FS_BEFOREFIRSTBIT;
  hsai->SlotInit.FirstBitOffset  = 0;
  hsai->SlotInit.SlotNumber      = nbslot;
  hsai->SlotInit.SlotActive      = SAI_SLOTACTIVE_ALL;
  
  switch(protocol)
  {
  case SAI_PCM_SHORT :
    hsai->FrameInit.ActiveFrameLength = 1;
    break;
  case SAI_PCM_LONG :
    hsai->FrameInit.ActiveFrameLength = 13;
    break;
  default :
    return HAL_ERROR;
  }
 
  switch(datasize)
  {
  case SAI_PROTOCOL_DATASIZE_16BIT:
    hsai->Init.DataSize = SAI_DATASIZE_16;
    hsai->FrameInit.FrameLength = 16 * nbslot;
    hsai->SlotInit.SlotSize = SAI_SLOTSIZE_16B;
    break; 
  case SAI_PROTOCOL_DATASIZE_16BITEXTENDED :
    hsai->Init.DataSize = SAI_DATASIZE_16;
    hsai->FrameInit.FrameLength = 32 * nbslot;
    hsai->SlotInit.SlotSize = SAI_SLOTSIZE_32B;
    break;
    
  case SAI_PROTOCOL_DATASIZE_32BIT: 
    hsai->Init.DataSize = SAI_DATASIZE_32;
    hsai->FrameInit.FrameLength = 32 * nbslot;
    hsai->SlotInit.SlotSize = SAI_SLOTSIZE_32B;
    break;
  default :
    return HAL_ERROR;
  }
 
  return HAL_OK;
}

/**
  * @brief  Fill the fifo 
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static void SAI_FillFifo(SAI_HandleTypeDef *hsai)
{
  /* fill the fifo with data before to enabled the SAI */
  while((hsai->Instance->SR & SAI_xSR_FLVL) != SAI_FIFOSTATUS_FULL)
  {
    if((hsai->Init.DataSize == SAI_DATASIZE_8) && (hsai->Init.CompandingMode == SAI_NOCOMPANDING))
    {
      hsai->Instance->DR = (*hsai->pBuffPtr++);
    }
    else if(hsai->Init.DataSize <= SAI_DATASIZE_16)
    {
      hsai->Instance->DR = *((uint32_t *)hsai->pBuffPtr);
      hsai->pBuffPtr+= 2;
    }
    else
    {
      hsai->Instance->DR = *((uint32_t *)hsai->pBuffPtr);
      hsai->pBuffPtr+= 4;
    }
    hsai->XferCount--;
  }
}

/**
  * @brief  return the interrupt flag to set according the SAI setup 
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @param  mode : SAI_MODE_DMA or SAI_MODE_IT
  * @retval the list of the IT flag to enable
 */
static uint32_t SAI_InterruptFlag(SAI_HandleTypeDef *hsai, uint32_t mode)
{
  uint32_t tmpIT = SAI_IT_OVRUDR; 
  
  if(mode == SAI_MODE_IT)
  {
    tmpIT|= SAI_IT_FREQ;
  }
  
  if((hsai->Init.AudioMode == SAI_MODESLAVE_RX) || (hsai->Init.AudioMode == SAI_MODESLAVE_TX))
  {
    tmpIT|= SAI_IT_AFSDET | SAI_IT_LFSDET;
  }
  else
  {
    /* hsai has been configured in master mode */
    tmpIT|= SAI_IT_WCKCFG;
  }
  return tmpIT;
}

/**
  * @brief  disable the SAI and wait the disabling
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static HAL_StatusTypeDef SAI_Disable(SAI_HandleTypeDef *hsai)
{
  uint32_t tickstart = HAL_GetTick();
  HAL_StatusTypeDef status = HAL_OK;
  
  __HAL_SAI_DISABLE(hsai);
  while((hsai->Instance->CR1 & SAI_xCR1_SAIEN) != RESET)
  {
    /* Check for the Timeout */
    if((HAL_GetTick() - tickstart ) > SAI_TIMEOUT_VALUE)
    {         
      /* Update error code */
      hsai->ErrorCode |= HAL_SAI_ERROR_TIMEOUT;
      
      status = HAL_TIMEOUT;
      
      /* Change the SAI state */
      HAL_SAI_ErrorCallback(hsai);
    }
  }
  return status;
}

/**
  * @brief  Tx Handler for Transmit in Interrupt mode 8Bit transfer
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static void SAI_Transmit_IT8Bit(SAI_HandleTypeDef *hsai)
{
  /* Write data on DR register */
  hsai->Instance->DR = (*hsai->pBuffPtr++);
  hsai->XferCount--;
  
  /* Handle the end of the transmission */
  if(hsai->XferCount == 0)
  {
    /* Disable FREQ and OVRUDR interrupts */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT)); 
    hsai->State = HAL_SAI_STATE_READY;
    HAL_SAI_TxCpltCallback(hsai);
  }
}

/**
  * @brief  Tx Handler for Transmit in Interrupt mode for 16Bit transfer
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static void SAI_Transmit_IT16Bit(SAI_HandleTypeDef *hsai)
{
  /* Write data on DR register */
  hsai->Instance->DR = *(uint16_t *)hsai->pBuffPtr;
  hsai->pBuffPtr+=2;
  hsai->XferCount--;
  
  /* Handle the end of the transmission */
  if(hsai->XferCount == 0)
  {
    /* Disable FREQ and OVRUDR interrupts */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT)); 
    hsai->State = HAL_SAI_STATE_READY;
    HAL_SAI_TxCpltCallback(hsai);
  }
}

/**
  * @brief  Tx Handler for Transmit in Interrupt mode for 32Bit transfer
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static void SAI_Transmit_IT32Bit(SAI_HandleTypeDef *hsai)
{
  /* Write data on DR register */
  hsai->Instance->DR = *(uint32_t *)hsai->pBuffPtr;
  hsai->pBuffPtr+=4;
  hsai->XferCount--;
  
  /* Handle the end of the transmission */
  if(hsai->XferCount == 0)
  {
    /* Disable FREQ and OVRUDR interrupts */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT)); 
    hsai->State = HAL_SAI_STATE_READY;
    HAL_SAI_TxCpltCallback(hsai);
  }
}

/**
  * @brief  Rx Handler for Receive in Interrupt mode 8Bit transfer
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static void SAI_Receive_IT8Bit(SAI_HandleTypeDef *hsai)
{
  /* Receive data */    
  (*hsai->pBuffPtr++) = hsai->Instance->DR;
  hsai->XferCount--;
  
  /* Check end of the transfer */  
  if(hsai->XferCount == 0)
  {    
    /* Disable TXE and OVRUDR interrupts */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT));
    
    /* Clear the SAI Overrun flag */
    __HAL_SAI_CLEAR_FLAG(hsai, SAI_FLAG_OVRUDR);
    
    hsai->State = HAL_SAI_STATE_READY;
    HAL_SAI_RxCpltCallback(hsai); 
  }
}

/**
  * @brief  Rx Handler for Receive in Interrupt mode for 16Bit transfer
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static void SAI_Receive_IT16Bit(SAI_HandleTypeDef *hsai)
{
  /* Receive data */    
  *(uint16_t*)hsai->pBuffPtr = hsai->Instance->DR;
  hsai->pBuffPtr+=2;
  hsai->XferCount--;
  
  /* Check end of the transfer */  
  if(hsai->XferCount == 0)
  {    
    /* Disable TXE and OVRUDR interrupts */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT));
    
    /* Clear the SAI Overrun flag */
    __HAL_SAI_CLEAR_FLAG(hsai, SAI_FLAG_OVRUDR);
    
    hsai->State = HAL_SAI_STATE_READY;
    HAL_SAI_RxCpltCallback(hsai); 
  }
}
/**
  * @brief  Rx Handler for Receive in Interrupt mode for 32Bit transfer
  * @param  hsai : pointer to a SAI_HandleTypeDef structure that contains
  *                the configuration information for SAI module.
  * @retval None.
  */
static void SAI_Receive_IT32Bit(SAI_HandleTypeDef *hsai)
{
  /* Receive data */    
  *(uint32_t*)hsai->pBuffPtr = hsai->Instance->DR;
  hsai->pBuffPtr+=4;
  hsai->XferCount--;
  
  /* Check end of the transfer */  
  if(hsai->XferCount == 0)
  {    
    /* Disable TXE and OVRUDR interrupts */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_IT));
    
    /* Clear the SAI Overrun flag */
    __HAL_SAI_CLEAR_FLAG(hsai, SAI_FLAG_OVRUDR);
    
    hsai->State = HAL_SAI_STATE_READY;
    HAL_SAI_RxCpltCallback(hsai); 
  }
}

/**
  * @brief DMA SAI transmit process complete callback.
  * @param  hdma: pointer to a DMA_HandleTypeDef structure that contains
  *                the configuration information for the specified DMA module.
  * @retval None
  */
static void SAI_DMATxCplt(DMA_HandleTypeDef *hdma)   
{
  uint32_t tickstart = 0;
  
  SAI_HandleTypeDef* hsai = (SAI_HandleTypeDef*)((DMA_HandleTypeDef* )hdma)->Parent;
  
  if((hdma->Instance->CR & DMA_SxCR_CIRC) == 0)
  { 
    hsai->XferCount = 0;
    
    /* Disable SAI Tx DMA Request */  
    hsai->Instance->CR1 &= (uint32_t)(~SAI_xCR1_DMAEN);
    
    /* Get tick */
    tickstart = HAL_GetTick();
    
    /* Set timeout: 10 is the max delay to send the remaining data in the SAI FIFO */
    /* Wait until FIFO is empty */    
    while(__HAL_SAI_GET_FLAG(hsai, SAI_xSR_FLVL) != RESET)
    {
      /* Check for the Timeout */
      if((HAL_GetTick() - tickstart ) > SAI_TIMEOUT_VALUE)
      {         
        /* Update error code */
        hsai->ErrorCode |= HAL_SAI_ERROR_TIMEOUT;
        
        /* Change the SAI state */
        HAL_SAI_ErrorCallback(hsai);
      }
    } 
    
    /* Stop the interrupts error handling */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_DMA));
    
    hsai->State= HAL_SAI_STATE_READY;
  }
  HAL_SAI_TxCpltCallback(hsai);
}

/**
  * @brief DMA SAI transmit process half complete callback 
  * @param  hdma: pointer to a DMA_HandleTypeDef structure that contains
  *                the configuration information for the specified DMA module.
  * @retval None
  */
static void SAI_DMATxHalfCplt(DMA_HandleTypeDef *hdma)
{
  SAI_HandleTypeDef* hsai = (SAI_HandleTypeDef*)((DMA_HandleTypeDef*)hdma)->Parent;

  HAL_SAI_TxHalfCpltCallback(hsai);
}

/**
  * @brief DMA SAI receive process complete callback. 
  * @param  hdma: pointer to a DMA_HandleTypeDef structure that contains
  *                the configuration information for the specified DMA module.
  * @retval None
  */
static void SAI_DMARxCplt(DMA_HandleTypeDef *hdma)   
{
  SAI_HandleTypeDef* hsai = ( SAI_HandleTypeDef* )((DMA_HandleTypeDef* )hdma)->Parent;
  if((hdma->Instance->CR & DMA_SxCR_CIRC) == 0)
  {
    /* Disable Rx DMA Request */
    hsai->Instance->CR1 &= (uint32_t)(~SAI_xCR1_DMAEN);
    hsai->XferCount = 0;
    
    /* Stop the interrupts error handling */
    __HAL_SAI_DISABLE_IT(hsai, SAI_InterruptFlag(hsai, SAI_MODE_DMA));
    
    hsai->State = HAL_SAI_STATE_READY;
  }
  HAL_SAI_RxCpltCallback(hsai); 
}

/**
  * @brief DMA SAI receive process half complete callback 
  * @param  hdma: pointer to a DMA_HandleTypeDef structure that contains
  *                the configuration information for the specified DMA module.
  * @retval None
  */
static void SAI_DMARxHalfCplt(DMA_HandleTypeDef *hdma)
{
  SAI_HandleTypeDef* hsai = (SAI_HandleTypeDef*)((DMA_HandleTypeDef*)hdma)->Parent;

  HAL_SAI_RxHalfCpltCallback(hsai); 
}
/**
  * @brief DMA SAI communication error callback. 
  * @param  hdma: pointer to a DMA_HandleTypeDef structure that contains
  *                the configuration information for the specified DMA module.
  * @retval None
  */
static void SAI_DMAError(DMA_HandleTypeDef *hdma)   
{
  SAI_HandleTypeDef* hsai = ( SAI_HandleTypeDef* )((DMA_HandleTypeDef* )hdma)->Parent;
  
  /* Stop the DMA transfer */
  HAL_SAI_DMAStop(hsai);
  
  /* Set the SAI state ready to be able to start again the process */
  hsai->State= HAL_SAI_STATE_READY;
  HAL_SAI_ErrorCallback(hsai);
  
  hsai->XferCount = 0;
}

/**
  * @}
  */

#endif /* HAL_SAI_MODULE_ENABLED */
/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
