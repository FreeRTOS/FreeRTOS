/**
  ******************************************************************************
  * @file    stm32f7xx_hal_crc.c
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   CRC HAL module driver.
  *          This file provides firmware functions to manage the following 
  *          functionalities of the Cyclic Redundancy Check (CRC) peripheral:
  *           + Initialization and de-initialization functions
  *           + Peripheral Control functions 
  *           + Peripheral State functions
  *
  @verbatim
 ===============================================================================
                     ##### CRC How to use this driver #####
 ===============================================================================
    [..]

    (#) Enable CRC AHB clock using __HAL_RCC_CRC_CLK_ENABLE();

    (#) Initialize CRC calculator
         (++) specify generating polynomial (IP default or non-default one)
         (++) specify initialization value (IP default or non-default one)
         (++) specify input data format
         (++) specify input or output data inversion mode if any

    (#) Use HAL_CRC_Accumulate() function to compute the CRC value of the 
        input data buffer starting with the previously computed CRC as 
        initialization value

    (#) Use HAL_CRC_Calculate() function to compute the CRC value of the 
        input data buffer starting with the defined initialization value 
        (default or non-default) to initiate CRC calculation

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

/** @defgroup CRC CRC
  * @brief CRC HAL module driver.
  * @{
  */

#ifdef HAL_CRC_MODULE_ENABLED

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
static uint32_t CRC_Handle_8(CRC_HandleTypeDef *hcrc, uint8_t pBuffer[], uint32_t BufferLength);
static uint32_t CRC_Handle_16(CRC_HandleTypeDef *hcrc, uint16_t pBuffer[], uint32_t BufferLength);
/* Exported functions --------------------------------------------------------*/

/** @defgroup CRC_Exported_Functions CRC Exported Functions
  * @{
  */

/** @defgroup HAL_CRC_Group1 Initialization/de-initialization functions 
 *  @brief    Initialization and Configuration functions. 
 *
@verbatim    
 ===============================================================================
            ##### Initialization and de-initialization functions #####
 ===============================================================================
    [..]  This section provides functions allowing to:
      (+) Initialize the CRC according to the specified parameters 
          in the CRC_InitTypeDef and create the associated handle
      (+) DeInitialize the CRC peripheral
      (+) Initialize the CRC MSP
      (+) DeInitialize CRC MSP 
 
@endverbatim
  * @{
  */

/**
  * @brief  Initializes the CRC according to the specified
  *         parameters in the CRC_InitTypeDef and creates the associated handle.
  * @param  hcrc: CRC handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_CRC_Init(CRC_HandleTypeDef *hcrc)
{
  /* Check the CRC handle allocation */
  if(hcrc == NULL)
  {
    return HAL_ERROR;
  }

  /* Check the parameters */
  assert_param(IS_CRC_ALL_INSTANCE(hcrc->Instance));

  if(hcrc->State == HAL_CRC_STATE_RESET)
  {
    /* Allocate lock resource and initialize it */
    hcrc->Lock = HAL_UNLOCKED;
    /* Init the low level hardware */
    HAL_CRC_MspInit(hcrc);
  }
  
  /* Change CRC peripheral state */
  hcrc->State = HAL_CRC_STATE_BUSY;
  
  /* check whether or not non-default generating polynomial has been 
   * picked up by user */
  assert_param(IS_DEFAULT_POLYNOMIAL(hcrc->Init.DefaultPolynomialUse)); 
  if (hcrc->Init.DefaultPolynomialUse == DEFAULT_POLYNOMIAL_ENABLE)
  {
    /* initialize IP with default generating polynomial */
    WRITE_REG(hcrc->Instance->POL, DEFAULT_CRC32_POLY);  
    MODIFY_REG(hcrc->Instance->CR, CRC_CR_POLYSIZE, CRC_POLYLENGTH_32B);
  }
  else
  {
    /* initialize CRC IP with generating polynomial defined by user */
    if (HAL_CRCEx_Polynomial_Set(hcrc, hcrc->Init.GeneratingPolynomial, hcrc->Init.CRCLength) != HAL_OK)
    {
      return HAL_ERROR;
    }
  }
  
  /* check whether or not non-default CRC initial value has been 
   * picked up by user */
  assert_param(IS_DEFAULT_INIT_VALUE(hcrc->Init.DefaultInitValueUse));
  if (hcrc->Init.DefaultInitValueUse == DEFAULT_INIT_VALUE_ENABLE)
  {
    WRITE_REG(hcrc->Instance->INIT, DEFAULT_CRC_INITVALUE);  
  }
  else
  {
    WRITE_REG(hcrc->Instance->INIT, hcrc->Init.InitValue);
  }
  

  /* set input data inversion mode */
  assert_param(IS_CRC_INPUTDATA_INVERSION_MODE(hcrc->Init.InputDataInversionMode)); 
  MODIFY_REG(hcrc->Instance->CR, CRC_CR_REV_IN, hcrc->Init.InputDataInversionMode); 
  
  /* set output data inversion mode */
  assert_param(IS_CRC_OUTPUTDATA_INVERSION_MODE(hcrc->Init.OutputDataInversionMode)); 
  MODIFY_REG(hcrc->Instance->CR, CRC_CR_REV_OUT, hcrc->Init.OutputDataInversionMode);  
  
  /* makes sure the input data format (bytes, halfwords or words stream)
   * is properly specified by user */
  assert_param(IS_CRC_INPUTDATA_FORMAT(hcrc->InputDataFormat));

  /* Change CRC peripheral state */
  hcrc->State = HAL_CRC_STATE_READY;
  
  /* Return function status */
  return HAL_OK;
}

/**
  * @brief  DeInitializes the CRC peripheral.
  * @param  hcrc: CRC handle
  * @retval HAL status
  */
HAL_StatusTypeDef HAL_CRC_DeInit(CRC_HandleTypeDef *hcrc)
{
  /* Check the CRC handle allocation */
  if(hcrc == NULL)
  {
    return HAL_ERROR;
  }

  /* Check the parameters */
  assert_param(IS_CRC_ALL_INSTANCE(hcrc->Instance));
  
  /* Check the CRC peripheral state */
  if(hcrc->State == HAL_CRC_STATE_BUSY)
  {
    return HAL_BUSY;
  }
  
  /* Change CRC peripheral state */
  hcrc->State = HAL_CRC_STATE_BUSY;
  
  /* Reset CRC calculation unit */
  __HAL_CRC_DR_RESET(hcrc);

  /* DeInit the low level hardware */
  HAL_CRC_MspDeInit(hcrc);

  /* Change CRC peripheral state */
  hcrc->State = HAL_CRC_STATE_RESET;

  /* Process unlocked */
  __HAL_UNLOCK(hcrc);

  /* Return function status */
  return HAL_OK;
}

/**
  * @brief  Initializes the CRC MSP.
  * @param  hcrc: CRC handle
  * @retval None
  */
__weak void HAL_CRC_MspInit(CRC_HandleTypeDef *hcrc)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_CRC_MspInit can be implemented in the user file
   */
}

/**
  * @brief  DeInitializes the CRC MSP.
  * @param  hcrc: CRC handle
  * @retval None
  */
__weak void HAL_CRC_MspDeInit(CRC_HandleTypeDef *hcrc)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_CRC_MspDeInit can be implemented in the user file
   */
}

/**
  * @}
  */

/** @defgroup HAL_CRC_Group2 Peripheral Control functions 
 *  @brief   Peripheral Control functions 
 *
@verbatim  
 ==============================================================================
                      ##### Peripheral Control functions #####
 ==============================================================================  
    [..]  This section provides functions allowing to:
      (+) Compute the 7, 8, 16 or 32-bit CRC value of an 8, 16 or 32-bit data buffer
          using combination of the previous CRC value and the new one.
          
          or
          
      (+) Compute the 7, 8, 16 or 32-bit CRC value of an 8, 16 or 32-bit data buffer
          independently of the previous CRC value.

@endverbatim
  * @{
  */

/**                  
  * @brief  Compute the 7, 8, 16 or 32-bit CRC value of an 8, 16 or 32-bit data buffer
  *         starting with the previously computed CRC as initialization value.
  * @param  hcrc: CRC handle
  * @param  pBuffer: pointer to the input data buffer, exact input data format is
  *         provided by hcrc->InputDataFormat.  
  * @param  BufferLength: input data buffer length
  * @retval uint32_t CRC (returned value LSBs for CRC shorter than 32 bits)
  */
uint32_t HAL_CRC_Accumulate(CRC_HandleTypeDef *hcrc, uint32_t pBuffer[], uint32_t BufferLength)
{
  uint32_t index = 0; /* CRC input data buffer index */
  uint32_t temp = 0;  /* CRC output (read from hcrc->Instance->DR register) */
  
  /* Process locked */
  __HAL_LOCK(hcrc); 
    
  /* Change CRC peripheral state */  
  hcrc->State = HAL_CRC_STATE_BUSY;
  
  switch (hcrc->InputDataFormat)
  {
    case CRC_INPUTDATA_FORMAT_WORDS:  
      /* Enter Data to the CRC calculator */
      for(index = 0; index < BufferLength; index++)
      {
        hcrc->Instance->DR = pBuffer[index];
      }
      temp = hcrc->Instance->DR;
      break;
      
    case CRC_INPUTDATA_FORMAT_BYTES: 
      temp = CRC_Handle_8(hcrc, (uint8_t*)pBuffer, BufferLength);
      break;
      
    case CRC_INPUTDATA_FORMAT_HALFWORDS: 
      temp = CRC_Handle_16(hcrc, (uint16_t*)pBuffer, BufferLength);
      break;
    default:
      break;  
  }
  
  /* Change CRC peripheral state */    
  hcrc->State = HAL_CRC_STATE_READY; 
  
  /* Process unlocked */
  __HAL_UNLOCK(hcrc);
  
  /* Return the CRC computed value */ 
  return temp;
}


/**                  
  * @brief  Compute the 7, 8, 16 or 32-bit CRC value of an 8, 16 or 32-bit data buffer
  *         starting with hcrc->Instance->INIT as initialization value.
  * @param  hcrc: CRC handle
  * @param  pBuffer: pointer to the input data buffer, exact input data format is
  *         provided by hcrc->InputDataFormat.  
  * @param  BufferLength: input data buffer length
  * @retval uint32_t CRC (returned value LSBs for CRC shorter than 32 bits)
  */  
uint32_t HAL_CRC_Calculate(CRC_HandleTypeDef *hcrc, uint32_t pBuffer[], uint32_t BufferLength)
{
  uint32_t index = 0; /* CRC input data buffer index */
  uint32_t temp = 0;  /* CRC output (read from hcrc->Instance->DR register) */
    
  /* Process locked */
  __HAL_LOCK(hcrc); 
  
  /* Change CRC peripheral state */  
  hcrc->State = HAL_CRC_STATE_BUSY;
  
  /* Reset CRC Calculation Unit (hcrc->Instance->INIT is 
  *  written in hcrc->Instance->DR) */
  __HAL_CRC_DR_RESET(hcrc);
  
  switch (hcrc->InputDataFormat)
  {
    case CRC_INPUTDATA_FORMAT_WORDS:  
      /* Enter 32-bit input data to the CRC calculator */
      for(index = 0; index < BufferLength; index++)
      {
        hcrc->Instance->DR = pBuffer[index];
      }
      temp = hcrc->Instance->DR;
      break;
      
    case CRC_INPUTDATA_FORMAT_BYTES: 
      /* Specific 8-bit input data handling  */
      temp = CRC_Handle_8(hcrc, (uint8_t*)pBuffer, BufferLength);
      break;
      
    case CRC_INPUTDATA_FORMAT_HALFWORDS: 
      /* Specific 16-bit input data handling  */
      temp = CRC_Handle_16(hcrc, (uint16_t*)pBuffer, BufferLength);
      break;
    default:
      break;
  }

  /* Change CRC peripheral state */
  hcrc->State = HAL_CRC_STATE_READY;

  /* Process unlocked */
  __HAL_UNLOCK(hcrc);
  
  /* Return the CRC computed value */ 
  return temp;
}



/**             
  * @brief  Enter 8-bit input data to the CRC calculator.
  *         Specific data handling to optimize processing time.  
  * @param  hcrc: CRC handle
  * @param  pBuffer: pointer to the input data buffer
  * @param  BufferLength: input data buffer length
  * @retval uint32_t CRC (returned value LSBs for CRC shorter than 32 bits)
  */
static uint32_t CRC_Handle_8(CRC_HandleTypeDef *hcrc, uint8_t pBuffer[], uint32_t BufferLength)
{
  uint32_t i = 0; /* input data buffer index */
  
   /* Processing time optimization: 4 bytes are entered in a row with a single word write,
    * last bytes must be carefully fed to the CRC calculator to ensure a correct type
    * handling by the IP */
   for(i = 0; i < (BufferLength/4); i++)
   {
     hcrc->Instance->DR = (uint32_t)(((uint32_t)(pBuffer[4*i])<<24) | ((uint32_t)(pBuffer[4*i+1])<<16) | ((uint32_t)(pBuffer[4*i+2])<<8) | (uint32_t)(pBuffer[4*i+3]));
   }
   /* last bytes specific handling */
   if ((BufferLength%4) != 0)
   {
     if  (BufferLength%4 == 1)
     {
       *(__IO uint8_t*) (&hcrc->Instance->DR) = pBuffer[4*i];
     }
     if  (BufferLength%4 == 2)
     {
       *(__IO uint32_t*) (&hcrc->Instance->DR) = (uint16_t)(((uint32_t)(pBuffer[4*i])<<8) | (uint32_t)(pBuffer[4*i+1]));
     }
     if  (BufferLength%4 == 3)
     {
       *(__IO uint32_t*) (&hcrc->Instance->DR) = (uint16_t)(((uint32_t)(pBuffer[4*i])<<8) | (uint32_t)(pBuffer[4*i+1]));
       *(__IO uint32_t*) (&hcrc->Instance->DR) = pBuffer[4*i+2];       
     }
   }
  
  /* Return the CRC computed value */ 
  return hcrc->Instance->DR;
}



/**             
  * @brief  Enter 16-bit input data to the CRC calculator.
  *         Specific data handling to optimize processing time.  
  * @param  hcrc: CRC handle
  * @param  pBuffer: pointer to the input data buffer
  * @param  BufferLength: input data buffer length
  * @retval uint32_t CRC (returned value LSBs for CRC shorter than 32 bits)
  */  
static uint32_t CRC_Handle_16(CRC_HandleTypeDef *hcrc, uint16_t pBuffer[], uint32_t BufferLength)
{
  uint32_t i = 0;  /* input data buffer index */
  
  /* Processing time optimization: 2 HalfWords are entered in a row with a single word write,
   * in case of odd length, last HalfWord must be carefully fed to the CRC calculator to ensure 
   * a correct type handling by the IP */
  for(i = 0; i < (BufferLength/2); i++)
  {
    hcrc->Instance->DR = (((uint32_t)(pBuffer[2*i])<<16) | (uint32_t)(pBuffer[2*i+1]));
  }
  if ((BufferLength%2) != 0)
  {
       *(__IO uint32_t*) (&hcrc->Instance->DR) = pBuffer[2*i]; 
  }
   
  /* Return the CRC computed value */ 
  return hcrc->Instance->DR;
}

/**
  * @}
  */

/** @defgroup HAL_CRC_Group3 Peripheral State functions 
 *  @brief    Peripheral State functions. 
 *
@verbatim   
 ==============================================================================
                      ##### Peripheral State functions #####
 ==============================================================================  
    [..]
    This subsection permits to get in run-time the status of the peripheral 
    and the data flow.

@endverbatim
  * @{
  */

/**
  * @brief  Returns the CRC state.
  * @param  hcrc: CRC handle
  * @retval HAL state
  */
HAL_CRC_StateTypeDef HAL_CRC_GetState(CRC_HandleTypeDef *hcrc)
{
  return hcrc->State;
}

/**
  * @}
  */

/**
  * @}
  */

#endif /* HAL_CRC_MODULE_ENABLED */
/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
