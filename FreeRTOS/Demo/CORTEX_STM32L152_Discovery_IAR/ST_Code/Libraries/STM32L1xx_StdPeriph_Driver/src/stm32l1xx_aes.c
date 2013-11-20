/**
  ******************************************************************************
  * @file    stm32l1xx_aes.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides firmware functions to manage the following 
  *          functionalities of the AES peripheral:           
  *           + Configuration
  *           + Read/Write operations
  *           + DMA transfers management  
  *           + Interrupts and flags management
  * 
  *  @verbatim
 ===============================================================================
                        ##### AES Peripheral features #####
 ===============================================================================
....[..]
   (#) The Advanced Encryption Standard hardware accelerator (AES) can be used
       to both encipher and decipher data using AES algorithm.
   (#) The AES supports 4 operation modes:
       (++) Encryption: It consumes 214 clock cycle when processing one 128-bit block
       (++) Decryption: It consumes 214 clock cycle when processing one 128-bit block
       (++) Key derivation for decryption: It consumes 80 clock cycle when processing one 128-bit block
       (++) Key Derivation and decryption: It consumes 288 clock cycle when processing one 128-bit blobk
   (#) Moreover 3 chaining modes are supported:
       (++) Electronic codebook (ECB): Each plain text is encrypted/decrypted separately
       (++) Cipher block chaining (CBC): Each block is XORed with the previous block
       (++) Counter mode (CTR): A 128-bit counter is encrypted and then XORed with the
          plain text to give the cipher text
  (#) The AES peripheral supports data swapping: 1-bit, 8-bit, 16-bit and 32-bit.
  (#) The AES peripheral supports write/read error handling with interrupt capability.
  (#) Automatic data flow control with support of direct memory access (DMA) using
      2 channels, one for incoming data (DMA2 Channel5), and one for outcoming data
      (DMA2 Channel3).

                      ##### How to use this driver #####
 ===============================================================================
    [..]
        (#) AES AHB clock must be enabled to get write access to AES registers 
            using RCC_AHBPeriphClockCmd(RCC_AHBPeriph_AES, ENABLE).
        (#) Initialize the key using AES_KeyInit().
        (#) Configure the AES operation mode using AES_Init().
        (#) If required, enable interrupt source using AES_ITConfig() and
            enable the AES interrupt vector using NVIC_Init().
        (#) If required, when using the DMA mode.
            (##) Configure the DMA using DMA_Init().
            (##) Enable DMA requests using AES_DMAConfig().
        (#) Enable the AES peripheral using AES_Cmd().
    @endverbatim
  
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
  *
  * Licensed under MCD-ST Liberty SW License Agreement V2, (the "License");
  * You may not use this file except in compliance with the License.
  * You may obtain a copy of the License at:
  *
  *        http://www.st.com/software_license_agreement_liberty_v2
  *
  * Unless required by applicable law or agreed to in writing, software 
  * distributed under the License is distributed on an "AS IS" BASIS, 
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  *
  ******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx_aes.h"
#include "stm32l1xx_rcc.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup AES 
  * @brief AES driver modules
  * @{
  */ 

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define CR_CLEAR_MASK  ((uint32_t)0xFFFFFF81)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup AES_Private_Functions
  * @{
  */

/** @defgroup AES_Group1 Initialization and configuration
 *  @brief   Initialization and configuration.
 *
@verbatim
 ===============================================================================
                ##### Initialization and configuration #####
 ===============================================================================

@endverbatim
  * @{
  */  

  /**
  * @brief  Deinitializes AES peripheral registers to their default reset values.
  * @param  None
  * @retval None
  */
void AES_DeInit(void)
{
  /* Enable AES reset state */
  RCC_AHBPeriphResetCmd(RCC_AHBPeriph_AES, ENABLE);
  /* Release AES from reset state */
  RCC_AHBPeriphResetCmd(RCC_AHBPeriph_AES, DISABLE);
}

/**
  * @brief  Initializes the AES peripheral according to the specified parameters
  *         in the AES_InitStruct:
  *           - AES_Operation: specifies the operation mode (encryption, decryption...).
  *           - AES_Chaining: specifies the chaining mode (ECB, CBC or CTR).
  *           - AES_DataType: specifies the data swapping type: 32-bit, 16-bit, 8-bit or 1-bit.
  * @note   If AES is already enabled, use AES_Cmd(DISABLE) before setting the new 
  *         configuration (When AES is enabled, setting configuration is forbidden).
  * @param  AES_InitStruct: pointer to an AES_InitTypeDef structure that contains 
  *         the configuration information for AES peripheral.
  * @retval None
  */
void AES_Init(AES_InitTypeDef* AES_InitStruct)
{
  uint32_t tmpreg = 0;
  
  /* Check the parameters */
  assert_param(IS_AES_MODE(AES_InitStruct->AES_Operation));
  assert_param(IS_AES_CHAINING(AES_InitStruct->AES_Chaining));
  assert_param(IS_AES_DATATYPE(AES_InitStruct->AES_DataType));

  /* Get AES CR register value */
  tmpreg = AES->CR;
  
  /* Clear DATATYPE[1:0], MODE[1:0] and CHMOD[1:0] bits */
  tmpreg &= (uint32_t)CR_CLEAR_MASK;
  
  tmpreg |= (AES_InitStruct->AES_Operation | AES_InitStruct->AES_Chaining | AES_InitStruct->AES_DataType);

  AES->CR = (uint32_t) tmpreg;
}

/**
  * @brief  Initializes the AES Keys according to the specified parameters in the AES_KeyInitStruct.
  * @param  AES_KeyInitStruct: pointer to an AES_KeyInitTypeDef structure that
  *         contains the configuration information for the specified AES Keys.
  * @note   This function must be called while the AES is disabled.
  * @note   In encryption, key derivation and key derivation + decryption modes,
  *         AES_KeyInitStruct must contain the encryption key.
  *         In decryption mode, AES_KeyInitStruct must contain the decryption key.
  * @retval None
  */
void AES_KeyInit(AES_KeyInitTypeDef* AES_KeyInitStruct)
{
  AES->KEYR0 = AES_KeyInitStruct->AES_Key0;
  AES->KEYR1 = AES_KeyInitStruct->AES_Key1;
  AES->KEYR2 = AES_KeyInitStruct->AES_Key2;
  AES->KEYR3 = AES_KeyInitStruct->AES_Key3;
}

/**
  * @brief  Initializes the AES Initialization Vector IV according to 
  *         the specified parameters in the AES_IVInitStruct.
  * @param  AES_KeyInitStruct: pointer to an AES_IVInitTypeDef structure that
  *         contains the configuration information for the specified AES IV.
  * @note   When ECB chaining mode is selected, Initialization Vector IV has no
  *         meaning.
  *         When CTR chaining mode is selected, AES_IV0 contains the CTR value.
  *         AES_IV1, AES_IV2 and AES_IV3 contains nonce value.
  * @retval None
  */
void AES_IVInit(AES_IVInitTypeDef* AES_IVInitStruct)
{
  AES->IVR0 = AES_IVInitStruct->AES_IV0;
  AES->IVR1 = AES_IVInitStruct->AES_IV1;
  AES->IVR2 = AES_IVInitStruct->AES_IV2;
  AES->IVR3 = AES_IVInitStruct->AES_IV3;
}

/**
  * @brief  Enable or disable the AES peripheral.
  * @param  NewState: new state of the AES peripheral.
  *         This parameter can be: ENABLE or DISABLE.
  * @note   The key must be written while AES is disabled.
  * @retval None
  */
void AES_Cmd(FunctionalState NewState)
{
  /* Check the parameter */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the AES peripheral */
    AES->CR |= (uint32_t) AES_CR_EN;   /**< AES Enable */
  }
  else
  {
    /* Disable the AES peripheral */
    AES->CR &= (uint32_t)(~AES_CR_EN);  /**< AES Disable */
  }
}

/**
  * @}
  */

/** @defgroup AES_Group2 Structures initialization functions
 *  @brief   Structures initialization.
 *
@verbatim
 ===============================================================================
              ##### Structures initialization functions #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Fills each AES_InitStruct member with its default value.
  * @param  AES_InitStruct: pointer to an AES_InitTypeDef structure which will 
  *         be initialized.
  * @retval None
  */
void AES_StructInit(AES_InitTypeDef* AES_InitStruct)
{
  AES_InitStruct->AES_Operation = AES_Operation_Encryp;
  AES_InitStruct->AES_Chaining = AES_Chaining_ECB;
  AES_InitStruct->AES_DataType = AES_DataType_32b;
}

/**
  * @brief  Fills each AES_KeyInitStruct member with its default value.
  * @param  AES_KeyInitStruct: pointer to an AES_KeyInitStruct structure which 
  *         will be initialized.
  * @retval None
  */
void AES_KeyStructInit(AES_KeyInitTypeDef* AES_KeyInitStruct)
{
  AES_KeyInitStruct->AES_Key0 = 0x00000000;
  AES_KeyInitStruct->AES_Key1 = 0x00000000;
  AES_KeyInitStruct->AES_Key2 = 0x00000000;
  AES_KeyInitStruct->AES_Key3 = 0x00000000;
}

/**
  * @brief  Fills each AES_IVInitStruct member with its default value.
  * @param  AES_IVInitStruct: pointer to an AES_IVInitTypeDef structure which
  *         will be initialized.
  * @retval None
  */
void AES_IVStructInit(AES_IVInitTypeDef* AES_IVInitStruct)
{
  AES_IVInitStruct->AES_IV0 = 0x00000000;
  AES_IVInitStruct->AES_IV1 = 0x00000000;
  AES_IVInitStruct->AES_IV2 = 0x00000000;
  AES_IVInitStruct->AES_IV3 = 0x00000000;
}

/**
  * @}
  */

/** @defgroup AES_Group3 AES Read and Write
 *  @brief   AES Read and Write.
 *
@verbatim
 ===============================================================================
                  ##### AES Read and Write functions #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Write data in DINR register to be processed by AES peripheral.
  * @note   To process 128-bit data (4 * 32-bit), this function must be called
  *         four times to write the 128-bit data in the 32-bit register DINR.
  * @note   When an unexpected write to DOUTR register is detected, WRERR flag is
  *         set.
  * @param  Data: The data to be processed.
  * @retval None
  */
void AES_WriteSubData(uint32_t Data)
{
  /* Write Data */
  AES->DINR = Data;
}

/**
  * @brief  Returns the data in DOUTR register processed by AES peripheral.
  * @note   This function must be called four times to get the 128-bit data.
  * @note   When an unexpected read of DINR register is detected, RDERR flag is
  *         set.
  * @retval The processed data.
  */
uint32_t AES_ReadSubData(void)
{
  /* Read Data */
  return AES->DOUTR;
}

/**
  * @brief  Read the Key value.
  * @param  AES_KeyInitStruct: pointer to an AES_KeyInitTypeDef structure which
  *         will contain the key.
  * @note   When the key derivation mode is selected, AES must be disabled
  *         (AES_Cmd(DISABLE)) before reading the decryption key.
  *         Reading the key while the AES is enabled will return unpredictable
  *         value.
  * @retval None
  */
void AES_ReadKey(AES_KeyInitTypeDef* AES_KeyInitStruct)
{
  AES_KeyInitStruct->AES_Key0 = AES->KEYR0;
  AES_KeyInitStruct->AES_Key1 = AES->KEYR1;
  AES_KeyInitStruct->AES_Key2 = AES->KEYR2;
  AES_KeyInitStruct->AES_Key3 = AES->KEYR3;
}

/**
  * @brief  Read the Initialization Vector IV value.
  * @param  AES_IVInitStruct: pointer to an AES_IVInitTypeDef structure which
  *         will contain the Initialization Vector IV.
  * @note   When the AES is enabled Reading the Initialization Vector IV value
  *         will return 0. The AES must be disabled using AES_Cmd(DISABLE)
  *         to get the right value.
  * @note   When ECB chaining mode is selected, Initialization Vector IV has no
  *         meaning.
  *         When CTR chaining mode is selected, AES_IV0 contains 32-bit Counter value.
  *         AES_IV1, AES_IV2 and AES_IV3 contains nonce value.
  * @retval None
  */
void AES_ReadIV(AES_IVInitTypeDef* AES_IVInitStruct)
{
  AES_IVInitStruct->AES_IV0 = AES->IVR0;
  AES_IVInitStruct->AES_IV1 = AES->IVR1;
  AES_IVInitStruct->AES_IV2 = AES->IVR2;
  AES_IVInitStruct->AES_IV3 = AES->IVR3;
}

/**
  * @}
  */

/** @defgroup AES_Group4 DMA transfers management functions
 *  @brief   DMA transfers management function.
 *
@verbatim
 ===============================================================================
               ##### DMA transfers management functions #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Configures the AES DMA interface.
  * @param  AES_DMATransfer: Specifies the AES DMA transfer.
  *   This parameter can be one of the following values:
  *     @arg AES_DMATransfer_In: When selected, DMA manages the data input phase.
  *     @arg AES_DMATransfer_Out: When selected, DMA manages the data output phase.
  *     @arg AES_DMATransfer_InOut: When selected, DMA manages both the data input/output phases.
  * @param  NewState Indicates the new state of the AES DMA interface.
  *           This parameter can be: ENABLE or DISABLE.
  * @note   The DMA has no action in key derivation mode.
  * @retval None
  */
void AES_DMAConfig(uint32_t AES_DMATransfer, FunctionalState NewState)
{
  /* Check the parameter */
  assert_param(IS_AES_DMA_TRANSFER(AES_DMATransfer));

  if (NewState != DISABLE)
  {
    /* Enable the DMA transfer */
    AES->CR |= (uint32_t) AES_DMATransfer;
  }
  else
  {
    /* Disable the DMA transfer */
    AES->CR &= (uint32_t)(~AES_DMATransfer);
  }
}

/**
  * @}
  */

/** @defgroup AES_Group5 Interrupts and flags management functions
 *  @brief   Interrupts and flags management functions.
 *
@verbatim

 ===============================================================================
           ##### Interrupts and flags management functions #####
 ===============================================================================
@endverbatim
  * @{
  */

/**
  * @brief  Enables or disables the specified AES interrupt.
  * @param  AES_IT: Specifies the AES interrupt source to enable/disable.
  *     This parameter can be any combinations of the following values:
  *     @arg AES_IT_CC: Computation Complete Interrupt. If enabled, once CCF 
  *                     flag is set an interrupt is generated.
  *     @arg AES_IT_ERR: Error Interrupt. If enabled, once a read error
  *                      flags (RDERR) or write error flag (WRERR) is set,
  *                      an interrupt is generated.
  * @param  NewState: The new state of the AES interrupt source.
  *                   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void AES_ITConfig(uint32_t AES_IT, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  assert_param(IS_AES_IT(AES_IT));

  if (NewState != DISABLE)
  {
    AES->CR |= (uint32_t) AES_IT;    /**< AES_IT Enable */
  }
  else
  {
    AES->CR &= (uint32_t)(~AES_IT);  /**< AES_IT Disable */
  }
}

/**
  * @brief  Checks whether the specified AES flag is set or not.
  * @param  AES_FLAG specifies the flag to check.
  *   This parameter can be one of the following values:
  *     @arg AES_FLAG_CCF: Computation Complete Flag is set by hardware when
  *                        he computation phase is completed.
  *     @arg AES_FLAG_RDERR: Read Error Flag is set when an unexpected read
  *                          operation of DOUTR register is detected.
  *     @arg AES_FLAG_WRERR: Write Error Flag  is set when an unexpected write
  *                          operation in DINR is detected.
  * @retval FlagStatus (SET or RESET)
  */
FlagStatus AES_GetFlagStatus(uint32_t AES_FLAG)
{
  FlagStatus bitstatus = RESET;

  /* Check parameters */
  assert_param(IS_AES_FLAG(AES_FLAG));

  if ((AES->SR & AES_FLAG) != (uint32_t)RESET)
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
    
  /* Return the AES_FLAG status */
  return  bitstatus;
}

/**
  * @brief  Clears the AES flags.
  * @param  AES_FLAG: specifies the flag to clear.
  *         This parameter can be:
  *     @arg AES_FLAG_CCF: Computation Complete Flag is cleared by setting CCFC
  *                        bit in CR register.
  *     @arg AES_FLAG_RDERR: Read Error is cleared by setting ERRC bit in 
  *                          CR register.
  *     @arg AES_FLAG_WRERR: Write Error is cleared by setting ERRC bit in
  *                          CR register.
  * @retval None
  */
void AES_ClearFlag(uint32_t AES_FLAG)
{
  /* Check the parameters */
  assert_param(IS_AES_FLAG(AES_FLAG));

  /* Check if AES_FLAG is AES_FLAG_CCF */
  if (AES_FLAG == AES_FLAG_CCF)
  {
    /* Clear CCF flag by setting CCFC bit */
    AES->CR |= (uint32_t) AES_CR_CCFC;
  }
  else /* AES_FLAG is AES_FLAG_RDERR or AES_FLAG_WRERR */
  {
    /* Clear RDERR and WRERR flags by setting ERRC bit */
    AES->CR |= (uint32_t) AES_CR_ERRC;
  }
}

/**
  * @brief  Checks whether the specified AES interrupt has occurred or not.
  * @param  AES_IT: Specifies the AES interrupt pending bit to check.
  *         This parameter can be:
  *     @arg AES_IT_CC: Computation Complete Interrupt.
  *     @arg AES_IT_ERR: Error Interrupt.
  * @retval ITStatus The new state of AES_IT (SET or RESET).
  */
ITStatus AES_GetITStatus(uint32_t AES_IT)
{
  ITStatus itstatus = RESET;
  uint32_t cciebitstatus = RESET, ccfbitstatus = RESET;

  /* Check parameters */
  assert_param(IS_AES_GET_IT(AES_IT));

  cciebitstatus = AES->CR & AES_CR_CCIE;
  ccfbitstatus =  AES->SR & AES_SR_CCF;

  /* Check if AES_IT is AES_IT_CC */
  if (AES_IT == AES_IT_CC)
  {
    /* Check the status of the specified AES interrupt */
    if (((cciebitstatus) != (uint32_t)RESET) && ((ccfbitstatus) != (uint32_t)RESET))
    {
      /* Interrupt occurred */
      itstatus = SET;
    }
    else
    {
      /* Interrupt didn't occur */
      itstatus = RESET;
    }
  }
  else /* AES_IT is AES_IT_ERR */
  {
    /* Check the status of the specified AES interrupt */
    if ((AES->CR & AES_CR_ERRIE) != RESET)
    {
      /* Check if WRERR or RDERR flags are set */
      if ((AES->SR & (uint32_t)(AES_SR_WRERR | AES_SR_RDERR)) != (uint16_t)RESET)
      {
        /* Interrupt occurred */
        itstatus = SET;
      }
      else
      {
        /* Interrupt didn't occur */
        itstatus = RESET;
      }
    }
    else
    {
      /* Interrupt didn't occur */
      itstatus = (ITStatus) RESET;
    }
  }

  /* Return the AES_IT status */
  return itstatus;
}

/**
  * @brief  Clears the AES's interrupt pending bits.
  * @param  AES_IT: specifies the interrupt pending bit to clear.
  *   This parameter can be any combinations of the following values:
  *     @arg AES_IT_CC: Computation Complete Interrupt.
  *     @arg AES_IT_ERR: Error Interrupt.
  * @retval None
  */
void AES_ClearITPendingBit(uint32_t AES_IT)
{
  /* Check the parameters */
  assert_param(IS_AES_IT(AES_IT));

  /* Clear the interrupt pending bit */
  AES->CR |= (uint32_t) (AES_IT >> (uint32_t) 0x00000002);
}

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
