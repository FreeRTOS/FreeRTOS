/**
  ******************************************************************************
  * @file    stm32l1xx_flash.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides all the Flash firmware functions. These functions 
  *          can be executed from Internal FLASH or Internal SRAM memories. 
  *          The functions that should be called from SRAM are defined inside 
  *          the "stm32l1xx_flash_ramfunc.c" file.
  *          This file provides firmware functions to manage the following 
  *          functionalities of the FLASH peripheral:
  *            + FLASH Interface configuration
  *            + FLASH Memory Programming
  *            + DATA EEPROM Programming
  *            + Option Bytes Programming
  *            + Interrupts and flags management
  *
  *  @verbatim

  ==============================================================================
                        ##### How to use this driver #####
  ==============================================================================
    [..] This driver provides functions to configure and program the Flash 
         memory of all STM32L1xx devices.
    [..] These functions are split in 5 groups:
         (#) FLASH Interface configuration functions: this group includes 
             the management of following features:
             (++) Set the latency.
             (++) Enable/Disable the prefetch buffer.
             (++) Enable/Disable the 64 bit Read Access. 
             (++) Enable/Disable the RUN PowerDown mode.
             (++) Enable/Disable the SLEEP PowerDown mode.  
    
         (#) FLASH Memory Programming functions: this group includes all 
             needed functions to erase and program the main memory:
             (++) Lock and Unlock the Flash interface.
             (++) Erase function: Erase Page.
             (++) Program functions: Fast Word and Half Page(should be 
                  executed from internal SRAM).
      
         (#) DATA EEPROM Programming functions: this group includes all 
             needed functions to erase and program the DATA EEPROM memory:
             (++) Lock and Unlock the DATA EEPROM interface.
             (++) Erase function: Erase Byte, erase HalfWord, erase Word, erase 
             (++) Double Word (should be executed from internal SRAM).
             (++) Program functions: Fast Program Byte, Fast Program Half-Word, 
                  FastProgramWord, Program Byte, Program Half-Word, 
                  Program Word and Program Double-Word (should be executed 
                  from internal SRAM).
      
         (#) FLASH Option Bytes Programming functions: this group includes 
             all needed functions to:
             (++) Lock and Unlock the Flash Option bytes.
             (++) Set/Reset the write protection.
             (++) Set the Read protection Level.
             (++) Set the BOR level.
             (++) rogram the user option Bytes.
             (++) Launch the Option Bytes loader.
             (++) Get the Write protection.
             (++) Get the read protection status.
             (++) Get the BOR level.
             (++) Get the user option bytes.
    
         (#) FLASH Interrupts and flag management functions: this group 
             includes all needed functions to:
             (++) Enable/Disable the flash interrupt sources.
             (++) Get flags status.
             (++) Clear flags.
             (++) Get Flash operation status.
             (++) Wait for last flash operation.

  *  @endverbatim
  *                      
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
#include "stm32l1xx_flash.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup FLASH 
  * @brief FLASH driver modules
  * @{
  */ 

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
  
/* FLASH Mask */
#define WRP01_MASK                 ((uint32_t)0x0000FFFF)
#define WRP23_MASK                 ((uint32_t)0xFFFF0000)
#define WRP45_MASK                 ((uint32_t)0x0000FFFF)
#define WRP67_MASK                 ((uint32_t)0xFFFF0000)
#define WRP89_MASK                 ((uint32_t)0x0000FFFF)
#define WRP1011_MASK               ((uint32_t)0xFFFF0000)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
 
/** @defgroup FLASH_Private_Functions
  * @{
  */ 

/** @defgroup FLASH_Group1 FLASH Interface configuration functions
  *  @brief   FLASH Interface configuration functions 
 *
@verbatim   
  ============================================================================== 
             ##### FLASH Interface configuration functions #####
  ==============================================================================

    [..] FLASH_Interface configuration_Functions, includes the following functions:
     (+) void FLASH_SetLatency(uint32_t FLASH_Latency):
    [..] To correctly read data from Flash memory, the number of wait states (LATENCY) 
         must be correctly programmed according to the frequency of the CPU clock 
        (HCLK) and the supply voltage of the device.
  [..] 
  ----------------------------------------------------------------
 |  Wait states  |                HCLK clock frequency (MHz)      |
 |               |------------------------------------------------|
 |   (Latency)   |            voltage range       | voltage range |
 |               |            1.65 V - 3.6 V      | 2.0 V - 3.6 V |
 |               |----------------|---------------|---------------|
 |               |  VCORE = 1.2 V | VCORE = 1.5 V | VCORE = 1.8 V |
 |-------------- |----------------|---------------|---------------|
 |0WS(1CPU cycle)|0 < HCLK <= 2   |0 < HCLK <= 8  |0 < HCLK <= 16 |
 |---------------|----------------|---------------|---------------|
 |1WS(2CPU cycle)|2 < HCLK <= 4   |8 < HCLK <= 16 |16 < HCLK <= 32|
  ----------------------------------------------------------------
  [..]
     (+) void FLASH_PrefetchBufferCmd(FunctionalState NewState);
     (+) void FLASH_ReadAccess64Cmd(FunctionalState NewState);
     (+) void FLASH_RUNPowerDownCmd(FunctionalState NewState);
     (+) void FLASH_SLEEPPowerDownCmd(FunctionalState NewState);
     (+) void FLASH_ITConfig(uint32_t FLASH_IT, FunctionalState NewState);
  [..]     
  Here below the allowed configuration of Latency, 64Bit access and prefetch buffer
  [..]  
  --------------------------------------------------------------------------------
 |               |              ACC64 = 0         |              ACC64 = 1        |
 |   Latency     |----------------|---------------|---------------|---------------|
 |               |   PRFTEN = 0   |   PRFTEN = 1  |   PRFTEN = 0  |   PRFTEN = 1  |
 |---------------|----------------|---------------|---------------|---------------|
 |0WS(1CPU cycle)|     YES        |     NO        |     YES       |     YES       |
 |---------------|----------------|---------------|---------------|---------------|
 |1WS(2CPU cycle)|     NO         |     NO        |     YES       |     YES       |
  --------------------------------------------------------------------------------
  [..]
   All these functions don't need the unlock sequence.

@endverbatim
  * @{
  */

/**
  * @brief  Sets the code latency value.
  * @param  FLASH_Latency: specifies the FLASH Latency value.
  *   This parameter can be one of the following values:
  *     @arg FLASH_Latency_0: FLASH Zero Latency cycle.
  *     @arg FLASH_Latency_1: FLASH One Latency cycle.
  * @retval None
  */
void FLASH_SetLatency(uint32_t FLASH_Latency)
{
   uint32_t tmpreg = 0;
  
  /* Check the parameters */
  assert_param(IS_FLASH_LATENCY(FLASH_Latency));
  
  /* Read the ACR register */
  tmpreg = FLASH->ACR;  
  
  /* Sets the Latency value */
  tmpreg &= (uint32_t) (~((uint32_t)FLASH_ACR_LATENCY));
  tmpreg |= FLASH_Latency;
  
  /* Write the ACR register */
  FLASH->ACR = tmpreg;
}

/**
  * @brief  Enables or disables the Prefetch Buffer.
  * @param  NewState: new state of the FLASH prefetch buffer.
  *              This parameter can be: ENABLE or DISABLE. 
  * @retval None
  */
void FLASH_PrefetchBufferCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
   
  if(NewState != DISABLE)
  {
    FLASH->ACR |= FLASH_ACR_PRFTEN;
  }
  else
  {
    FLASH->ACR &= (uint32_t)(~((uint32_t)FLASH_ACR_PRFTEN));
  }
}

/**
  * @brief  Enables or disables read access to flash by 64 bits.
  * @param  NewState: new state of the FLASH read access mode.
  *              This parameter can be: ENABLE or DISABLE.
  * @note    If this bit is set, the Read access 64 bit is used.
  *          If this bit is reset, the Read access 32 bit is used.
  * @note    This bit cannot be written at the same time as the LATENCY and 
  *          PRFTEN bits.
  *          To reset this bit, the LATENCY should be zero wait state and the 
  *          prefetch off.
  * @retval None
  */
void FLASH_ReadAccess64Cmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if(NewState != DISABLE)
  {
    FLASH->ACR |= FLASH_ACR_ACC64;
  }
  else
  {
    FLASH->ACR &= (uint32_t)(~((uint32_t)FLASH_ACR_ACC64));
  }
}

/**
  * @brief  Enable or disable the power down mode during Sleep mode.
  * @note   This function is used to power down the FLASH when the system is in SLEEP LP mode.
  * @param  NewState: new state of the power down mode during sleep mode.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void FLASH_SLEEPPowerDownCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Set the SLEEP_PD bit to put Flash in power down mode during sleep mode */
    FLASH->ACR |= FLASH_ACR_SLEEP_PD;
  }
  else
  {
    /* Clear the SLEEP_PD bit in to put Flash in idle mode during sleep mode */
    FLASH->ACR &= (uint32_t)(~((uint32_t)FLASH_ACR_SLEEP_PD));
  }
}

/**
  * @}
  */

/** @defgroup FLASH_Group2 FLASH Memory Programming functions
 *  @brief   FLASH Memory Programming functions
 *
@verbatim   
  ==============================================================================
                ##### FLASH Memory Programming functions ##### 
  ==============================================================================

    [..] The FLASH Memory Programming functions, includes the following functions:
    (+) void FLASH_Unlock(void);
    (+) void FLASH_Lock(void);
    (+) FLASH_Status FLASH_ErasePage(uint32_t Page_Address);
    (+) FLASH_Status FLASH_FastProgramWord(uint32_t Address, uint32_t Data);
   
    [..] Any operation of erase or program should follow these steps:
    (#) Call the FLASH_Unlock() function to enable the flash control register and 
        program memory access.
    (#) Call the desired function to erase page or program data.
    (#) Call the FLASH_Lock() to disable the flash program memory access 
       (recommended to protect the FLASH memory against possible unwanted operation).

@endverbatim
  * @{
  */

/**
  * @brief  Unlocks the FLASH control register and program memory access.
  * @param  None
  * @retval None
  */
void FLASH_Unlock(void)
{
  if((FLASH->PECR & FLASH_PECR_PRGLOCK) != RESET)
  {
    /* Unlocking the data memory and FLASH_PECR register access */
    DATA_EEPROM_Unlock();
  
    /* Unlocking the program memory access */
    FLASH->PRGKEYR = FLASH_PRGKEY1;
    FLASH->PRGKEYR = FLASH_PRGKEY2;  
  }
}

/**
  * @brief  Locks the Program memory access.
  * @param  None
  * @retval None
  */
void FLASH_Lock(void)
{
  /* Set the PRGLOCK Bit to lock the program memory access */
  FLASH->PECR |= FLASH_PECR_PRGLOCK;
}

/**
  * @brief  Erases a specified page in program memory.
  * @note   To correctly run this function, the FLASH_Unlock() function
  *         must be called before.
  *         Call the FLASH_Lock() to disable the flash memory access 
  *         (recommended to protect the FLASH memory against possible unwanted operation)
  * @param  Page_Address: The page address in program memory to be erased.
  * @note   A Page is erased in the Program memory only if the address to load 
  *         is the start address of a page (multiple of 256 bytes).
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_ErasePage(uint32_t Page_Address)
{
  FLASH_Status status = FLASH_COMPLETE;

  /* Check the parameters */
  assert_param(IS_FLASH_PROGRAM_ADDRESS(Page_Address));
 
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* If the previous operation is completed, proceed to erase the page */

    /* Set the ERASE bit */
    FLASH->PECR |= FLASH_PECR_ERASE;

    /* Set PROG bit */
    FLASH->PECR |= FLASH_PECR_PROG;
  
    /* Write 00000000h to the first word of the program page to erase */
    *(__IO uint32_t *)Page_Address = 0x00000000;
 
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);

    /* If the erase operation is completed, disable the ERASE and PROG bits */
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_PROG);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_ERASE);   
  }     
  /* Return the Erase Status */
  return status;
}

/**
  * @brief  Programs a word at a specified address in program memory.
  * @note   To correctly run this function, the FLASH_Unlock() function
  *         must be called before.
  *         Call the FLASH_Lock() to disable the flash memory access
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @retval FLASH Status: The returned value can be:  
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT. 
  */
FLASH_Status FLASH_FastProgramWord(uint32_t Address, uint32_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;

  /* Check the parameters */
  assert_param(IS_FLASH_PROGRAM_ADDRESS(Address));
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* If the previous operation is completed, proceed to program the new  word */  
    *(__IO uint32_t *)Address = Data;
    
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);       
  }
  /* Return the Write Status */
  return status;
}

/**
  * @}
  */
  
/** @defgroup FLASH_Group3 DATA EEPROM Programming functions
 *  @brief   DATA EEPROM Programming functions
 *
@verbatim   
 ===============================================================================
                     ##### DATA EEPROM Programming functions ##### 
 ===============================================================================  
 
    [..] The DATA_EEPROM Programming_Functions, includes the following functions:
        (+) void DATA_EEPROM_Unlock(void);
        (+) void DATA_EEPROM_Lock(void);
        (+) FLASH_Status DATA_EEPROM_EraseByte(uint32_t Address);
        (+) FLASH_Status DATA_EEPROM_EraseHalfWord(uint32_t Address);
        (+) FLASH_Status DATA_EEPROM_EraseWord(uint32_t Address);
        (+) FLASH_Status DATA_EEPROM_FastProgramByte(uint32_t Address, uint8_t Data);
        (+) FLASH_Status DATA_EEPROM_FastProgramHalfWord(uint32_t Address, uint16_t Data);
        (+) FLASH_Status DATA_EEPROM_FastProgramWord(uint32_t Address, uint32_t Data);
        (+) FLASH_Status DATA_EEPROM_ProgramByte(uint32_t Address, uint8_t Data);
        (+) FLASH_Status DATA_EEPROM_ProgramHalfWord(uint32_t Address, uint16_t Data);
        (+) FLASH_Status DATA_EEPROM_ProgramWord(uint32_t Address, uint32_t Data);
   
    [..] Any operation of erase or program should follow these steps:
    (#) Call the DATA_EEPROM_Unlock() function to enable the data EEPROM access
        and Flash program erase control register access.
    (#) Call the desired function to erase or program data.
    (#) Call the DATA_EEPROM_Lock() to disable the data EEPROM access
        and Flash program erase control register access(recommended
        to protect the DATA_EEPROM against possible unwanted operation).

@endverbatim
  * @{
  */

/**
  * @brief  Unlocks the data memory and FLASH_PECR register access.
  * @param  None
  * @retval None
  */
void DATA_EEPROM_Unlock(void)
{
  if((FLASH->PECR & FLASH_PECR_PELOCK) != RESET)
  {  
    /* Unlocking the Data memory and FLASH_PECR register access*/
    FLASH->PEKEYR = FLASH_PEKEY1;
    FLASH->PEKEYR = FLASH_PEKEY2;
  }
}

/**
  * @brief  Locks the Data memory and FLASH_PECR register access.
  * @param  None
  * @retval None
  */
void DATA_EEPROM_Lock(void)
{
  /* Set the PELOCK Bit to lock the data memory and FLASH_PECR register access */
  FLASH->PECR |= FLASH_PECR_PELOCK;
}

/**
  * @brief  Enables or disables DATA EEPROM fixed Time programming (2*Tprog).
  * @param  NewState: new state of the DATA EEPROM fixed Time programming mode.
  *         This parameter can be: ENABLE or DISABLE.  
  * @retval None
  */
void DATA_EEPROM_FixedTimeProgramCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if(NewState != DISABLE)
  {
    FLASH->PECR |= (uint32_t)FLASH_PECR_FTDW;
  }
  else
  {
    FLASH->PECR &= (uint32_t)(~((uint32_t)FLASH_PECR_FTDW));
  }
}

/**
  * @brief  Erase a byte in data memory.
  * @param  Address: specifies the address to be erased.
  * @note   This function can be used only for STM32L1XX_HD and STM32L1XX_MDP 
  *         density devices.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status DATA_EEPROM_EraseByte(uint32_t Address)
{
  FLASH_Status status = FLASH_COMPLETE;
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address));
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* Write "00h" to valid address in the data memory" */
    *(__IO uint8_t *) Address = (uint8_t)0x00;
  }
   
  /* Return the erase status */
  return status;
}

/**
  * @brief  Erase a halfword in data memory.
  * @param  Address: specifies the address to be erased.
  * @note   This function can be used only for STM32L1XX_HD and STM32L1XX_MDP 
  *         density devices.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status DATA_EEPROM_EraseHalfWord(uint32_t Address)
{
  FLASH_Status status = FLASH_COMPLETE;
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address));
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* Write "0000h" to valid address in the data memory" */
    *(__IO uint16_t *) Address = (uint16_t)0x0000;
  }
   
  /* Return the erase status */
  return status;
}

/**
  * @brief  Erase a word in data memory.
  * @param  Address: specifies the address to be erased.
  * @note   For STM32L1XX_MD, A data memory word is erased in the data memory only 
  *         if the address to load is the start address of a word (multiple of a word).
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status DATA_EEPROM_EraseWord(uint32_t Address)
{
  FLASH_Status status = FLASH_COMPLETE;
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address));
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* Write "00000000h" to valid address in the data memory" */
    *(__IO uint32_t *) Address = 0x00000000;
  }
   
  /* Return the erase status */
  return status;
}

/**
  * @brief  Write a Byte at a specified address in data memory.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @note   This function assumes that the is data word is already erased.
  * @retval FLASH Status: The returned value can be:
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status DATA_EEPROM_FastProgramByte(uint32_t Address, uint8_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;
#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
  uint32_t tmp = 0, tmpaddr = 0;
#endif
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address)); 

  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
    
  if(status == FLASH_COMPLETE)
  {
    /* Clear the FTDW bit */
    FLASH->PECR &= (uint32_t)(~((uint32_t)FLASH_PECR_FTDW));

#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
    if(Data != (uint8_t)0x00) 
    {
      /* If the previous operation is completed, proceed to write the new Data */
      *(__IO uint8_t *)Address = Data;
            
      /* Wait for last operation to be completed */
      status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
    }
    else
    {
      tmpaddr = Address & 0xFFFFFFFC;
      tmp = * (__IO uint32_t *) tmpaddr;
      tmpaddr = 0xFF << ((uint32_t) (0x8 * (Address & 0x3)));
      tmp &= ~tmpaddr;
      status = DATA_EEPROM_EraseWord(Address & 0xFFFFFFFC);
      status = DATA_EEPROM_FastProgramWord((Address & 0xFFFFFFFC), tmp);
    }       
#elif defined (STM32L1XX_HD) || defined (STM32L1XX_MDP)
    /* If the previous operation is completed, proceed to write the new Data */
    *(__IO uint8_t *)Address = Data;
            
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
#endif  
  }
  /* Return the Write Status */
  return status;
}

/**
  * @brief  Writes a half word at a specified address in data memory.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @note   This function assumes that the is data word is already erased.
  * @retval FLASH Status: The returned value can be: 
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or  FLASH_TIMEOUT. 
  */
FLASH_Status DATA_EEPROM_FastProgramHalfWord(uint32_t Address, uint16_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;
#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
  uint32_t tmp = 0, tmpaddr = 0;
#endif
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address));

  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
    
  if(status == FLASH_COMPLETE)
  {
    /* Clear the FTDW bit */
    FLASH->PECR &= (uint32_t)(~((uint32_t)FLASH_PECR_FTDW));

#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
    if(Data != (uint16_t)0x0000) 
    {
      /* If the previous operation is completed, proceed to write the new data */
      *(__IO uint16_t *)Address = Data;
  
      /* Wait for last operation to be completed */
      status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
    }
    else
    {
      if((Address & 0x3) != 0x3)
      {
        tmpaddr = Address & 0xFFFFFFFC;
        tmp = * (__IO uint32_t *) tmpaddr;
        tmpaddr = 0xFFFF << ((uint32_t) (0x8 * (Address & 0x3)));
        tmp &= ~tmpaddr;        
        status = DATA_EEPROM_EraseWord(Address & 0xFFFFFFFC);
        status = DATA_EEPROM_FastProgramWord((Address & 0xFFFFFFFC), tmp);
      }
      else
      {
        DATA_EEPROM_FastProgramByte(Address, 0x00);
        DATA_EEPROM_FastProgramByte(Address + 1, 0x00);
      }
    }
#elif defined (STM32L1XX_HD) || defined (STM32L1XX_MDP)
    /* If the previous operation is completed, proceed to write the new data */
    *(__IO uint16_t *)Address = Data;
  
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
#endif
  }
  /* Return the Write Status */
  return status;
}

/**
  * @brief  Programs a word at a specified address in data memory.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to the data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @note   This function assumes that the is data word is already erased.
  * @retval FLASH Status: The returned value can be: 
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT. 
  */
FLASH_Status DATA_EEPROM_FastProgramWord(uint32_t Address, uint32_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;

  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address));
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* Clear the FTDW bit */
    FLASH->PECR &= (uint32_t)(~((uint32_t)FLASH_PECR_FTDW));
  
    /* If the previous operation is completed, proceed to program the new data */    
    *(__IO uint32_t *)Address = Data;
    
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);       
  }
  /* Return the Write Status */
  return status;
}

/**
  * @brief  Write a Byte at a specified address in data memory without erase.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @note   The function  DATA_EEPROM_FixedTimeProgramCmd() can be called before 
  *         this function to configure the Fixed Time Programming.
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT. 
  */
FLASH_Status DATA_EEPROM_ProgramByte(uint32_t Address, uint8_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;
#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
  uint32_t tmp = 0, tmpaddr = 0;
#endif
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address)); 

  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
    if(Data != (uint8_t) 0x00)
    {  
      *(__IO uint8_t *)Address = Data;
    
      /* Wait for last operation to be completed */
      status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);

    }
    else
    {
      tmpaddr = Address & 0xFFFFFFFC;
      tmp = * (__IO uint32_t *) tmpaddr;
      tmpaddr = 0xFF << ((uint32_t) (0x8 * (Address & 0x3)));
      tmp &= ~tmpaddr;        
      status = DATA_EEPROM_EraseWord(Address & 0xFFFFFFFC);
      status = DATA_EEPROM_FastProgramWord((Address & 0xFFFFFFFC), tmp);
    }
#elif defined (STM32L1XX_HD) || defined (STM32L1XX_MDP)
    *(__IO uint8_t *)Address = Data;
    
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
#endif
  }
  /* Return the Write Status */
  return status;
}

/**
  * @brief  Writes a half word at a specified address in data memory without erase.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @note   The function  DATA_EEPROM_FixedTimeProgramCmd() can be called before 
  *         this function to configure the Fixed Time Programming
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @retval FLASH Status: The returned value can be:
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT. 
  */
FLASH_Status DATA_EEPROM_ProgramHalfWord(uint32_t Address, uint16_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;
#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
  uint32_t tmp = 0, tmpaddr = 0;
#endif
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address));

  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
#if !defined (STM32L1XX_HD) && !defined (STM32L1XX_MDP)
    if(Data != (uint16_t)0x0000)
    {
      *(__IO uint16_t *)Address = Data;
   
      /* Wait for last operation to be completed */
      status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
    }
    else
    {
      if((Address & 0x3) != 0x3)
      {
        tmpaddr = Address & 0xFFFFFFFC;
        tmp = * (__IO uint32_t *) tmpaddr;
        tmpaddr = 0xFFFF << ((uint32_t) (0x8 * (Address & 0x3)));
        tmp &= ~tmpaddr;          
        status = DATA_EEPROM_EraseWord(Address & 0xFFFFFFFC);
        status = DATA_EEPROM_FastProgramWord((Address & 0xFFFFFFFC), tmp);
      }
      else
      {
        DATA_EEPROM_FastProgramByte(Address, 0x00);
        DATA_EEPROM_FastProgramByte(Address + 1, 0x00);
      }
    }
#elif defined (STM32L1XX_HD) || defined (STM32L1XX_MDP)
    *(__IO uint16_t *)Address = Data;
   
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
#endif
  }
  /* Return the Write Status */
  return status;
}

/**
  * @brief  Programs a word at a specified address in data memory without erase.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @note   The function  DATA_EEPROM_FixedTimeProgramCmd() can be called before 
  *         this function to configure the Fixed Time Programming.
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @retval FLASH Status: The returned value can be:
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or  FLASH_TIMEOUT. 
  */
FLASH_Status DATA_EEPROM_ProgramWord(uint32_t Address, uint32_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;
  
  /* Check the parameters */
  assert_param(IS_FLASH_DATA_ADDRESS(Address));
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    *(__IO uint32_t *)Address = Data;

    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  }
  /* Return the Write Status */
  return status;
}

/**
  * @}
  */

/** @defgroup FLASH_Group4 Option Bytes Programming functions
 *  @brief   Option Bytes Programming functions 
 *
@verbatim   
  ==============================================================================
                ##### Option Bytes Programming functions ##### 
  ==============================================================================  

    [..] The FLASH_Option Bytes Programming_functions, includes the following functions:
    (+) void FLASH_OB_Unlock(void);
    (+) void FLASH_OB_Lock(void);
    (+) void FLASH_OB_Launch(void);
    (+) FLASH_Status FLASH_OB_WRPConfig(uint32_t OB_WRP, FunctionalState NewState);
    (+) FLASH_Status FLASH_OB_WRP1Config(uint32_t OB_WRP1, FunctionalState NewState);
    (+) FLASH_Status FLASH_OB_WRP2Config(uint32_t OB_WRP2, FunctionalState NewState);   
    (+) FLASH_Status FLASH_OB_RDPConfig(uint8_t OB_RDP);
    (+) FLASH_Status FLASH_OB_UserConfig(uint8_t OB_IWDG, uint8_t OB_STOP, uint8_t OB_STDBY);
    (+) FLASH_Status FLASH_OB_BORConfig(uint8_t OB_BOR);
    (+) uint8_t FLASH_OB_GetUser(void);
    (+) uint32_t FLASH_OB_GetWRP(void);
    (+) uint32_t FLASH_OB_GetWRP1(void);
    (+) uint32_t FLASH_OB_GetWRP2(void);     
    (+) FlagStatus FLASH_OB_GetRDP(void);
    (+) uint8_t FLASH_OB_GetBOR(void);
    (+) FLASH_Status FLASH_OB_BootConfig(uint16_t OB_BOOT);
   
    [..] Any operation of erase or program should follow these steps:
    (#) Call the FLASH_OB_Unlock() function to enable the Flash option control 
        register access.
    (#) Call one or several functions to program the desired option bytes.
        (++) void FLASH_OB_WRPConfig(uint32_t OB_WRP, FunctionalState NewState) => to Enable/Disable 
             the desired sector write protection.
        (++) void FLASH_OB_RDPConfig(uint8_t OB_RDP) => to set the desired read Protection Level.
        (++) void FLASH_OB_UserConfig(uint8_t OB_IWDG, uint8_t OB_STOP, uint8_t OB_STDBY) => to configure 
             the user option Bytes: IWDG, STOP and the Standby.
        (++) void FLASH_OB_BORConfig(uint8_t OB_BOR) => to Set the BOR level.
        (++) FLASH_Status FLASH_ProgramOTP(uint32_t Address, uint32_t Data) => to program the OTP bytes			.
    (#) Once all needed option bytes to be programmed are correctly written, call the
        FLASH_OB_Launch(void) function to launch the Option Bytes programming process.
    (#) Call the FLASH_OB_Lock() to disable the Flash option control register access (recommended
        to protect the option Bytes against possible unwanted operations).

@endverbatim
  * @{
  */

/**
  * @brief  Unlocks the option bytes block access.
  * @param  None
  * @retval None
  */
void FLASH_OB_Unlock(void)
{
  if((FLASH->PECR & FLASH_PECR_OPTLOCK) != RESET)
  {
    /* Unlocking the data memory and FLASH_PECR register access */
    DATA_EEPROM_Unlock();
  
    /* Unlocking the option bytes block access */
    FLASH->OPTKEYR = FLASH_OPTKEY1;
    FLASH->OPTKEYR = FLASH_OPTKEY2;
  }
}

/**
  * @brief  Locks the option bytes block access.
  * @param  None
  * @retval None
  */
void FLASH_OB_Lock(void)
{
  /* Set the OPTLOCK Bit to lock the option bytes block access */
  FLASH->PECR |= FLASH_PECR_OPTLOCK;
}

/**
  * @brief  Launch the option byte loading.
  * @param  None
  * @retval None
  */
void FLASH_OB_Launch(void)
{
  /* Set the OBL_Launch bit to lauch the option byte loading */
  FLASH->PECR |= FLASH_PECR_OBL_LAUNCH;
}

/**
  * @brief  Write protects the desired pages.
  * @note   To correctly run this function, the FLASH_OB_Unlock() function
  *         must be called before.
  *         Call the FLASH_OB_Lock() to disable the flash control register access and the option bytes 
  *        (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  OB_WRP: specifies the address of the pages to be write protected.
  *   This parameter can be:
  * @param  value between OB_WRP_Pages0to15 and OB_WRP_Pages496to511
  * @param  OB_WRP_AllPages
  * @param  NewState: new state of the specified FLASH Pages Wtite protection.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval FLASH Status: The returned value can be: 
  * FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_OB_WRPConfig(uint32_t OB_WRP, FunctionalState NewState)
{
  uint32_t WRP01_Data = 0, WRP23_Data = 0;
  
  FLASH_Status status = FLASH_COMPLETE;
  uint32_t tmp1 = 0, tmp2 = 0;
  
  /* Check the parameters */
  assert_param(IS_OB_WRP(OB_WRP));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
     
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
 
  if(status == FLASH_COMPLETE)
  {
    if (NewState != DISABLE)
    {
      WRP01_Data = (uint16_t)(((OB_WRP & WRP01_MASK) | OB->WRP01));
      WRP23_Data = (uint16_t)((((OB_WRP & WRP23_MASK)>>16 | OB->WRP23))); 
      tmp1 = (uint32_t)(~(WRP01_Data) << 16)|(WRP01_Data);
      OB->WRP01 = tmp1;
      
      tmp2 = (uint32_t)(~(WRP23_Data) << 16)|(WRP23_Data);
      OB->WRP23 = tmp2;      
    }             
    
    else
    {
      WRP01_Data = (uint16_t)(~OB_WRP & (WRP01_MASK & OB->WRP01));
      WRP23_Data = (uint16_t)((((~OB_WRP & WRP23_MASK)>>16 & OB->WRP23))); 

      tmp1 = (uint32_t)((~WRP01_Data) << 16)|(WRP01_Data);
      OB->WRP01 = tmp1;
      
      tmp2 = (uint32_t)((~WRP23_Data) << 16)|(WRP23_Data);
      OB->WRP23 = tmp2;
    }
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  }

  /* Return the write protection operation Status */
  return status;      
}

/**
  * @brief  Write protects the desired pages.
  * @note   This function can be used only for STM32L1XX_HD and STM32L1XX_MDP 
  *         density devices.
  *         To correctly run this function, the FLASH_OB_Unlock() function
  *         must be called before.
  *         Call the FLASH_OB_Lock() to disable the flash control register access and the option bytes 
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  OB_WRP1: specifies the address of the pages to be write protected.
  *   This parameter can be:
  *     @arg  value between OB_WRP_Pages512to527 and OB_WRP_Pages1008to1023
  *     @arg OB_WRP_AllPages
  * @param  NewState: new state of the specified FLASH Pages Wtite protection.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval FLASH Status: The returned value can be: 
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_OB_WRP1Config(uint32_t OB_WRP1, FunctionalState NewState)
{
  uint32_t WRP45_Data = 0, WRP67_Data = 0;
  
  FLASH_Status status = FLASH_COMPLETE;
  uint32_t tmp1 = 0, tmp2 = 0;
  
  /* Check the parameters */
  assert_param(IS_OB_WRP(OB_WRP1));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
     
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
 
  if(status == FLASH_COMPLETE)
  {
    if (NewState != DISABLE)
    {
      WRP45_Data = (uint16_t)(((OB_WRP1 & WRP45_MASK) | OB->WRP45));
      WRP67_Data = (uint16_t)((((OB_WRP1 & WRP67_MASK)>>16 | OB->WRP67))); 
      tmp1 = (uint32_t)(~(WRP45_Data) << 16)|(WRP45_Data);
      OB->WRP45 = tmp1;
      
      tmp2 = (uint32_t)(~(WRP67_Data) << 16)|(WRP67_Data);
      OB->WRP67 = tmp2;      
    }             
    
    else
    {
      WRP45_Data = (uint16_t)(~OB_WRP1 & (WRP45_MASK & OB->WRP45));
      WRP67_Data = (uint16_t)((((~OB_WRP1 & WRP67_MASK)>>16 & OB->WRP67))); 

      tmp1 = (uint32_t)((~WRP45_Data) << 16)|(WRP45_Data);
      OB->WRP45 = tmp1;
      
      tmp2 = (uint32_t)((~WRP67_Data) << 16)|(WRP67_Data);
      OB->WRP67 = tmp2;
    }
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  }

  /* Return the write protection operation Status */
  return status;      
}

/**
  * @brief  Write protects the desired pages.
  * @note   This function can be used only for STM32L1XX_HD density devices.
  *         To correctly run this function, the FLASH_OB_Unlock() function
  *         must be called before.
  *         Call the FLASH_OB_Lock() to disable the flash control register access and the option bytes 
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  OB_WRP2: specifies the address of the pages to be write protected.
  *   This parameter can be:
  *     @arg  value between OB_WRP_Pages1024to1039 and OB_WRP_Pages1520to1535
  *     @arg OB_WRP_AllPages
  * @param  NewState: new state of the specified FLASH Pages Wtite protection.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval FLASH Status: The returned value can be: 
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_OB_WRP2Config(uint32_t OB_WRP2, FunctionalState NewState)
{
  uint32_t WRP89_Data = 0, WRP1011_Data = 0;
  
  FLASH_Status status = FLASH_COMPLETE;
  uint32_t tmp1 = 0, tmp2 = 0;
  
  /* Check the parameters */
  assert_param(IS_OB_WRP(OB_WRP2));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
     
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
 
  if(status == FLASH_COMPLETE)
  {
    if (NewState != DISABLE)
    {
      WRP89_Data = (uint16_t)(((OB_WRP2 & WRP89_MASK) | OB->WRP89));
      WRP1011_Data = (uint16_t)((((OB_WRP2 & WRP1011_MASK)>>16 | OB->WRP1011))); 
      tmp1 = (uint32_t)(~(WRP89_Data) << 16)|(WRP89_Data);
      OB->WRP89 = tmp1;
      
      tmp2 = (uint32_t)(~(WRP1011_Data) << 16)|(WRP1011_Data);
      OB->WRP1011 = tmp2;      
    }             
    
    else
    {
      WRP89_Data = (uint16_t)(~OB_WRP2 & (WRP89_MASK & OB->WRP89));
      WRP1011_Data = (uint16_t)((((~OB_WRP2 & WRP1011_MASK)>>16 & OB->WRP1011))); 

      tmp1 = (uint32_t)((~WRP89_Data) << 16)|(WRP89_Data);
      OB->WRP89 = tmp1;
      
      tmp2 = (uint32_t)((~WRP1011_Data) << 16)|(WRP1011_Data);
      OB->WRP1011 = tmp2;
    }
    /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  }

  /* Return the write protection operation Status */
  return status;      
}

/**
  * @brief  Enables or disables the read out protection.
  * @note   To correctly run this function, the FLASH_OB_Unlock() function
  *         must be called before.
  *         Call the FLASH_OB_Lock() to disable the flash control register access and the option bytes 
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  FLASH_ReadProtection_Level: specifies the read protection level. 
  *   This parameter can be:
  *     @arg OB_RDP_Level_0: No protection
  *     @arg OB_RDP_Level_1: Read protection of the memory
  *     @arg OB_RDP_Level_2: Chip protection
  *     @retval FLASH Status: The returned value can be: 
  * FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_OB_RDPConfig(uint8_t OB_RDP)
{
  FLASH_Status status = FLASH_COMPLETE;
  uint8_t tmp1 = 0;
  uint32_t tmp2 = 0;
  
  /* Check the parameters */
  assert_param(IS_OB_RDP(OB_RDP));
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  /* calculate the option byte to write */
  tmp1 = (uint8_t)(~(OB_RDP ));
  tmp2 = (uint32_t)(((uint32_t)((uint32_t)(tmp1) << 16)) | ((uint32_t)OB_RDP));
  
  if(status == FLASH_COMPLETE)
  {         
   /* program read protection level */
    OB->RDP = tmp2;
  }
  
  /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
     
  /* Return the Read protection operation Status */
  return status;            
}

/**
  * @brief  Programs the FLASH User Option Byte: IWDG_SW / RST_STOP / RST_STDBY.
  * @note   To correctly run this function, the FLASH_OB_Unlock() function
  *         must be called before.
  *         Call the FLASH_OB_Lock() to disable the flash control register access and the option bytes 
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  OB_IWDG: Selects the WDG mode.
  *   This parameter can be one of the following values:
  *     @arg OB_IWDG_SW: Software WDG selected
  *     @arg OB_IWDG_HW: Hardware WDG selected
  * @param  OB_STOP: Reset event when entering STOP mode.
  *   This parameter can be one of the following values:
  *     @arg OB_STOP_NoRST: No reset generated when entering in STOP
  *     @arg OB_STOP_RST: Reset generated when entering in STOP
  * @param  OB_STDBY: Reset event when entering Standby mode.
  *   This parameter can be one of the following values:
  *     @arg OB_STDBY_NoRST: No reset generated when entering in STANDBY
  *     @arg OB_STDBY_RST: Reset generated when entering in STANDBY
  * @retval FLASH Status: The returned value can be: 
  * FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_OB_UserConfig(uint8_t OB_IWDG, uint8_t OB_STOP, uint8_t OB_STDBY)
{
  FLASH_Status status = FLASH_COMPLETE; 
  uint32_t tmp = 0, tmp1 = 0;

  /* Check the parameters */
  assert_param(IS_OB_IWDG_SOURCE(OB_IWDG));
  assert_param(IS_OB_STOP_SOURCE(OB_STOP));
  assert_param(IS_OB_STDBY_SOURCE(OB_STDBY));

  /* Get the User Option byte register */
  tmp1 = (FLASH->OBR & 0x000F0000) >> 16;
    
  /* Calculate the user option byte to write */ 
  tmp = (uint32_t)(((uint32_t)~((uint32_t)((uint32_t)(OB_IWDG) | (uint32_t)(OB_STOP) | (uint32_t)(OB_STDBY) | tmp1))) << ((uint32_t)0x10));
  tmp |= ((uint32_t)(OB_IWDG) | ((uint32_t)OB_STOP) | (uint32_t)(OB_STDBY) | tmp1);
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {  
    /* Write the User Option Byte */              
    OB->USER = tmp; 
  }
  
  /* Wait for last operation to be completed */
    status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
       
  /* Return the Option Byte program Status */
  return status;
}

/**
  * @brief  Programs the FLASH brownout reset threshold level Option Byte.
  * @note   To correctly run this function, the FLASH_OB_Unlock() function
  *         must be called before.
  *         Call the FLASH_OB_Lock() to disable the flash control register access and the option bytes 
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  OB_BOR: Selects the brownout reset threshold level.
  *   This parameter can be one of the following values:
  *     @arg OB_BOR_OFF: BOR is disabled at power down, the reset is asserted when the VDD 
  *                      power supply reaches the PDR(Power Down Reset) threshold (1.5V)
  *     @arg OB_BOR_LEVEL1: BOR Reset threshold levels for 1.7V - 1.8V VDD power supply
  *     @arg OB_BOR_LEVEL2: BOR Reset threshold levels for 1.9V - 2.0V VDD power supply
  *     @arg OB_BOR_LEVEL3: BOR Reset threshold levels for 2.3V - 2.4V VDD power supply
  *     @arg OB_BOR_LEVEL4: BOR Reset threshold levels for 2.55V - 2.65V VDD power supply
  *     @arg OB_BOR_LEVEL5: BOR Reset threshold levels for 2.8V - 2.9V VDD power supply
  * @retval FLASH Status: The returned value can be: 
  * FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_OB_BORConfig(uint8_t OB_BOR)
{
  FLASH_Status status = FLASH_COMPLETE;
  uint32_t tmp = 0, tmp1 = 0;

  /* Check the parameters */
  assert_param(IS_OB_BOR_LEVEL(OB_BOR));

  /* Get the User Option byte register */
  tmp1 = (FLASH->OBR & 0x00F00000) >> 16;
     
  /* Calculate the option byte to write */
  tmp = (uint32_t)~(OB_BOR | tmp1)<<16;
  tmp |= (OB_BOR | tmp1);
    
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {  
    /* Write the BOR Option Byte */            
    OB->USER = tmp; 
  }
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
        
  /* Return the Option Byte program Status */
  return status;
}

/**
  * @brief  Configures to boot from Bank1 or Bank2.
  * @note   This function can be used only for STM32L1XX_HD density devices.
  *         To correctly run this function, the FLASH_OB_Unlock() function
  *         must be called before.
  *         Call the FLASH_OB_Lock() to disable the flash control register access and the option bytes 
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  OB_BOOT: select the FLASH Bank to boot from.
  *   This parameter can be one of the following values:
  *     @arg OB_BOOT_BANK2: At startup, if boot pins are set in boot from user Flash
  *        position and this parameter is selected the device will boot from Bank2 or Bank1,
  *        depending on the activation of the bank. The active banks are checked in
  *        the following order: Bank2, followed by Bank1.
  *        The active bank is recognized by the value programmed at the base address
  *        of the respective bank (corresponding to the initial stack pointer value
  *        in the interrupt vector table).
  *     @arg OB_BOOT_BANK1: At startup, if boot pins are set in boot from user Flash
  *        position and this parameter is selected the device will boot from Bank1(Default).
  *        For more information, please refer to AN2606 from www.st.com. 
  * @retval FLASH Status: The returned value can be: 
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_OB_BootConfig(uint8_t OB_BOOT)
{
  FLASH_Status status = FLASH_COMPLETE; 
  uint32_t tmp = 0, tmp1 = 0;

  /* Check the parameters */
  assert_param(IS_OB_BOOT_BANK(OB_BOOT));

  /* Get the User Option byte register */
  tmp1 = (FLASH->OBR & 0x007F0000) >> 16;
     
  /* Calculate the option byte to write */
  tmp = (uint32_t)~(OB_BOOT | tmp1)<<16;
  tmp |= (OB_BOOT | tmp1);
    
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {  
    /* Write the BOOT Option Byte */            
    OB->USER = tmp; 
  }
  
  /* Wait for last operation to be completed */
  status = FLASH_WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
       
  /* Return the Option Byte program Status */
  return status;
}

/**
  * @brief  Returns the FLASH User Option Bytes values.
  * @param  None
  * @retval The FLASH User Option Bytes.
  */
uint8_t FLASH_OB_GetUser(void)
{
  /* Return the User Option Byte */
  return (uint8_t)(FLASH->OBR >> 20);
}

/**
  * @brief  Returns the FLASH Write Protection Option Bytes value.
  * @param  None
  * @retval The FLASH Write Protection Option Bytes value.
  */
uint32_t FLASH_OB_GetWRP(void)
{
  /* Return the FLASH write protection Register value */
  return (uint32_t)(FLASH->WRPR);
}

/**
  * @brief  Returns the FLASH Write Protection Option Bytes value.
  * @note   This function can be used only for STM32L1XX_HD and STM32L1XX_MDP 
  *         density devices.
  * @param  None
  * @retval The FLASH Write Protection Option Bytes value.
  */
uint32_t FLASH_OB_GetWRP1(void)
{
  /* Return the FLASH write protection Register value */
  return (uint32_t)(FLASH->WRPR1);
}

/**
  * @brief  Returns the FLASH Write Protection Option Bytes value.
  * @note   This function can be used only for STM32L1XX_HD density devices.
  * @param  None
  * @retval The FLASH Write Protection Option Bytes value.
  */
uint32_t FLASH_OB_GetWRP2(void)
{
  /* Return the FLASH write protection Register value */
  return (uint32_t)(FLASH->WRPR2);
}

/**
  * @brief  Checks whether the FLASH Read out Protection Status is set or not.
  * @param  None
  * @retval FLASH ReadOut Protection Status(SET or RESET).
  */
FlagStatus FLASH_OB_GetRDP(void)
{
  FlagStatus readstatus = RESET;
  
  if ((uint8_t)(FLASH->OBR) != (uint8_t)OB_RDP_Level_0)
  {
    readstatus = SET;
  }
  else
  {
    readstatus = RESET;
  }
  return readstatus;
}

/**
  * @brief  Returns the FLASH BOR level.
  * @param  None
  * @retval The FLASH User Option Bytes.
  */
uint8_t FLASH_OB_GetBOR(void)
{
  /* Return the BOR level */
  return (uint8_t)((FLASH->OBR & (uint32_t)0x000F0000) >> 16);
}

/**
  * @}
  */

/** @defgroup FLASH_Group5 Interrupts and flags management functions
 *  @brief   Interrupts and flags management functions
 *
@verbatim   
  ==============================================================================
              ##### Interrupts and flags management functions #####
  ==============================================================================    

@endverbatim
  * @{
  */

/**
  * @brief  Enables or disables the specified FLASH interrupts.
  * @param  FLASH_IT: specifies the FLASH interrupt sources to be enabled or 
  *         disabled.
  *   This parameter can be any combination of the following values:
  *     @arg FLASH_IT_EOP: FLASH end of programming Interrupt
  *     @arg FLASH_IT_ERR: FLASH Error Interrupt
  * @retval None 
  */
void FLASH_ITConfig(uint32_t FLASH_IT, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FLASH_IT(FLASH_IT)); 
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if(NewState != DISABLE)
  {
    /* Enable the interrupt sources */
    FLASH->PECR |= FLASH_IT;
  }
  else
  {
    /* Disable the interrupt sources */
    FLASH->PECR &= ~(uint32_t)FLASH_IT;
  }
}

/**
  * @brief  Checks whether the specified FLASH flag is set or not.
  * @param  FLASH_FLAG: specifies the FLASH flag to check.
  *   This parameter can be one of the following values:
  *     @arg FLASH_FLAG_BSY: FLASH write/erase operations in progress flag 
  *     @arg FLASH_FLAG_EOP: FLASH End of Operation flag
  *     @arg FLASH_FLAG_READY: FLASH Ready flag after low power mode
  *     @arg FLASH_FLAG_ENDHV: FLASH End of high voltage flag
  *     @arg FLASH_FLAG_WRPERR: FLASH Write protected error flag 
  *     @arg FLASH_FLAG_PGAERR: FLASH Programming Alignment error flag
  *     @arg FLASH_FLAG_SIZERR: FLASH size error flag
  *     @arg FLASH_FLAG_OPTVERR: FLASH Option validity error flag
  *     @arg FLASH_FLAG_OPTVERRUSR: FLASH Option User validity error flag
  * @retval The new state of FLASH_FLAG (SET or RESET).
  */
FlagStatus FLASH_GetFlagStatus(uint32_t FLASH_FLAG)
{
  FlagStatus bitstatus = RESET;

  /* Check the parameters */
  assert_param(IS_FLASH_GET_FLAG(FLASH_FLAG));

  if((FLASH->SR & FLASH_FLAG) != (uint32_t)RESET)
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  /* Return the new state of FLASH_FLAG (SET or RESET) */
  return bitstatus; 
}

/**
  * @brief  Clears the FLASH's pending flags.
  * @param  FLASH_FLAG: specifies the FLASH flags to clear.
  *   This parameter can be any combination of the following values:
  *     @arg FLASH_FLAG_EOP: FLASH End of Operation flag
  *     @arg FLASH_FLAG_WRPERR: FLASH Write protected error flag 
  *     @arg FLASH_FLAG_PGAERR: FLASH Programming Alignment error flag 
  *     @arg FLASH_FLAG_SIZERR: FLASH size error flag    
  *     @arg FLASH_FLAG_OPTVERR: FLASH Option validity error flag
  *     @arg FLASH_FLAG_OPTVERRUSR: FLASH Option User validity error flag
  * @retval None
  */
void FLASH_ClearFlag(uint32_t FLASH_FLAG)
{
  /* Check the parameters */
  assert_param(IS_FLASH_CLEAR_FLAG(FLASH_FLAG));
  
  /* Clear the flags */
  FLASH->SR = FLASH_FLAG;
}

/**
  * @brief  Returns the FLASH Status.
  * @param  None
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_BUSY, FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP or FLASH_COMPLETE.
  */
FLASH_Status FLASH_GetStatus(void)
{
  FLASH_Status FLASHstatus = FLASH_COMPLETE;
  
  if((FLASH->SR & FLASH_FLAG_BSY) == FLASH_FLAG_BSY) 
  {
    FLASHstatus = FLASH_BUSY;
  }
  else 
  {  
    if((FLASH->SR & (uint32_t)FLASH_FLAG_WRPERR)!= (uint32_t)0x00)
    { 
      FLASHstatus = FLASH_ERROR_WRP;
    }
    else 
    {
      if((FLASH->SR & (uint32_t)0x1E00) != (uint32_t)0x00)
      {
        FLASHstatus = FLASH_ERROR_PROGRAM; 
      }
      else
      {
        FLASHstatus = FLASH_COMPLETE;
      }
    }
  }
  /* Return the FLASH Status */
  return FLASHstatus;
}


/**
  * @brief  Waits for a FLASH operation to complete or a TIMEOUT to occur.
  * @param  Timeout: FLASH programming Timeout.
  * @retval FLASH Status: The returned value can be: FLASH_BUSY, 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_WaitForLastOperation(uint32_t Timeout)
{ 
  __IO FLASH_Status status = FLASH_COMPLETE;
   
  /* Check for the FLASH Status */
  status = FLASH_GetStatus();
  
  /* Wait for a FLASH operation to complete or a TIMEOUT to occur */
  while((status == FLASH_BUSY) && (Timeout != 0x00))
  {
    status = FLASH_GetStatus();
    Timeout--;
  }
  
  if(Timeout == 0x00 )
  {
    status = FLASH_TIMEOUT;
  }
  /* Return the operation status */
  return status;
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

/**
  * @}
  */ 

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
