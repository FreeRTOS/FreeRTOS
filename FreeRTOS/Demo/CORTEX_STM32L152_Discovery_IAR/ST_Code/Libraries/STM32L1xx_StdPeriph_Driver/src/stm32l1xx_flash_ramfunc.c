/**
  ******************************************************************************
  * @file    stm32l1xx_flash_ramfunc.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides all the Flash firmware functions which should be
  *          executed from the internal SRAM. This file should be placed in 
  *          internal SRAM. 
  *          Other FLASH memory functions that can be used from the FLASH are 
  *          defined in the "stm32l1xx_flash.c" file. 
@verbatim

    *** ARM Compiler ***
    --------------------
    [..] RAM functions are defined using the toolchain options. 
         Functions that are be executed in RAM should reside in a separate
         source module. Using the 'Options for File' dialog you can simply change
         the 'Code / Const' area of a module to a memory space in physical RAM.
         Available memory areas are declared in the 'Target' tab of the 
         Options for Target' dialog.

    *** ICCARM Compiler ***
    -----------------------
    [..] RAM functions are defined using a specific toolchain keyword "__ramfunc".

    *** GNU Compiler ***
    --------------------
    [..] RAM functions are defined using a specific toolchain attribute
         "__attribute__((section(".data")))".

    *** TASKING Compiler ***
    ------------------------
    [..] RAM functions are defined using a specific toolchain pragma. This 
         pragma is defined inside this file.

@endverbatim
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
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
static __RAM_FUNC GetStatus(void);
static __RAM_FUNC WaitForLastOperation(uint32_t Timeout);

/* Private functions ---------------------------------------------------------*/
 
/** @defgroup FLASH_Private_Functions
  * @{
  */ 

/** @addtogroup FLASH_Group1
 *
@verbatim  
@endverbatim
  * @{
  */  
#if defined (  __TASKING__  )
#pragma section_code_init on
#endif

/**
  * @brief  Enable or disable the power down mode during RUN mode.
  * @note  This function can be used only when the user code is running from Internal SRAM.
  * @param  NewState: new state of the power down mode during RUN mode.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
__RAM_FUNC FLASH_RUNPowerDownCmd(FunctionalState NewState)
{
  FLASH_Status status = FLASH_COMPLETE;
 
  if (NewState != DISABLE)
  {
     /* Unlock the RUN_PD bit */
     FLASH->PDKEYR = FLASH_PDKEY1;
     FLASH->PDKEYR = FLASH_PDKEY2;
     
     /* Set the RUN_PD bit in  FLASH_ACR register to put Flash in power down mode */
     FLASH->ACR |= (uint32_t)FLASH_ACR_RUN_PD;

     if((FLASH->ACR & FLASH_ACR_RUN_PD) != FLASH_ACR_RUN_PD)
     {
       status = FLASH_ERROR_PROGRAM;
     }
  }
  else
  {
    /* Clear the RUN_PD bit in  FLASH_ACR register to put Flash in idle  mode */
    FLASH->ACR &= (uint32_t)(~(uint32_t)FLASH_ACR_RUN_PD);
  }

  /* Return the Write Status */
  return status;  
}

/**
  * @}
  */

/** @addtogroup FLASH_Group2
 *
@verbatim  
@endverbatim
  * @{
  */

/**
  * @brief  Erases a specified 2 page in program memory in parallel.
  * @note   This function can be used only for STM32L1XX_HD density devices.
  *         To correctly run this function, the FLASH_Unlock() function
  *         must be called before.
  *         Call the FLASH_Lock() to disable the flash memory access 
  *        (recommended to protect the FLASH memory against possible unwanted operation).
  * @param  Page_Address1: The page address in program memory to be erased in 
  *         the first Bank (BANK1). This parameter should be between 0x08000000
  *         and 0x0802FF00.
  * @param  Page_Address2: The page address in program memory to be erased in 
  *         the second Bank (BANK2). This parameter should be between 0x08030000
  *         and 0x0805FF00.
  * @note   A Page is erased in the Program memory only if the address to load 
  *         is the start address of a page (multiple of 256 bytes).
  * @retval FLASH Status: The returned value can be: 
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
FLASH_Status FLASH_EraseParallelPage(uint32_t Page_Address1, uint32_t Page_Address2)
{
  FLASH_Status status = FLASH_COMPLETE;

  /* Wait for last operation to be completed */
  status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* If the previous operation is completed, proceed to erase the page */

    /* Set the PARALLBANK bit */
    FLASH->PECR |= FLASH_PECR_PARALLBANK;
    
    /* Set the ERASE bit */
    FLASH->PECR |= FLASH_PECR_ERASE;

    /* Set PROG bit */
    FLASH->PECR |= FLASH_PECR_PROG;
  
    /* Write 00000000h to the first word of the first program page to erase */
    *(__IO uint32_t *)Page_Address1 = 0x00000000;
    /* Write 00000000h to the first word of the second program page to erase */    
    *(__IO uint32_t *)Page_Address2 = 0x00000000;    
 
    /* Wait for last operation to be completed */
    status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);

    /* If the erase operation is completed, disable the ERASE, PROG and PARALLBANK bits */
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_PROG);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_ERASE);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_PARALLBANK);   
  }     
  /* Return the Erase Status */
  return status;
}

/**
  * @brief  Programs a half page in program memory.
  * @param  Address: specifies the address to be written.
  * @param  pBuffer: pointer to the buffer  containing the data to be  written to 
  *         the half page.
  * @note   To correctly run this function, the FLASH_Unlock() function
  *         must be called before.
  *         Call the FLASH_Lock() to disable the flash memory access  
  *         (recommended to protect the FLASH memory against possible unwanted operation)
  * @note   Half page write is possible only from SRAM.
  * @note   If there are more than 32 words to write, after 32 words another 
  *         Half Page programming operation starts and has to be finished.
  * @note   A half page is written to the program memory only if the first 
  *         address to load is the start address of a half page (multiple of 128 
  *         bytes) and the 31 remaining words to load are in the same half page.
  * @note   During the Program memory half page write all read operations are 
  *         forbidden (this includes DMA read operations and debugger read 
  *         operations such as breakpoints, periodic updates, etc.).
  * @note   If a PGAERR is set during a Program memory half page write, the 
  *         complete write operation is aborted. Software should then reset the 
  *         FPRG and PROG/DATA bits and restart the write operation from the 
  *         beginning.
  * @retval FLASH Status: The returned value can be:  
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT. 
  */
__RAM_FUNC FLASH_ProgramHalfPage(uint32_t Address, uint32_t* pBuffer)
{
  uint32_t count = 0; 
   
  FLASH_Status status = FLASH_COMPLETE;

  /* Set the DISMCYCINT[0] bit in the Auxillary Control Register (0xE000E008) 
     This bit prevents the interruption of multicycle instructions and therefore 
     will increase the interrupt latency. of Cortex-M3. */
  SCnSCB->ACTLR |= SCnSCB_ACTLR_DISMCYCINT_Msk;
  
  /* Wait for last operation to be completed */
  status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* if the previous operation is completed, proceed to program the new  
    half page */
    FLASH->PECR |= FLASH_PECR_FPRG;
    FLASH->PECR |= FLASH_PECR_PROG;
    
    /* Write one half page directly with 32 different words */
    while(count < 32)
    {
      *(__IO uint32_t*) (Address + (4 * count)) = *(pBuffer++);
      count ++;  
    }
    /* Wait for last operation to be completed */
    status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
 
    /* if the write operation is completed, disable the PROG and FPRG bits */
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_PROG);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_FPRG);
  }

  SCnSCB->ACTLR &= ~SCnSCB_ACTLR_DISMCYCINT_Msk;
    
  /* Return the Write Status */
  return status;
}

/**
  * @brief  Programs 2 half page in program memory in parallel.
  * @param  Address1: specifies the first address to be written in the first bank 
  *        (BANK1). This parameter should be between 0x08000000 and 0x0802FF80.
  * @param  pBuffer1: pointer to the buffer  containing the data to be  written 
  *         to the first half page in the first bank.
  * @param  Address2: specifies the second address to be written in the second bank
  *        (BANK2). This parameter should be between 0x08030000 and 0x0805FF80.
  * @param  pBuffer2: pointer to the buffer containing the data to be  written 
  *         to the second half page in the second bank.
  * @note   This function can be used only for STM32L1XX_HD density devices.
  * @note   To correctly run this function, the FLASH_Unlock() function
  *         must be called before.
  *         Call the FLASH_Lock() to disable the flash memory access  
  *         (recommended to protect the FLASH memory against possible unwanted operation).
  * @note   Half page write is possible only from SRAM.
  * @note   If there are more than 32 words to write, after 32 words another 
  *         Half Page programming operation starts and has to be finished.
  * @note   A half page is written to the program memory only if the first 
  *         address to load is the start address of a half page (multiple of 128 
  *         bytes) and the 31 remaining words to load are in the same half page.
  * @note   During the Program memory half page write all read operations are 
  *         forbidden (this includes DMA read operations and debugger read 
  *         operations such as breakpoints, periodic updates, etc.).
  * @note   If a PGAERR is set during a Program memory half page write, the 
  *         complete write operation is aborted. Software should then reset the 
  *         FPRG and PROG/DATA bits and restart the write operation from the 
  *         beginning.
  * @retval FLASH Status: The returned value can be:  
  *         FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */
__RAM_FUNC FLASH_ProgramParallelHalfPage(uint32_t Address1, uint32_t* pBuffer1, uint32_t Address2, uint32_t* pBuffer2)
{
  uint32_t count = 0; 
   
  FLASH_Status status = FLASH_COMPLETE;

  /* Set the DISMCYCINT[0] bit in the Auxillary Control Register (0xE000E008) 
     This bit prevents the interruption of multicycle instructions and therefore 
     will increase the interrupt latency. of Cortex-M3. */
  SCnSCB->ACTLR |= SCnSCB_ACTLR_DISMCYCINT_Msk;

  /* Wait for last operation to be completed */
  status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* If the previous operation is completed, proceed to program the new  
       half page */
    FLASH->PECR |= FLASH_PECR_PARALLBANK;
    FLASH->PECR |= FLASH_PECR_FPRG;
    FLASH->PECR |= FLASH_PECR_PROG;
    
    /* Write the first half page directly with 32 different words */
    while(count < 32)
    {
      *(__IO uint32_t*) (Address1 + (4 * count)) = *(pBuffer1++);
      count ++;  
    }
    count = 0;
    /* Write the second half page directly with 32 different words */
    while(count < 32)
    {
      *(__IO uint32_t*) (Address2 + (4 * count)) = *(pBuffer2++);
      count ++;  
    }
    /* Wait for last operation to be completed */
    status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
 
    /* if the write operation is completed, disable the PROG, FPRG and PARALLBANK bits */
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_PROG);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_FPRG);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_PARALLBANK);
  }

  SCnSCB->ACTLR &= ~SCnSCB_ACTLR_DISMCYCINT_Msk;
    
  /* Return the Write Status */
  return status;
}

/**
  * @}
  */

/** @addtogroup FLASH_Group3
 *
@verbatim  
@endverbatim
  * @{
  */

/**
  * @brief  Erase a double word in data memory.
  * @param  Address: specifies the address to be erased.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @note   Data memory double word erase is possible only from SRAM.
  * @note   A double word is erased to the data memory only if the first address 
  *         to load is the start address of a double word (multiple of 8 bytes).
  * @note   During the Data memory double word erase, all read operations are 
  *         forbidden (this includes DMA read operations and debugger read 
  *         operations such as breakpoints, periodic updates, etc.).
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT.
  */

__RAM_FUNC DATA_EEPROM_EraseDoubleWord(uint32_t Address)
{
  FLASH_Status status = FLASH_COMPLETE;
  
  /* Set the DISMCYCINT[0] bit in the Auxillary Control Register (0xE000E008) 
     This bit prevents the interruption of multicycle instructions and therefore 
     will increase the interrupt latency. of Cortex-M3. */
  SCnSCB->ACTLR |= SCnSCB_ACTLR_DISMCYCINT_Msk;
    
  /* Wait for last operation to be completed */
  status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* If the previous operation is completed, proceed to erase the next double word */
    /* Set the ERASE bit */
    FLASH->PECR |= FLASH_PECR_ERASE;

    /* Set DATA bit */
    FLASH->PECR |= FLASH_PECR_DATA;
   
    /* Write 00000000h to the 2 words to erase */
    *(__IO uint32_t *)Address = 0x00000000;
    Address += 4;
    *(__IO uint32_t *)Address = 0x00000000;
   
    /* Wait for last operation to be completed */
    status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
    
    /* If the erase operation is completed, disable the ERASE and DATA bits */
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_ERASE);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_DATA);
  }  
  
  SCnSCB->ACTLR &= ~SCnSCB_ACTLR_DISMCYCINT_Msk;
    
  /* Return the erase status */
  return status;
}

/**
  * @brief  Write a double word in data memory without erase.
  * @param  Address: specifies the address to be written.
  * @param  Data: specifies the data to be written.
  * @note   To correctly run this function, the DATA_EEPROM_Unlock() function
  *         must be called before.
  *         Call the DATA_EEPROM_Lock() to he data EEPROM access
  *         and Flash program erase control register access(recommended to protect 
  *         the DATA_EEPROM against possible unwanted operation).
  * @note   Data memory double word write is possible only from SRAM.
  * @note   A data memory double word is written to the data memory only if the 
  *         first address to load is the start address of a double word (multiple 
  *         of double word).
  * @note   During the Data memory double word write, all read operations are 
  *         forbidden (this includes DMA read operations and debugger read 
  *         operations such as breakpoints, periodic updates, etc.).
  * @retval FLASH Status: The returned value can be: 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or FLASH_TIMEOUT. 
  */ 
__RAM_FUNC DATA_EEPROM_ProgramDoubleWord(uint32_t Address, uint64_t Data)
{
  FLASH_Status status = FLASH_COMPLETE;

  /* Set the DISMCYCINT[0] bit in the Auxillary Control Register (0xE000E008) 
     This bit prevents the interruption of multicycle instructions and therefore 
     will increase the interrupt latency. of Cortex-M3. */
  SCnSCB->ACTLR |= SCnSCB_ACTLR_DISMCYCINT_Msk;
    
  /* Wait for last operation to be completed */
  status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
  
  if(status == FLASH_COMPLETE)
  {
    /* If the previous operation is completed, proceed to program the new data*/
    FLASH->PECR |= FLASH_PECR_FPRG;
    FLASH->PECR |= FLASH_PECR_DATA;
    
    /* Write the 2 words */  
     *(__IO uint32_t *)Address = (uint32_t) Data;
     Address += 4;
     *(__IO uint32_t *)Address = (uint32_t) (Data >> 32);
    
    /* Wait for last operation to be completed */
    status = WaitForLastOperation(FLASH_ER_PRG_TIMEOUT);
    
    /* If the write operation is completed, disable the FPRG and DATA bits */
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_FPRG);
    FLASH->PECR &= (uint32_t)(~FLASH_PECR_DATA);     
  }
  
  SCnSCB->ACTLR &= ~SCnSCB_ACTLR_DISMCYCINT_Msk;
    
  /* Return the Write Status */
  return status;
}

/**
  * @}
  */

/**
  * @brief  Returns the FLASH Status.
  * @param  None
  * @retval FLASH Status: The returned value can be: FLASH_BUSY, 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP or FLASH_COMPLETE
  */
static __RAM_FUNC GetStatus(void)
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
  * @param  Timeout: FLASH programming Timeout
  * @retval FLASH Status: The returned value can be: FLASH_BUSY, 
  *   FLASH_ERROR_PROGRAM, FLASH_ERROR_WRP, FLASH_COMPLETE or 
  *   FLASH_TIMEOUT.
  */
static __RAM_FUNC  WaitForLastOperation(uint32_t Timeout)
{ 
  __IO FLASH_Status status = FLASH_COMPLETE;
   
  /* Check for the FLASH Status */
  status = GetStatus();
  
  /* Wait for a FLASH operation to complete or a TIMEOUT to occur */
  while((status == FLASH_BUSY) && (Timeout != 0x00))
  {
    status = GetStatus();
    Timeout--;
  }
  
  if(Timeout == 0x00 )
  {
    status = FLASH_TIMEOUT;
  }
  /* Return the operation status */
  return status;
}

#if defined (  __TASKING__  )
#pragma section_code_init restore
#endif

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
