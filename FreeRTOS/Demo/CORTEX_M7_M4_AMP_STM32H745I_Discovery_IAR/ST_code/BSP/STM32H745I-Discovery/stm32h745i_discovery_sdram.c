/**
  ******************************************************************************
  * @file    stm32h745i_discovery_sdram.c
  * @author  MCD Application Team
  * @brief   This file includes the SDRAM driver for the MT48LC4M32B2B5-6A memory 
  *          device mounted on STM32H745I_DISCOVERY boards.
  ******************************************************************************
  @verbatim
  How To use this driver:
  -----------------------
   - This driver is used to drive the MT48LC4M32B2B5-6A SDRAM external memory mounted
     on STM32H745I_DISCOVERY board.
   - This driver does not need a specific component driver for the SDRAM device
     to be included with.

  Driver description:
  ------------------
  + Initialization steps:
     o Initialize the SDRAM external memory using the BSP_SDRAM_Init() function. This 
       function includes the MSP layer hardware resources initialization and the
       FMC controller configuration to interface with the external SDRAM memory.
     o It contains the SDRAM initialization sequence to program the SDRAM external 
       device using the function BSP_SDRAM_Initialization_sequence(). Note that this 
       sequence is standard for all SDRAM devices, but can include some differences
       from a device to another. If it is the case, the right sequence should be 
       implemented separately.
  
  + SDRAM read/write operations
     o SDRAM external memory can be accessed with read/write operations once it is
       initialized.
       Read/write operation can be performed with AHB access using the functions
       BSP_SDRAM_ReadData()/BSP_SDRAM_WriteData(), or by MDMA transfer using the functions
       BSP_SDRAM_ReadData_DMA()/BSP_SDRAM_WriteData_DMA().
     o The AHB access is performed with 32-bit width transaction, the MDMA transfer
       configuration is fixed at single (no burst) word transfer (see the 
       SDRAM_MspInit() static function).
     o User can implement his own functions for read/write access with his desired 
       configurations.
     o If interrupt mode is used for MDMA transfer, the function BSP_SDRAM_MDMA_IRQHandler()
       is called in IRQ handler file, to serve the generated interrupt once the MDMA 
       transfer is complete.
     o You can send a command to the SDRAM device in runtime using the function 
       BSP_SDRAM_Sendcmd(), and giving the desired command as parameter chosen between 
       the predefined commands of the "FMC_SDRAM_CommandTypeDef" structure. 
  @endverbatim
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; Copyright (c) 2019 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "stm32h745i_discovery_sdram.h"

/** @addtogroup BSP
  * @{
  */

/** @addtogroup STM32H745I_DISCOVERY
  * @{
  */ 
  
/** @defgroup  STM32H745I_DISCOVERY_SDRAM STM32H745I_DISCOVERY_SDRAM
  * @{
  */ 


/** @defgroup STM32H745I_DISCOVERY_SDRAM_Private_Variables Private Variables
  * @{
  */       
SDRAM_HandleTypeDef sdramHandle;
static FMC_SDRAM_TimingTypeDef Timing;
static FMC_SDRAM_CommandTypeDef Command;
/**
  * @}
  */ 

    
/** @defgroup STM32H745I_DISCOVERY_SDRAM_Exported_Functions Exported Functions
  * @{
  */ 

/**
  * @brief  Initializes the SDRAM device.
  * @retval SDRAM status
  */
uint8_t BSP_SDRAM_Init(void)
{ 
  static uint8_t sdramstatus = SDRAM_OK;
  /* SDRAM device configuration */
  sdramHandle.Instance = FMC_SDRAM_DEVICE;
    
  /* Timing configuration for 100Mhz as SDRAM clock frequency (System clock is up to 200Mhz) */
  Timing.LoadToActiveDelay    = 2;
  Timing.ExitSelfRefreshDelay = 7;
  Timing.SelfRefreshTime      = 4;
  Timing.RowCycleDelay        = 7;
  Timing.WriteRecoveryTime    = 2;
  Timing.RPDelay              = 2;
  Timing.RCDDelay             = 2;
  
  sdramHandle.Init.SDBank             = FMC_SDRAM_BANK2;
  sdramHandle.Init.ColumnBitsNumber   = FMC_SDRAM_COLUMN_BITS_NUM_8;
  sdramHandle.Init.RowBitsNumber      = FMC_SDRAM_ROW_BITS_NUM_12;
  sdramHandle.Init.MemoryDataWidth    = SDRAM_MEMORY_WIDTH;
  sdramHandle.Init.InternalBankNumber = FMC_SDRAM_INTERN_BANKS_NUM_4;
  sdramHandle.Init.CASLatency         = FMC_SDRAM_CAS_LATENCY_3;
  sdramHandle.Init.WriteProtection    = FMC_SDRAM_WRITE_PROTECTION_DISABLE;
  sdramHandle.Init.SDClockPeriod      = SDCLOCK_PERIOD;
  sdramHandle.Init.ReadBurst          = FMC_SDRAM_RBURST_ENABLE;
  sdramHandle.Init.ReadPipeDelay      = FMC_SDRAM_RPIPE_DELAY_0;
  
  /* SDRAM controller initialization */

  BSP_SDRAM_MspInit(&sdramHandle, NULL); /* __weak function can be rewritten by the application */

  if(HAL_SDRAM_Init(&sdramHandle, &Timing) != HAL_OK)
  {
    sdramstatus = SDRAM_ERROR;
  }
  else
  {
    /* SDRAM initialization sequence */
    BSP_SDRAM_Initialization_sequence(REFRESH_COUNT);
  }

  return sdramstatus;
}

/**
  * @brief  DeInitializes the SDRAM device.
  * @retval SDRAM status
  */
uint8_t BSP_SDRAM_DeInit(void)
{ 
  static uint8_t sdramstatus = SDRAM_OK;
  /* SDRAM device de-initialization */
  sdramHandle.Instance = FMC_SDRAM_DEVICE;

  if(HAL_SDRAM_DeInit(&sdramHandle) != HAL_OK)
  {
    sdramstatus = SDRAM_ERROR;
  }
  else
  {
    /* SDRAM controller de-initialization */
    BSP_SDRAM_MspDeInit(&sdramHandle, NULL);
  }
 
  return sdramstatus;
}

/**
  * @brief  Programs the SDRAM device.
  * @param  RefreshCount: SDRAM refresh counter value 
  * @retval None
  */
void BSP_SDRAM_Initialization_sequence(uint32_t RefreshCount)
{
  __IO uint32_t tmpmrd = 0;
  
  /* Step 1: Configure a clock configuration enable command */
  Command.CommandMode            = FMC_SDRAM_CMD_CLK_ENABLE;
  Command.CommandTarget          = FMC_SDRAM_CMD_TARGET_BANK2;
  Command.AutoRefreshNumber      = 1;
  Command.ModeRegisterDefinition = 0;

  /* Send the command */
  HAL_SDRAM_SendCommand(&sdramHandle, &Command, SDRAM_TIMEOUT);

  /* Step 2: Insert 100 us minimum delay */ 
  /* Inserted delay is equal to 1 ms due to systick time base unit (ms) */
  HAL_Delay(1);
    
  /* Step 3: Configure a PALL (precharge all) command */ 
  Command.CommandMode            = FMC_SDRAM_CMD_PALL;
  Command.CommandTarget          = FMC_SDRAM_CMD_TARGET_BANK2;
  Command.AutoRefreshNumber      = 1;
  Command.ModeRegisterDefinition = 0;

  /* Send the command */
  HAL_SDRAM_SendCommand(&sdramHandle, &Command, SDRAM_TIMEOUT);  
  
  /* Step 4: Configure an Auto Refresh command */ 
  Command.CommandMode            = FMC_SDRAM_CMD_AUTOREFRESH_MODE;
  Command.CommandTarget          = FMC_SDRAM_CMD_TARGET_BANK2;
  Command.AutoRefreshNumber      = 8;
  Command.ModeRegisterDefinition = 0;

  /* Send the command */
  HAL_SDRAM_SendCommand(&sdramHandle, &Command, SDRAM_TIMEOUT);
  
  /* Step 5: Program the external memory mode register */
  tmpmrd = (uint32_t)SDRAM_MODEREG_BURST_LENGTH_1          |\
                     SDRAM_MODEREG_BURST_TYPE_SEQUENTIAL   |\
                     SDRAM_MODEREG_CAS_LATENCY_3           |\
                     SDRAM_MODEREG_OPERATING_MODE_STANDARD |\
                     SDRAM_MODEREG_WRITEBURST_MODE_SINGLE;
  
  Command.CommandMode            = FMC_SDRAM_CMD_LOAD_MODE;
  Command.CommandTarget          = FMC_SDRAM_CMD_TARGET_BANK2;
  Command.AutoRefreshNumber      = 1;
  Command.ModeRegisterDefinition = tmpmrd;

  /* Send the command */
  HAL_SDRAM_SendCommand(&sdramHandle, &Command, SDRAM_TIMEOUT);
  
  /* Step 6: Set the refresh rate counter */
  /* Set the device refresh rate */
  HAL_SDRAM_ProgramRefreshRate(&sdramHandle, RefreshCount); 
}

/**
  * @brief  Reads an amount of data from the SDRAM memory in polling mode.
  * @param  uwStartAddress: Read start address
  * @param  pData: Pointer to data to be read  
  * @param  uwDataSize: Size of read data from the memory
  * @retval SDRAM status
  */
uint8_t BSP_SDRAM_ReadData(uint32_t uwStartAddress, uint32_t *pData, uint32_t uwDataSize)
{
  if(HAL_SDRAM_Read_32b(&sdramHandle, (uint32_t *)uwStartAddress, pData, uwDataSize) != HAL_OK)
  {
    return SDRAM_ERROR;
  }
  else
  {
    return SDRAM_OK;
  } 
}

/**
  * @brief  Reads an amount of data from the SDRAM memory in DMA mode.
  * @param  uwStartAddress: Read start address
  * @param  pData: Pointer to data to be read  
  * @param  uwDataSize: Size of read data from the memory
  * @retval SDRAM status
  */
uint8_t BSP_SDRAM_ReadData_DMA(uint32_t uwStartAddress, uint32_t *pData, uint32_t uwDataSize)
{
  if(HAL_SDRAM_Read_DMA(&sdramHandle, (uint32_t *)uwStartAddress, pData, uwDataSize) != HAL_OK)
  {
    return SDRAM_ERROR;
  }
  else
  {
    return SDRAM_OK;
  }     
}

/**
  * @brief  Writes an amount of data to the SDRAM memory in polling mode.
  * @param  uwStartAddress: Write start address
  * @param  pData: Pointer to data to be written  
  * @param  uwDataSize: Size of written data from the memory
  * @retval SDRAM status
  */
uint8_t BSP_SDRAM_WriteData(uint32_t uwStartAddress, uint32_t *pData, uint32_t uwDataSize) 
{
  if(HAL_SDRAM_Write_32b(&sdramHandle, (uint32_t *)uwStartAddress, pData, uwDataSize) != HAL_OK)
  {
    return SDRAM_ERROR;
  }
  else
  {
    return SDRAM_OK;
  }
}

/**
  * @brief  Writes an amount of data to the SDRAM memory in DMA mode.
  * @param  uwStartAddress: Write start address
  * @param  pData: Pointer to data to be written  
  * @param  uwDataSize: Size of written data from the memory
  * @retval SDRAM status
  */
uint8_t BSP_SDRAM_WriteData_DMA(uint32_t uwStartAddress, uint32_t *pData, uint32_t uwDataSize) 
{
  if(HAL_SDRAM_Write_DMA(&sdramHandle, (uint32_t *)uwStartAddress, pData, uwDataSize) != HAL_OK)
  {
    return SDRAM_ERROR;
  }
  else
  {
    return SDRAM_OK;
  } 
}

/**
  * @brief  Sends command to the SDRAM bank.
  * @param  SdramCmd: Pointer to SDRAM command structure 
  * @retval SDRAM status
  */  
uint8_t BSP_SDRAM_Sendcmd(FMC_SDRAM_CommandTypeDef *SdramCmd)
{
  if(HAL_SDRAM_SendCommand(&sdramHandle, SdramCmd, SDRAM_TIMEOUT) != HAL_OK)
  {
    return SDRAM_ERROR;
  }
  else
  {
    return SDRAM_OK;
  }
}

/**
  * @brief  Initializes SDRAM MSP.
  * @param  hsdram SDRAM handle
  * @param  Params User parameters
  * @retval None
  */
__weak void BSP_SDRAM_MspInit(SDRAM_HandleTypeDef  *hsdram, void *Params)
{  
  static MDMA_HandleTypeDef mdma_handle;
  GPIO_InitTypeDef gpio_init_structure;
  
  /* Enable FMC clock */
  __HAL_RCC_FMC_CLK_ENABLE();
  
  /* Enable chosen MDMAx clock */
  __MDMAx_CLK_ENABLE();

  /* Enable GPIOs clock */
  __HAL_RCC_GPIOD_CLK_ENABLE();
  __HAL_RCC_GPIOE_CLK_ENABLE();
  __HAL_RCC_GPIOF_CLK_ENABLE();
  __HAL_RCC_GPIOG_CLK_ENABLE();
  __HAL_RCC_GPIOH_CLK_ENABLE();
  
  /* Common GPIO configuration */
  gpio_init_structure.Mode      = GPIO_MODE_AF_PP;
  gpio_init_structure.Pull      = GPIO_PULLUP;
  gpio_init_structure.Speed     = GPIO_SPEED_FREQ_VERY_HIGH;
  gpio_init_structure.Alternate = GPIO_AF12_FMC;
  
  /* GPIOD configuration */
  gpio_init_structure.Pin   = GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_8| GPIO_PIN_9 | GPIO_PIN_10 |\
                              GPIO_PIN_14 | GPIO_PIN_15;
 
   
  HAL_GPIO_Init(GPIOD, &gpio_init_structure);

  /* GPIOE configuration */  
  gpio_init_structure.Pin   = GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_7| GPIO_PIN_8 | GPIO_PIN_9 |\
                              GPIO_PIN_10 | GPIO_PIN_11 | GPIO_PIN_12 | GPIO_PIN_13 | GPIO_PIN_14 |\
                              GPIO_PIN_15;
      
  HAL_GPIO_Init(GPIOE, &gpio_init_structure);
  
  /* GPIOF configuration */  
  gpio_init_structure.Pin   = GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_2| GPIO_PIN_3 | GPIO_PIN_4 |\
                              GPIO_PIN_5 | GPIO_PIN_11 | GPIO_PIN_12 | GPIO_PIN_13 | GPIO_PIN_14 |\
                              GPIO_PIN_15;
    
  HAL_GPIO_Init(GPIOF, &gpio_init_structure);
  
  /* GPIOG configuration */  
  gpio_init_structure.Pin   = GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_4 | GPIO_PIN_5 | GPIO_PIN_8 | GPIO_PIN_15;
  HAL_GPIO_Init(GPIOG, &gpio_init_structure);

  /* GPIOH configuration */  
  gpio_init_structure.Pin   = GPIO_PIN_5 | GPIO_PIN_6 | GPIO_PIN_7 ;
  HAL_GPIO_Init(GPIOH, &gpio_init_structure); 
  

  
  /* Configure common MDMA parameters */
  mdma_handle.Init.Request = MDMA_REQUEST_SW;
  mdma_handle.Init.TransferTriggerMode = MDMA_BLOCK_TRANSFER;
  mdma_handle.Init.Priority = MDMA_PRIORITY_HIGH;
  mdma_handle.Init.Endianness = MDMA_LITTLE_ENDIANNESS_PRESERVE;
  mdma_handle.Init.SourceInc = MDMA_SRC_INC_WORD;
  mdma_handle.Init.DestinationInc = MDMA_DEST_INC_WORD;
  mdma_handle.Init.SourceDataSize = MDMA_SRC_DATASIZE_WORD;
  mdma_handle.Init.DestDataSize = MDMA_DEST_DATASIZE_WORD;
  mdma_handle.Init.DataAlignment = MDMA_DATAALIGN_PACKENABLE;                            
  mdma_handle.Init.SourceBurst = MDMA_SOURCE_BURST_SINGLE;
  mdma_handle.Init.DestBurst = MDMA_DEST_BURST_SINGLE;
  mdma_handle.Init.BufferTransferLength = 128;
  mdma_handle.Init.SourceBlockAddressOffset = 0;
  mdma_handle.Init.DestBlockAddressOffset = 0; 
   
  
  mdma_handle.Instance = SDRAM_MDMAx_CHANNEL;
  
   /* Associate the DMA handle */
  __HAL_LINKDMA(hsdram, hmdma, mdma_handle);
  
  /* Deinitialize the stream for new transfer */
  HAL_MDMA_DeInit(&mdma_handle);
  
  /* Configure the DMA stream */
  HAL_MDMA_Init(&mdma_handle); 
  
  /* NVIC configuration for DMA transfer complete interrupt */
  HAL_NVIC_SetPriority(SDRAM_MDMAx_IRQn, 0x0F, 0);
  HAL_NVIC_EnableIRQ(SDRAM_MDMAx_IRQn);
}

/**
  * @brief  DeInitializes SDRAM MSP.
  * @param  hsdram SDRAM handle
  * @param  Params User parameters
  * @retval None
  */
__weak void BSP_SDRAM_MspDeInit(SDRAM_HandleTypeDef  *hsdram, void *Params)
{  
    static MDMA_HandleTypeDef mdma_handle;
  
    /* Disable NVIC configuration for DMA interrupt */
    HAL_NVIC_DisableIRQ(SDRAM_MDMAx_IRQn);

    /* Deinitialize the stream for new transfer */
    mdma_handle.Instance = SDRAM_MDMAx_CHANNEL;
    HAL_MDMA_DeInit(&mdma_handle);

    /* GPIO pins clock, FMC clock and MDMA clock can be shut down in the applications
       by surcharging this __weak function */ 
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
