/**
  ******************************************************************************
  * @file    stm32h745i_discovery_mmc.c
  * @author  MCD Application Team
  * @brief   This file includes the EMMC driver mounted on STM32H745I-DISCOVERY
  *          board.
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

/* File Info : -----------------------------------------------------------------
                                   User NOTES
1. How To use this driver:
--------------------------
   - This driver is used to drive the EMMC mounted on STM32H745I-DISCOVERY
     board.
   - This driver does not need a specific component driver for the EMMC device
     to be included with.

2. Driver description:
---------------------
  + Initialization steps:
     o Initialize the external EMMC memory using the BSP_MMC_Init() function. This
       function includes the MSP layer hardware resources initialization and the
       SDIO interface configuration to interface with the external EMMC. It
       also includes the EMMC initialization sequence.
     o The function BSP_MMC_GetCardInfo() is used to get the MMC information
       which is stored in the structure "HAL_MMC_CardInfoTypedef".

  + Micro MMC card operations
     o The micro MMC card can be accessed with read/write block(s) operations once
       it is ready for access. The access can be performed whether using the polling
       mode by calling the functions BSP_MMC_ReadBlocks()/BSP_MMC_WriteBlocks(), or by DMA
       transfer using the functions BSP_MMC_ReadBlocks_DMA()/BSP_MMC_WriteBlocks_DMA()
     o The DMA transfer complete is used with interrupt mode. Once the MMC transfer
       is complete, the MMC interrupt is handled using the function BSP_MMC_IRQHandler(),
       the DMA Tx/Rx transfer complete are handled using the functions
       MMC_DMA_Tx_IRQHandler()/MMC_DMA_Rx_IRQHandler() that should be defined by user.
       The corresponding user callbacks are implemented by the user at application level.
     o The MMC erase block(s) is performed using the function BSP_MMC_Erase() with specifying
       the number of blocks to erase.
     o The MMC runtime status is returned when calling the function BSP_MMC_GetStatus().

------------------------------------------------------------------------------*/

/* Includes ------------------------------------------------------------------*/
#include "stm32h745i_discovery_mmc.h"

/** @addtogroup BSP
  * @{
  */

/** @addtogroup STM32H745I_DISCOVERY
  * @{
  */

/** @defgroup STM32H745I_DISCOVERY_MMC STM32H745I_DISCOVERY_MMC
  * @{
  */


/** @defgroup STM32H745I_DISCOVERY_MMC_Exported_Variables Exported Variables
  * @{
  */
MMC_HandleTypeDef uSdHandle;
/**
  * @}
  */


/** @defgroup STM32H745I_DISCOVERY_MMC_Exported_Functions  Exported Functions
  * @{
  */

/**
  * @brief  Initializes the MMC card device.
  * @retval MMC status
  */
uint8_t BSP_MMC_Init(void)
{
  uint8_t mmc_state = MMC_OK;

  /* uMMC device interface configuration */
  uSdHandle.Instance = SDMMC1;

  /* if CLKDIV = 0 then SDMMC Clock frequency = SDMMC Kernel Clock
     else SDMMC Clock frequency = SDMMC Kernel Clock / [2 * CLKDIV].
  */
  uSdHandle.Init.ClockDiv            = 2;
  uSdHandle.Init.ClockPowerSave      = SDMMC_CLOCK_POWER_SAVE_DISABLE;
  uSdHandle.Init.ClockEdge           = SDMMC_CLOCK_EDGE_RISING;
  uSdHandle.Init.HardwareFlowControl = SDMMC_HARDWARE_FLOW_CONTROL_DISABLE;
  uSdHandle.Init.BusWide             = SDMMC_BUS_WIDE_8B;

  /* Msp MMC initialization */
  BSP_MMC_MspInit(&uSdHandle, NULL);

  /* HAL MMC initialization */
  if(HAL_MMC_Init(&uSdHandle) != HAL_OK)
  {
    mmc_state = MMC_ERROR;
  }

  return  mmc_state;
}

/**
  * @brief  DeInitializes the MMC card device.
  * @retval MMC status
  */
uint8_t BSP_MMC_DeInit(void)
{
  uint8_t mmc_state = MMC_OK;

  uSdHandle.Instance = SDMMC1;

  /* HAL MMC deinitialization */
  if(HAL_MMC_DeInit(&uSdHandle) != HAL_OK)
  {
    mmc_state = MMC_ERROR;
  }

  /* Msp MMC deinitialization */
  uSdHandle.Instance = SDMMC1;
  BSP_MMC_MspDeInit(&uSdHandle, NULL);

  return  mmc_state;
}

/**
  * @brief  Reads block(s) from a specified address in an MMC card, in polling mode.
  * @param  pData: Pointer to the buffer that will contain the data to transmit
  * @param  ReadAddr: Address from where data is to be read
  * @param  NumOfBlocks: Number of MMC blocks to read
  * @param  Timeout: Timeout for read operation
  * @retval MMC status
  */
uint8_t BSP_MMC_ReadBlocks(uint32_t *pData, uint32_t ReadAddr, uint32_t NumOfBlocks, uint32_t Timeout)
{

  if( HAL_MMC_ReadBlocks(&uSdHandle, (uint8_t *)pData, ReadAddr, NumOfBlocks, Timeout) == HAL_OK)
  {
    return MMC_OK;
  }
  else
  {
    return MMC_ERROR;
  }

}

/**
  * @brief  Writes block(s) to a specified address in an MMC card, in polling mode.
  * @param  pData: Pointer to the buffer that will contain the data to transmit
  * @param  WriteAddr: Address from where data is to be written
  * @param  NumOfBlocks: Number of MMC blocks to write
  * @param  Timeout: Timeout for write operation
  * @retval MMC status
  */
uint8_t BSP_MMC_WriteBlocks(uint32_t *pData, uint32_t WriteAddr, uint32_t NumOfBlocks, uint32_t Timeout)
{

  if( HAL_MMC_WriteBlocks(&uSdHandle, (uint8_t *)pData, WriteAddr, NumOfBlocks, Timeout) == HAL_OK)
  {
    return MMC_OK;
  }
  else
  {
    return MMC_ERROR;
  }
}

/**
  * @brief  Reads block(s) from a specified address in an MMC card, in DMA mode.
  * @param  pData: Pointer to the buffer that will contain the data to transmit
  * @param  ReadAddr: Address from where data is to be read
  * @param  NumOfBlocks: Number of MMC blocks to read
  * @retval MMC status
  */
uint8_t BSP_MMC_ReadBlocks_DMA(uint32_t *pData, uint32_t ReadAddr, uint32_t NumOfBlocks)
{

  if( HAL_MMC_ReadBlocks_DMA(&uSdHandle, (uint8_t *)pData, ReadAddr, NumOfBlocks) == HAL_OK)
  {
    return MMC_OK;
  }
  else
  {
    return MMC_ERROR;
  }
}

/**
  * @brief  Writes block(s) to a specified address in an MMC card, in DMA mode.
  * @param  pData: Pointer to the buffer that will contain the data to transmit
  * @param  WriteAddr: Address from where data is to be written
  * @param  NumOfBlocks: Number of MMC blocks to write
  * @retval MMC status
  */
uint8_t BSP_MMC_WriteBlocks_DMA(uint32_t *pData, uint32_t WriteAddr, uint32_t NumOfBlocks)
{

  if( HAL_MMC_WriteBlocks_DMA(&uSdHandle, (uint8_t *)pData, WriteAddr, NumOfBlocks) == HAL_OK)
  {
    return MMC_OK;
  }
  else
  {
    return MMC_ERROR;
  }

}

/**
  * @brief  Erases the specified memory area of the given MMC card.
  * @param  StartAddr: Start byte address
  * @param  EndAddr: End byte address
  * @retval MMC status
  */
uint8_t BSP_MMC_Erase(uint32_t StartAddr, uint32_t EndAddr)
{

  if( HAL_MMC_Erase(&uSdHandle, StartAddr, EndAddr) == HAL_OK)
  {
    return MMC_OK;
  }
  else
  {
    return MMC_ERROR;
  }
}

/**
  * @brief  Initializes the MMC MSP.
  * @param  hmmc: MMC handle
  * @param  Params User parameters
  * @retval None
  */
__weak void BSP_MMC_MspInit(MMC_HandleTypeDef *hmmc, void *Params)
{
  /* __weak function can be modified by the application */

  GPIO_InitTypeDef gpio_init_structure;

  /* Enable SDIO clock */
  __HAL_RCC_SDMMC1_CLK_ENABLE();

  /* Enable GPIOs clock */
  __HAL_RCC_GPIOB_CLK_ENABLE();
  __HAL_RCC_GPIOC_CLK_ENABLE();
  __HAL_RCC_GPIOD_CLK_ENABLE();


  /* Common GPIO configuration */
  gpio_init_structure.Mode      = GPIO_MODE_AF_PP;
  gpio_init_structure.Pull      = GPIO_PULLUP;
  gpio_init_structure.Speed     = GPIO_SPEED_FREQ_VERY_HIGH;
  gpio_init_structure.Alternate = GPIO_AF12_SDIO1;

  /* SDMMC GPIO CLKIN PB8, D0 PC8, D1 PC9, D2 PC10, D3 PC11, CK PC12, CMD PD2 */
  /* GPIOC configuration */
  gpio_init_structure.Pin = GPIO_PIN_6 | GPIO_PIN_7 | GPIO_PIN_8 | GPIO_PIN_9 | GPIO_PIN_10 | GPIO_PIN_11 | GPIO_PIN_12;
  HAL_GPIO_Init(GPIOC, &gpio_init_structure);

  /* GPIOD configuration */
  gpio_init_structure.Pin = GPIO_PIN_2;
  HAL_GPIO_Init(GPIOD, &gpio_init_structure);

  gpio_init_structure.Pin = GPIO_PIN_8 | GPIO_PIN_9;
  HAL_GPIO_Init(GPIOB, &gpio_init_structure);


  /* NVIC configuration for SDIO interrupts */
  HAL_NVIC_SetPriority(SDMMC1_IRQn, 5, 0);
  HAL_NVIC_EnableIRQ(SDMMC1_IRQn);

}

/**
  * @brief  DeInitializes the MMC MSP.
  * @param  hmmc: MMC handle
  * @param  Params User parameters
  * @retval None
  */
__weak void BSP_MMC_MspDeInit(MMC_HandleTypeDef *hmmc, void *Params)
{
    /* Disable NVIC for SDIO interrupts */
    HAL_NVIC_DisableIRQ(SDMMC1_IRQn);

    /* DeInit GPIO pins can be done in the application
       (by surcharging this __weak function) */

    /* Disable SDMMC1 clock */
    __HAL_RCC_SDMMC1_CLK_DISABLE();

    /* GPIO pins clock and DMA clocks can be shut down in the application
       by surcharging this __weak function */
}

/**
  * @brief  Handles MMC card interrupt request.
  * @retval None
  */
void BSP_MMC_IRQHandler(void)
{
  HAL_MMC_IRQHandler(&uSdHandle);
}



/**
  * @brief  Gets the current MMC card data status.
  * @retval Data transfer state.
  *          This value can be one of the following values:
  *            @arg  MMC_TRANSFER_OK: No data transfer is acting
  *            @arg  MMC_TRANSFER_BUSY: Data transfer is acting
  *            @arg  MMC_TRANSFER_ERROR: Data transfer error
  */
uint8_t BSP_MMC_GetCardState(void)
{
  return((HAL_MMC_GetCardState(&uSdHandle) == HAL_MMC_CARD_TRANSFER ) ? MMC_TRANSFER_OK : MMC_TRANSFER_BUSY);
}


/**
  * @brief  Get MMC information about specific MMC card.
  * @param  CardInfo: Pointer to HAL_MMC_CardInfoTypedef structure
  * @retval None
  */
void BSP_MMC_GetCardInfo(BSP_MMC_CardInfo *CardInfo)
{
  HAL_MMC_GetCardInfo(&uSdHandle, CardInfo);
}

/**
  * @brief MMC Abort callbacks
  * @param hmmc: MMC handle
  * @retval None
  */
void HAL_MMC_AbortCallback(MMC_HandleTypeDef *hmmc)
{
  BSP_MMC_AbortCallback();
}


/**
  * @brief Tx Transfer completed callbacks
  * @param hmmc: MMC handle
  * @retval None
  */
void HAL_MMC_TxCpltCallback(MMC_HandleTypeDef *hmmc)
{
  BSP_MMC_WriteCpltCallback();
}

/**
  * @brief Rx Transfer completed callbacks
  * @param hmmc: MMC handle
  * @retval None
  */
void HAL_MMC_RxCpltCallback(MMC_HandleTypeDef *hmmc)
{
  BSP_MMC_ReadCpltCallback();
}

/**
  * @brief BSP MMC Abort callbacks
  * @retval None
  */
__weak void BSP_MMC_AbortCallback(void)
{

}

/**
  * @brief BSP Tx Transfer completed callbacks
  * @retval None
  */
__weak void BSP_MMC_WriteCpltCallback(void)
{

}

/**
  * @brief BSP Rx Transfer completed callbacks
  * @retval None
  */
__weak void BSP_MMC_ReadCpltCallback(void)
{

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
