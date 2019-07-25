/**
  ******************************************************************************
  * @file    stm32h745i_discovery_mmc.h
  * @author  MCD Application Team
  * @brief   This file contains the common defines and functions prototypes for
  *          the stm32h745i_discovery_mmc.c driver.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef STM32H745I_DISCOVERY_MMC_H
#define STM32H745I_DISCOVERY_MMC_H

#ifdef __cplusplus
 extern "C" {
#endif 

/* Includes ------------------------------------------------------------------*/
#include "stm32h7xx_hal.h"
#include "stm32h745i_discovery.h"

/** @addtogroup BSP
  * @{
  */ 

/** @addtogroup STM32H745I_DISCOVERY
  * @{
  */
    
/** @addtogroup STM32H745I_DISCOVERY_MMC
  * @{
  */    

/** @defgroup STM32H745I_DISCOVERY_MMC_Exported_Types Exported Types
  * @{
  */

/** 
  * @brief SD Card information structure 
  */
#define BSP_MMC_CardInfo HAL_MMC_CardInfoTypeDef
/**
  * @}
  */
  
/** @defgroup STM32H745I_DISCOVERY_MMC_Exported_Constants Exported Constants
  * @{
  */    
/** 
  * @brief  SD status structure definition  
  */     
#define MMC_OK                        ((uint8_t)0x00)
#define MMC_ERROR                     ((uint8_t)0x01)
#define MMC_ERROR_MMC_NOT_PRESENT     ((uint8_t)0x02)

/** 
  * @brief  MMC transfer state definition  
  */     
#define MMC_TRANSFER_OK                ((uint8_t)0x00)
#define MMC_TRANSFER_BUSY              ((uint8_t)0x01)


#define MMC_PRESENT               ((uint8_t)0x01)
#define MMC_NOT_PRESENT           ((uint8_t)0x00)

#define MMC_DATATIMEOUT           ((uint32_t)0xFFFFFFFFU)
    
/**
  * @}
  */
  
   
/** @addtogroup STM32H745I_DISCOVERY_MMC_Exported_Functions
  * @{
  */   
uint8_t BSP_MMC_Init(void);
uint8_t BSP_MMC_DeInit(void);
uint8_t BSP_MMC_ITConfig(void);

uint8_t BSP_MMC_ReadBlocks(uint32_t *pData, uint32_t ReadAddr, uint32_t NumOfBlocks, uint32_t Timeout);
uint8_t BSP_MMC_WriteBlocks(uint32_t *pData, uint32_t WriteAddr, uint32_t NumOfBlocks, uint32_t Timeout);
uint8_t BSP_MMC_ReadBlocks_DMA(uint32_t *pData, uint32_t ReadAddr, uint32_t NumOfBlocks);
uint8_t BSP_MMC_WriteBlocks_DMA(uint32_t *pData, uint32_t WriteAddr, uint32_t NumOfBlocks);
uint8_t BSP_MMC_Erase(uint32_t StartAddr, uint32_t EndAddr);
uint8_t BSP_MMC_GetCardState(void);
void    BSP_MMC_GetCardInfo(BSP_MMC_CardInfo *CardInfo);
uint8_t BSP_MMC_IsDetected(void);
void    BSP_MMC_IRQHandler(void);

/* These functions can be modified in case the current settings (e.g. DMA stream)
   need to be changed for specific application needs */
void    BSP_MMC_MspInit(MMC_HandleTypeDef *hmmc, void *Params);
void    BSP_MMC_MspDeInit(MMC_HandleTypeDef *hmmc, void *Params);
void    BSP_MMC_AbortCallback(void);
void    BSP_MMC_WriteCpltCallback(void);
void    BSP_MMC_ReadCpltCallback(void);


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

#ifdef __cplusplus
}
#endif

#endif /* __STM32H745I_DISCOVERY_MMC_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
