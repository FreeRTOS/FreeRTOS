/**
  ******************************************************************************
  * @file    stm32h7xx_hal_gpio_ex.h
  * @author  MCD Application Team
  * @brief   Header file of GPIO HAL Extension module.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2017 STMicroelectronics.
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
#ifndef STM32H7xx_HAL_GPIO_EX_H
#define STM32H7xx_HAL_GPIO_EX_H

#ifdef __cplusplus
extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32h7xx_hal_def.h"

/** @addtogroup STM32H7xx_HAL_Driver
  * @{
  */

/** @addtogroup GPIOEx GPIOEx
  * @{
  */

/* Exported types ------------------------------------------------------------*/

/* Exported constants --------------------------------------------------------*/
/** @defgroup GPIOEx_Exported_Constants GPIO Exported Constants
  * @{
  */

/** @defgroup GPIO_Alternate_function_selection GPIO Alternate Function Selection
  * @{
  */
/**
  * @brief   AF 0 selection
  */
#define GPIO_AF0_RTC_50Hz      ((uint8_t)0x00)  /* RTC_50Hz Alternate Function mapping                       */
#define GPIO_AF0_MCO           ((uint8_t)0x00)  /* MCO (MCO1 and MCO2) Alternate Function mapping            */
#define GPIO_AF0_SWJ           ((uint8_t)0x00)  /* SWJ (SWD and JTAG) Alternate Function mapping             */
#define GPIO_AF0_LCDBIAS       ((uint8_t)0x00)  /* LCDBIAS Alternate Function mapping                        */
#define GPIO_AF0_TRACE         ((uint8_t)0x00)  /* TRACE Alternate Function mapping                          */
#define GPIO_AF0_C1DSLEEP      ((uint8_t)0x00)  /* Cortex-M7 Deep Sleep Alternate Function mapping : available on STM32H7 Rev.B and above  */
#define GPIO_AF0_C1SLEEP       ((uint8_t)0x00)  /* Cortex-M7 Sleep Alternate Function mapping : available on STM32H7 Rev.B and above       */
#define GPIO_AF0_D1PWREN       ((uint8_t)0x00)  /* Domain 1 PWR enable Alternate Function mapping : available on STM32H7 Rev.B and above   */
#define GPIO_AF0_D2PWREN       ((uint8_t)0x00)  /* Domain 2 PWR enable Alternate Function mapping : available on STM32H7 Rev.B and above   */
#if defined(DUAL_CORE)
#define GPIO_AF0_C2DSLEEP      ((uint8_t)0x00)  /* Cortex-M4 Deep Sleep Alternate Function mapping : available on STM32H7 Rev.B and above  */
#define GPIO_AF0_C2SLEEP       ((uint8_t)0x00)  /* Cortex-M4 Sleep Alternate Function mapping : available on STM32H7 Rev.B and above       */
#endif /* DUAL_CORE */

/**
  * @brief   AF 1 selection
  */
#define GPIO_AF1_TIM1          ((uint8_t)0x01)  /* TIM1 Alternate Function mapping */
#define GPIO_AF1_TIM2          ((uint8_t)0x01)  /* TIM2 Alternate Function mapping */
#define GPIO_AF1_TIM16         ((uint8_t)0x01)  /* TIM16 Alternate Function mapping */
#define GPIO_AF1_TIM17         ((uint8_t)0x01)  /* TIM17 Alternate Function mapping */
#define GPIO_AF1_LPTIM1        ((uint8_t)0x01)  /* LPTIM1 Alternate Function mapping */
#define GPIO_AF1_HRTIM1        ((uint8_t)0x01)  /* HRTIM1 Alternate Function mapping */

/**
  * @brief   AF 2 selection
  */
#define GPIO_AF2_TIM3          ((uint8_t)0x02)  /* TIM3 Alternate Function mapping */
#define GPIO_AF2_TIM4          ((uint8_t)0x02)  /* TIM4 Alternate Function mapping */
#define GPIO_AF2_TIM5          ((uint8_t)0x02)  /* TIM5 Alternate Function mapping */
#define GPIO_AF2_TIM12         ((uint8_t)0x02)  /* TIM12 Alternate Function mapping */
#define GPIO_AF2_HRTIM1        ((uint8_t)0x02)  /* HRTIM2 Alternate Function mapping */
#define GPIO_AF2_SAI1          ((uint8_t)0x02)  /* SAI1 Alternate Function mapping */

/**
  * @brief   AF 3 selection
  */
#define GPIO_AF3_TIM8          ((uint8_t)0x03)  /* TIM8 Alternate Function mapping   */
#define GPIO_AF3_LPTIM2        ((uint8_t)0x03)  /* LPTIM2 Alternate Function mapping */
#define GPIO_AF3_DFSDM1        ((uint8_t)0x03)  /* DFSDM Alternate Function mapping  */
#define GPIO_AF3_HRTIM1        ((uint8_t)0x03)  /* HRTIM3 Alternate Function mapping */
#define GPIO_AF3_LPTIM3        ((uint8_t)0x03)  /* LPTIM3 Alternate Function mapping */
#define GPIO_AF3_LPTIM4        ((uint8_t)0x03)  /* LPTIM4 Alternate Function mapping */
#define GPIO_AF3_LPTIM5        ((uint8_t)0x03)  /* LPTIM5 Alternate Function mapping */
#define GPIO_AF3_LPUART        ((uint8_t)0x03)  /* LPUART Alternate Function mapping */

/**
  * @brief   AF 4 selection
  */
#define GPIO_AF4_I2C1          ((uint8_t)0x04)  /* I2C1 Alternate Function mapping   */
#define GPIO_AF4_I2C2          ((uint8_t)0x04)  /* I2C2 Alternate Function mapping   */
#define GPIO_AF4_I2C3          ((uint8_t)0x04)  /* I2C3 Alternate Function mapping   */
#define GPIO_AF4_I2C4          ((uint8_t)0x04)  /* I2C4 Alternate Function mapping   */
#define GPIO_AF4_TIM15         ((uint8_t)0x04)  /* TIM15 Alternate Function mapping  */
#define GPIO_AF4_CEC           ((uint8_t)0x04)  /* CEC Alternate Function mapping    */
#define GPIO_AF4_LPTIM2        ((uint8_t)0x04)  /* LPTIM2 Alternate Function mapping */
#define GPIO_AF4_USART1        ((uint8_t)0x04)  /* USART1 Alternate Function mapping */
#define GPIO_AF4_DFSDM1        ((uint8_t)0x04)  /* DFSDM  Alternate Function mapping   */

/**
  * @brief   AF 5 selection
  */
#define GPIO_AF5_SPI1          ((uint8_t)0x05)  /* SPI1 Alternate Function mapping   */
#define GPIO_AF5_SPI2          ((uint8_t)0x05)  /* SPI2 Alternate Function mapping   */
#define GPIO_AF5_SPI3          ((uint8_t)0x05)  /* SPI3 Alternate Function mapping   */
#define GPIO_AF5_SPI4          ((uint8_t)0x05)  /* SPI4 Alternate Function mapping   */
#define GPIO_AF5_SPI5          ((uint8_t)0x05)  /* SPI5 Alternate Function mapping   */
#define GPIO_AF5_SPI6          ((uint8_t)0x05)  /* SPI6 Alternate Function mapping   */
#define GPIO_AF5_CEC           ((uint8_t)0x05)  /* CEC  Alternate Function mapping   */


/**
  * @brief   AF 6 selection
  */
#define GPIO_AF6_SPI2          ((uint8_t)0x06)  /* SPI2 Alternate Function mapping  */
#define GPIO_AF6_SPI3          ((uint8_t)0x06)  /* SPI3 Alternate Function mapping  */
#define GPIO_AF6_SAI1          ((uint8_t)0x06)  /* SAI1 Alternate Function mapping  */
#define GPIO_AF6_SAI3          ((uint8_t)0x06)  /* SAI3 Alternate Function mapping  */
#define GPIO_AF6_I2C4          ((uint8_t)0x06)  /* I2C4 Alternate Function mapping  */
#define GPIO_AF6_DFSDM1        ((uint8_t)0x06)  /* DFSDM Alternate Function mapping */
#define GPIO_AF6_UART4         ((uint8_t)0x06)  /* UART4 Alternate Function mapping */

/**
  * @brief   AF 7 selection
  */
#define GPIO_AF7_SPI2          ((uint8_t)0x07)  /* SPI2 Alternate Function mapping   */
#define GPIO_AF7_SPI3          ((uint8_t)0x07)  /* SPI3 Alternate Function mapping   */
#define GPIO_AF7_SPI6          ((uint8_t)0x07)  /* SPI6 Alternate Function mapping   */
#define GPIO_AF7_USART1        ((uint8_t)0x07)  /* USART1 Alternate Function mapping */
#define GPIO_AF7_USART2        ((uint8_t)0x07)  /* USART2 Alternate Function mapping */
#define GPIO_AF7_USART3        ((uint8_t)0x07)  /* USART3 Alternate Function mapping */
#define GPIO_AF7_USART6        ((uint8_t)0x07)  /* USART6 Alternate Function mapping */
#define GPIO_AF7_UART7         ((uint8_t)0x07)  /* UART7 Alternate Function mapping  */
#define GPIO_AF7_DFSDM1        ((uint8_t)0x07)  /* DFSDM Alternate Function mapping  */
#define GPIO_AF7_SDMMC1        ((uint8_t)0x07)  /* SDMMC1 Alternate Function mapping */

/**
  * @brief   AF 8 selection
  */
#define GPIO_AF8_SPI6         ((uint8_t)0x08)  /* SPI6 Alternate Function mapping   */
#define GPIO_AF8_SAI2         ((uint8_t)0x08)  /* SAI2 Alternate Function mapping   */
#define GPIO_AF8_SAI4         ((uint8_t)0x08)  /* SAI4 Alternate Function mapping   */
#define GPIO_AF8_UART4        ((uint8_t)0x08)  /* UART4 Alternate Function mapping  */
#define GPIO_AF8_UART5        ((uint8_t)0x08)  /* UART5 Alternate Function mapping  */
#define GPIO_AF8_UART8        ((uint8_t)0x08)  /* UART8 Alternate Function mapping  */
#define GPIO_AF8_SPDIF        ((uint8_t)0x08)  /* SPDIF Alternate Function mapping  */
#define GPIO_AF8_LPUART       ((uint8_t)0x08)  /* LPUART Alternate Function mapping */
#define GPIO_AF8_SDMMC1       ((uint8_t)0x08)  /* SDMMC1 Alternate Function mapping */

/**
  * @brief   AF 9 selection
  */
#define GPIO_AF9_FDCAN1        ((uint8_t)0x09)  /* FDCAN1 Alternate Function mapping    */
#define GPIO_AF9_FDCAN2        ((uint8_t)0x09)  /* FDCAN2 Alternate Function mapping    */
#define GPIO_AF9_TIM13         ((uint8_t)0x09)  /* TIM13 Alternate Function mapping   */
#define GPIO_AF9_TIM14         ((uint8_t)0x09)  /* TIM14 Alternate Function mapping   */
#define GPIO_AF9_QUADSPI       ((uint8_t)0x09)  /* QUADSPI Alternate Function mapping   */
#define GPIO_AF9_SDMMC2        ((uint8_t)0x09)  /* SDMMC2 Alternate Function mapping   */
#define GPIO_AF9_LTDC          ((uint8_t)0x09)  /* LTDC Alternate Function mapping   */
#define GPIO_AF9_SPDIF         ((uint8_t)0x09)  /* SPDIF Alternate Function mapping   */
#define GPIO_AF9_FMC           ((uint8_t)0x09)  /* FMC Alternate Function mapping     */
#define GPIO_AF9_SAI4          ((uint8_t)0x09)  /* SAI4 Alternate Function mapping   */

/**
  * @brief   AF 10 selection
  */
#define GPIO_AF10_QUADSPI       ((uint8_t)0xA)  /* QUADSPI Alternate Function mapping */
#define GPIO_AF10_SAI2          ((uint8_t)0xA)  /* SAI2 Alternate Function mapping */
#define GPIO_AF10_SAI4          ((uint8_t)0xA)  /* SAI4 Alternate Function mapping */
#define GPIO_AF10_SDMMC2        ((uint8_t)0xA)  /* SDMMC2 Alternate Function mapping */
#define GPIO_AF10_OTG2_HS       ((uint8_t)0xA)  /* OTG2_HS Alternate Function mapping */
#define GPIO_AF10_OTG1_FS       ((uint8_t)0xA)  /* OTG1_FS Alternate Function mapping */
#define GPIO_AF10_COMP1         ((uint8_t)0xA)  /* COMP1 Alternate Function mapping */
#define GPIO_AF10_COMP2         ((uint8_t)0xA)  /* COMP2 Alternate Function mapping */
#define GPIO_AF10_LTDC          ((uint8_t)0xA)  /* LTDC Alternate Function mapping   */
#define GPIO_AF10_CRS_SYNC      ((uint8_t)0xA)  /* CRS Sync Alternate Function mapping : available on STM32H7 Rev.B and above  */


/**
  * @brief   AF 11 selection
  */
#define GPIO_AF11_SWP           ((uint8_t)0x0B)  /* SWP Alternate Function mapping */
#define GPIO_AF11_ETH           ((uint8_t)0x0B)  /* ETH Alternate Function mapping */
#define GPIO_AF11_MDIOS         ((uint8_t)0x0B)   /* MDIOS Alternate Function mapping   */
#define GPIO_AF11_OTG1_HS       ((uint8_t)0x0B)  /* OTG1_HS Alternate Function mapping */
#define GPIO_AF11_UART7         ((uint8_t)0x0B)  /* UART7 Alternate Function mapping */
#define GPIO_AF11_SDMMC2        ((uint8_t)0x0B)  /* SDMMC2 Alternate Function mapping */
#define GPIO_AF11_DFSDM1        ((uint8_t)0x0B)  /* DFSDM  Alternate Function mapping   */
#define GPIO_AF11_COMP1         ((uint8_t)0x0B)  /* COMP1 Alternate Function mapping */
#define GPIO_AF11_COMP2         ((uint8_t)0x0B)  /* COMP2 Alternate Function mapping */
#define GPIO_AF11_I2C4          ((uint8_t)0x0B)  /* I2C4 Alternate Function mapping  */

/**
  * @brief   AF 12 selection
  */
#define GPIO_AF12_FMC           ((uint8_t)0xC)  /* FMC Alternate Function mapping     */
#define GPIO_AF12_SDMMC1        ((uint8_t)0xC)  /* SDMMC1 Alternate Function mapping  */
#define GPIO_AF12_MDIOS         ((uint8_t)0xC)  /* MDIOS Alternate Function mapping   */
#define GPIO_AF12_OTG2_FS       ((uint8_t)0xC)  /* OTG2_FS Alternate Function mapping   */
#define GPIO_AF12_COMP1         ((uint8_t)0xC)  /* COMP1 Alternate Function mapping */
#define GPIO_AF12_COMP2         ((uint8_t)0xC)  /* COMP2 Alternate Function mapping */
#define GPIO_AF12_LTDC          ((uint8_t)0xC)  /* LTDC Alternate Function mapping   */

/**
  * @brief   AF 13 selection
  */
#define GPIO_AF13_DCMI          ((uint8_t)0x0D)   /* DCMI Alternate Function mapping */
#define GPIO_AF13_DSI           ((uint8_t)0x0D)   /* DSI Alternate Function mapping */
#define GPIO_AF13_COMP1         ((uint8_t)0x0D)   /* COMP1 Alternate Function mapping */
#define GPIO_AF13_COMP2         ((uint8_t)0x0D)   /* COMP2 Alternate Function mapping */
#define GPIO_AF13_LTDC          ((uint8_t)0x0D)   /* LTDC Alternate Function mapping   */

/**
  * @brief   AF 14 selection
  */
#define GPIO_AF14_LTDC         ((uint8_t)0x0E)   /* LTDC Alternate Function mapping   */
#define GPIO_AF14_UART5        ((uint8_t)0x0E)   /* UART5 Alternate Function mapping */

/**
  * @brief   AF 15 selection
  */
#define GPIO_AF15_EVENTOUT      ((uint8_t)0x0F)  /* EVENTOUT Alternate Function mapping */

#define IS_GPIO_AF(AF)   ((AF) <= (uint8_t)0x0F)



/**
  * @}
  */

/**
  * @}
  */

/* Exported macro ------------------------------------------------------------*/
/** @defgroup GPIOEx_Exported_Macros GPIO Exported Macros
  * @{
  */
/**
  * @}
  */

/* Exported functions --------------------------------------------------------*/
/** @defgroup GPIOEx_Exported_Functions GPIO Exported Functions
  * @{
  */
/**
  * @}
  */
/* Private types -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private constants ---------------------------------------------------------*/
/** @defgroup GPIOEx_Private_Constants GPIO Private Constants
  * @{
  */

/**
  * @brief   GPIO pin available on the platform
  */
/* Defines the available pins per GPIOs */
#define GPIOA_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOB_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOC_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOD_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOE_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOF_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOG_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOI_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOJ_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOH_PIN_AVAILABLE  GPIO_PIN_All
#define GPIOK_PIN_AVAILABLE  (GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_3 | GPIO_PIN_4 | \
                              GPIO_PIN_5 | GPIO_PIN_6 | GPIO_PIN_7)

/**
  * @}
  */

/* Private macros ------------------------------------------------------------*/
/** @defgroup GPIOEx_Private_Macros GPIO Private Macros
  * @{
  */
/** @defgroup GPIOEx_Get_Port_Index GPIO Get Port Index
  * @{
  */
#define GPIO_GET_INDEX(__GPIOx__)  (((__GPIOx__) == (GPIOA))? 0UL :\
                                    ((__GPIOx__) == (GPIOB))? 1UL :\
                                    ((__GPIOx__) == (GPIOC))? 2UL :\
                                    ((__GPIOx__) == (GPIOD))? 3UL :\
                                    ((__GPIOx__) == (GPIOE))? 4UL :\
                                    ((__GPIOx__) == (GPIOF))? 5UL :\
                                    ((__GPIOx__) == (GPIOG))? 6UL :\
                                    ((__GPIOx__) == (GPIOH))? 7UL :\
                                    ((__GPIOx__) == (GPIOI))? 8UL :\
                                    ((__GPIOx__) == (GPIOJ))? 9UL : 10UL)
/**
  * @}
  */

/** @defgroup GPIOEx_IS_Alternat_function_selection GPIO Check Alternate Function
  * @{
  */
/**
  * @}
  */

/**
  * @}
  */

/* Private functions ---------------------------------------------------------*/
/** @defgroup GPIOEx_Private_Functions GPIO Private Functions
  * @{
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

#endif /* STM32H7xx_HAL_GPIO_EX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
